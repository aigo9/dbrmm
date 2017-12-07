#!/usr/bin/env python
import os
import sys
import json
import fcntl
import re
import errno
import time
import traceback
import socket
import struct
import argparse
import pwd
import grp
import textwrap
import logging
import hashlib
import base64
import copy
import time
import signal
import threading

from functools import wraps
from collections import namedtuple
from collections import defaultdict
from subprocess import Popen, PIPE
from Queue import Empty as QueueEmpty
from multiprocessing import Process, Queue, cpu_count

ROOT = "root"
ROOT_UID = pwd.getpwnam(ROOT).pw_uid
ROOT_GID = pwd.getpwnam(ROOT).pw_gid
ROOT_GRP = grp.getgrgid(ROOT_GID).gr_name
# Subsystems
CGS_CPUSET = "cpuset"
CGS_CPU = "cpu"
CGS_CPUACCT = "cpuacct"
CGS_MEMORY = "memory"
# Parameters
CGP_CPU_SHARES = "cpu.shares"
CGP_CLONE_CHILDREN = "cgroup.clone_children"
CGP_MOVE_CHARGE_AT_IMMIGRATE = "memory.move_charge_at_immigrate"
CGP_TASKS = "tasks"
CGP_CGROUP_PROCS = "cgroup.procs"
CGP_MEMORY_USE_HIERARCHY = "memory.use_hierarchy"
# Attributes
CGA_PROMISED_CPUS = "promised_cpus"

DEFAULT_CPU_SHARES = 2
DEFAULT_CG_PARAMETERS = {
    CGS_CPU: {
        CGP_CPU_SHARES: DEFAULT_CPU_SHARES
    },
    CGS_MEMORY: {
        CGP_MOVE_CHARGE_AT_IMMIGRATE: 1
    }
}

# Sample interval in seconds
SAMPLE_INTERVAL = 5

# Time format string
TIME_FORMAT = "%Y-%m-%d %H:%M:%S"

# Subsystems we are interested in
CG_SUBSYSTEMS = (CGS_CPU, CGS_CPUACCT, CGS_MEMORY)

# Oracle DB path prefix
CG_PATH_PREFIX = "oracle.db"

# Total CPU shares for all registered Oracle database instances
# excluding ASM, APX and MGMTDB

TOTAL_CPU_SHARES = 1000

# Program return codes

R_SUCCESS = 0
R_WARNING = 1
R_ERROR = 2
R_STATUS = ("SUCCESS", "WARNING", "ERROR")

try: # Python 2.7
    from logging import NullHandler
except ImportError:
    class NullHandler(logging.Handler):
        def emit(self, record):
            pass

logger = logging.getLogger(__name__)
logger.addHandler(NullHandler())


def md5id(s):
    """md5(s)->base64->remove +/=

    Calculates md5 hash of string s and converts it ot printable identifier
    using base64 encoding and removing +/= characters from the result.
    """
    m = hashlib.md5()
    m.update(s)
    x = m.digest()
    x = base64.b64encode(x)
    return re.sub(r'[+/=]', '', x)

class TerminatedException(Exception):
    def __init__(self):
        pass
    def __repr__(self):
        return self.__class__.__name__ + "()"
    def __str__(self):
        return self.__class__.__name__

class ExecutionError(Exception):
    def __init__(self, msg, stdout='', stderr='', stdin='', rc=None):
        self.mgs = msg
        self.stdout = stdout
        self.stderr = stderr
        self.stdin = stdin
        self.rc = rc
    def _p(self, n, s):
        separator = "{0}: ---------- {1}".format(n, md5id(s))
        return [separator, s.split(os.linesep), separator]
    def __repr__(self):
        return \
            "ExecutionError(msg={0.msg!r}, stdout={0.stdout!r}, " \
            "stderr={0.stderr!r}, stdin={0.stdin!r}, rc={0.rc!r})".format(self)
    def __str__(self):
        rv = []
        rv.append("ExecutionError")
        if self.msg:
            rv += self._p("msg", self.msg)
        if self.stdout:
            rv += self._p("stdout", self.stdout)
        if self.stderr:
            rv += self._p("stderr", self.stderr)
        if self.stdin:
            rv += self._p("stdin", self.stdin)
        rv.append("return code: {0}".format(self.rc))
        return os.linesep.join(rv)

def execute(cmd, stdin=None, env=None, shell=False, cwd=None):
    p = Popen(cmd, stdout=PIPE, stderr=PIPE, stdin=PIPE, env=env, shell=shell, cwd=cwd)
    o, e = p.communicate(stdin)
    rc = p.poll()
    if rc != 0:
        raise ExecutionError(
            "Error executing {0!r}, rc = {1}".format(cmd, rc), o, e, stdin, rc)
    return o

def check_is_root():
    current_ruid = os.getuid()
    current_euid = os.geteuid()
    current_rgid = os.getgid()
    current_egid = os.getegid()
    if current_ruid != ROOT_UID or current_euid != ROOT_UID:
        raise RuntimeError("Operation not permitted: you have to be root to run this operation")
    if current_rgid != ROOT_GID or current_egid != ROOT_GID:
        os.setregid(ROOT_GID, ROOT_GID)

def cgclassify(path, pid):
    with open(os.path.join(path, CGP_CGROUP_PROCS), "w") as fd:
        try:
            fd.write(std(pid))
            fd.close()
        except IOError as e:
            if e.errno == errno.ESRCH: # No such process
                pass
            elif e.errno == errno.EINVAL: # Invalid argument
                # vktm and lms* processes return "Invalid argument" error
                # processes in RR class can't be moved to lower cpu cgroup
                # related to undocumented parameters
                # _highest_priority_processes and _high_priority_processes
                # use the following command to see process class and priority
                # ps -eo user,pid,tid,class,rtprio,ni,pri,psr,pcpu,stat,wchan:14,comm
                pass
            else:
                raise

def get_ora_cgpath(mount_dir, sid):
    return os.path.join(mount_dir, CG_PATH_PREFIX, sid)

CGInfo = namedtuple('CGInfo', ('hierarchy', 'num_cgroups', 'enabled'))

def get_cginfo_(fd):
    rv = {}
    lines = fd.readlines()
    for line in lines:
        if line.startswith('#'):
            continue
        fields = line.split()
        rv[fields[0]] = CGInfo(int(fields[1]), int(fields[2]), int(fields[3]))
    return rv

def get_cginfo():
    with open('/proc/cgroups') as fd:
        return get_cginfo_(fd)

def get_cgmounts_(fd):
    rv = {}
    lines = fd.readlines()
    for line in lines:
        fields = line.split()
        if fields[2] != 'cgroup':
            continue
        mount_options = fields[3].split(',')
        for subsystem in CG_SUBSYSTEMS:
            if subsystem in mount_options:
                rv[subsystem] = fields[1]
    return rv

def get_cgmounts():
    with open('/proc/mounts') as fd:
        return get_cgmounts_(fd)

def cg_path(mount_dir, cg_name):
    return os.path.join(mount_dir, CG_PATH_PREFIX, cg_name)

def cg_exists(mount_dir, cg_name):
    path = cg_path(mount_dir, cg_name)
    return os.path.exists(path)

def cg_get_parameter(path, pname):
    with open(os.path.join(path, pname)) as fd:
        return fd.read().strip()

def cg_set_parameter(path, pname, pvalue):
    with open(os.path.join(path, pname), 'w') as fd:
        fd.write(pvalue)

def cgcreate(config_file, cgmounts, cg_name, cpu_shares, promised_cpus):
    config_changed = False
    cgroup_changed = False
    with open(config_file, "r+") as fd:
        fcntl.flock(fd, fcntl.LOCK_EX)
        config = json.loads(fd.read())
        fd.seek(0)
        current_total_shares = 0
        for cgnm in config.keys():
            current_total_shares += int(config[cgnm][CGS_CPU][CGP_CPU_SHARES])
        total_shares_exceeded = ValueError(
            "Total number of shares exceeds the upper limit {0}".format(TOTAL_CPU_SHARES))
        if cg_name in config:
            logger.info("DB instance {0} is already registered in config file".format(cg_name))
            current_cpu_shares = int(config[cg_name][CGS_CPU][CGP_CPU_SHARES])
            current_promised_cpus = config[cg_name].get(CGA_PROMISED_CPUS, 0)
            if promised_cpus != current_promised_cpus:
                config_changed = True
                config[cg_name][CGA_PROMISED_CPUS] = promised_cpus
                logger.info("updated DB instance {0}: {1} = {2}".format(
                    cg_name,
                    CGA_PROMISED_CPUS,
                    promised_cpus))
            if cpu_shares != current_cpu_shares:
                if current_total_shares + cpu_shares - current_cpu_shares > TOTAL_CPU_SHARES:
                    raise total_shares_exceeded
                config_changed = True
                config[cg_name][CGS_CPU][CGP_CPU_SHARES] = cpu_shares
                logger.info("updated DB instance {0}: {1} = {2}".format(
                    cg_name,
                    CGP_CPU_SHARES,
                    cpu_shares))
        else:
            if current_total_shares + cpu_shares > TOTAL_CPU_SHARES:
                raise total_shares_exceeded
            params = dict(DEFAULT_CG_PARAMETERS)
            params[CGS_CPU][CGP_CPU_SHARES] = cpu_shares
            params[CGA_PROMISED_CPUS] = promised_cpus
            config[cg_name] = params
            config_changed = True
            logger.info("registered DB isntance {0} in config file".format(cg_name))
        for subsystem in CG_SUBSYSTEMS:
            mount_dir = cgmounts[subsystem]
            path = get_ora_cgpath(mount_dir, cg_name)
            cgroup_changed = \
                create_cgroup(path, config[cg_name].get(subsystem, {})) or cgroup_changed
        if config_changed:
            fd.truncate()
            fd.write(json.dumps(config, sort_keys=True, indent=4))
    return config_changed or cgroup_changed

def cgdelete(config_file, cgmounts, cg_name):
    """If there are procs running within the cgroup
    removes the cgroup from config file and set cpu.shares to default
    value. Otherwise deletes cgroup from both config file and the system"""
    config_changed = False
    cgroup_changed = False
    with open(config_file, "r+") as fd:
        fcntl.flock(fd, fcntl.LOCK_EX)
        config = json.loads(fd.read())
        fd.seek(0)
        if cg_name in config:
            del config[cg_name]
            config_changed = True
            logger.info("DB instance {0} deleted from config file".format(cg_name))
        for subsystem in CG_SUBSYSTEMS:
            mount_dir = cgmounts[subsystem]
            path = get_ora_cgpath(mount_dir, cg_name)
            if not os.path.exists(path):
                continue
            procs = cg_get_parameter(path, CGP_CGROUP_PROCS)
            if procs:
                if subsystem == CGS_CPU:
                    current_cpu_shares = cg_get_parameter(path, CGP_CPU_SHARES)
                if current_cpu_shares != DEFAULT_CPU_SHARES:
                    cg_set_parameter(path, CGP_CPU_SHARES, str(DEFAULT_CPU_SHARES))
                    cgroup_changed = True
                    logger.info("cgroup {0} is updated: {1} = {2}".format(
                        path, CGP_CPU_SHARES, DEFAULT_CPU_SHARES))
            else:
                os.rmdir(path)
                cgroup_changed = True
                logger.info("deleted cgroup {0}".format(path))
        if config_changed:
            fd.truncate()
            fd.write(json.dumps(config, sort_keys=True, indent=4))
    return config_changed or cgroup_changed

def create_cgroup(path, params=None):
    cgroup_changed = False
    if not os.path.exists(path):
        try:
            os.makedirs(path)
            cgroup_changed = True
            logger.info("created cgroup {0}".format(path))
        except OSError as e:
            if e.errno != errno.EEXIST: # File exist
                raise
    if params is not None:
        for p in params.keys():
            str_param = str(params[p])
            if cg_get_parameter(path, p) != str_param:
                cg_set_parameter(path, p, str_param)
                cgroup_changed = True
                logger.info("updated cgroup: {0} = {1}".format(p, str_param))
            else:
                logger.info("cgroup parameter is already set: {0} = {1}".format(p, str_param))
    return cgroup_changed

def get_proc_cgroup(pid):
    rv = {}
    try:
        with open(os.path.join('/proc', pid, 'cgroup')) as fd:
            for line in fd.read().strip().split(os.linesep):
                _, subsystem, path = line.split(':')
                rv[subsystem] = path
    except IOError as e:
        if e.errno != errno.ENOENT: # No such file or directory
            raise
    return rv

def classify_oracle_process(cgmounts, sid, pid):
    for subsystem in CG_SUBSYSTEMS:
        mount_dir = cgmounts[subsystem]
        path = get_ora_cgpath(mount_dir, sid)
        if not os.path.exists(path):
            create_cgroup(path, DEFAULT_CG_PARAMETERS.get(subsystem, {}))
        cgpath = get_ora_cgpath('/', sid)
        proc_cgroups = get_proc_cgroups(pid)
        if proc_cgroups.get(subsystem, '') != cgpath:
            cgclassify(path, pid)

def get_procs(path):
    return set(cg_get_parameter(path, CGP_CGROUP_PROCS).split(os.linesep))

# Regular expression to extract Oracle SID from command line; use m.group(3)
SIDRE = re.compile(r'^((ora|mdb)_[a-z0-9]{4}_|oracle)(?!\+ASM|\+APX)(-?\w+)')
# Regular expression to match process id
PIDRE = re.compile(r'^\d+$')

def get_oracle_processes():
    rv = defaultdict(lambda: set())
    root, dirs, _ = os.walk('/proc', topdown=True).next()
    for d in dirs:
        if PIDRE.match(d) is None:
            continue
        try:
            with open(os.path.join(root, d, 'cmdline')) as fd:
                cmdline = fd.read()
        except IOError as e:
            if e.errno == errno.ENOENT: # No such file or directory
                continue
            else:
                raise
        m = SIDRE.match(cmdline)
        if m is None:
            continue
        sid = m.group(3)
        rv[sid].add(d)
    return rv

def classify_oracle_processes(config_file, oracle_processes, cgmounts):
    with open(config_file, 'r') as fd:
        fcntl.flock(fd, fcntl.LOCK_EX)
        config = json.loads(fd.read())
        for sid in oracle_processes.keys():
            for subsystem in CG_SUBSYSTEMS:
                mount_dir = cgmounts[subsystem]
                path = get_ora_cgpath(kmount_dir, sid)
                params = dict(DEFAULT_CG_PARAMETERS.get(subsystem, {}))
                if sid in config and subsystem in config[sid]:
                    params.update(config[sid][subsystem])
                if not os.path.exists(path):
                    create_cgroup(path, params)
                procs = get_procs(path)
                processes = oracle_processes[sid]
                for pid in processes:
                    if pid not in procs:
                        cgclassify(path, pid)

def create_configured_cgroups(config_file, cgmounts):
    cgroup_changed = False
    with open(config_file, 'r') as fd:
        fcntl.flock(fd, fcntl.LOCK_EX)
        config = json.loads(fd.read())
        for sid in config:
            for subsystem in CG_SUBSYSTEMS:
                mount_dir = cgmounts[subsystem]
                path = get_ora_cgpath(mount_dir, sid)
                params = dict(DEFAULT_CG_PARAMETERS.get(subsystem, {}))
                if subsystem in config[sid]:
                    params.update(config[sid][subsystem])
                cgroup_changed = create_cgroup(path, params) or cgroup_changed
    return cgroup_changed

USER_HZ = os.sysconf(os.sysconf_names['SC_CLK_TCK'])

def _stats_delta(t0, t1, v0, v1, multiplier):
    if v1 is not None:
        return str(int(round((int(v1) - int(v0))/multiplier/(t1 - t0))))
    else:
        return None

def stats_delta_cpu_stat(t0, t1, v0, v1):
    return _stats_delta(t0, t1, v0, v1, USER_HZ/100.0)

def stats_delta_cpu_usage(t0, t1, v0, v1):
    return _stats_delta(t0, t1, v0, v1, 10000000.0)

def stats_delta(t0, t1, v0, v1):
    return _stats_delta(t0, t1, v0, v1, 1.0)

def stats_kb(t0, t1, v0, v1):
    return str(int(round(int(v1)/1024.0)))

class StatsSample(object):

    CPU_COUNT = cpu_count()
    CG_MOUNTS = get_cgmounts()

    def get_multi(strval):
        rv = {}
        for nv in [line.split() for line in strval.split(os.linesep)]:
            rv[nv[0]] = nv[1]
        return rv

    def get_count(strval):
        if strval:
            return str(len(strval.split(os.linesep)))
        else:
            return "0"

    STATS_DEF = {
        'cpuacct.stat': ('cpuacct', get_multi),
        'cpuacct.usage': ('cpuacct', None),
        'tasks': ('cpuacct', get_count),
        'cgroup.procs': ('cpuacct', get_count),
        'cpu.shares': ('cpu', None),
        'memory.stat': ('memory', get_multi),
        'memory.usage_in_bytes': ('memory', None),
        'memory.memsw.usage_in_bytes': ('memory', None),
        'memory.use_hierarchy': ('memory', None),
        'memory.move_change_at_immigrate': ('memory', None)
    }

    CALCULATED_STATS = {
        'syscpu': ('cpuacct.stat:system', stats_delta_cpu_stat),
        'usrcpu': ('cpuacct.stat:user', stats_delta_cpu_stat),
        'totcpu': ('cpuacct.usage', stats_delta_cpu_usage),
        'pgfault': ('memory.stat:pgfault', stats_delta),
        'pgmajfault': ('memory.stat:pgmajfault', stats_delta),
        'pgpgin': ('memory.stat:pgpgin', stats_delta),
        'pgpgout': ('memory.stat:pgpgout', stats_delta),
        'rssKB': ('memory.stat:rss', stats_kb),
        'rss_hugeKB': ('memory.stat:rss_huge', stats_kb),
        'total_pgfault': ('memory.stat:total_pgfault', stats_delta),
        'total_pgmajfault': ('memory.stat:total_pgmajfault', stats_delta),
        'total_pgpgin': ('memory.stat:total_pgpgin', stats_delta),
        'total_pgpgout': ('memory.stat:total_pgpgout', stats_delta),
        'total_rssKB': ('memory.stat:total_rss', stats_kb),
        'total_rss_hugeKB': ('memory.stat:total_rss_huge', stats_kb),
        'memKB': ('memory.usage_in_bytes', stats_kb),
        'memswKB': ('memory.memsw.usage_in_bytes', stats_kb)
    }

    STATS = (
        # calculated
        'syscpu',
        'usrcpu',
        'totcpu',
        'pgfault',
        'pgmajfault',
        'pgpgin',
        'pgpgout',
        'rssKB',
        'rss_hugeKB',
        'total_pgfault',
        'total_pgmajfault',
        'total_pgpgin',
        'total_pgpgout',
        'total_rssKB',
        'total_rss_hugeKB',
        'memKB',
        'memswKB',
        # raw
        'cpu.shares',
        'cpuacct.stat:system',
        'cpuacct.stat:user',
        'cpuacct.usage',
        'memory.memsw.usage_in_bytes',
        'memory.stat:pgfault',
        'memory.stat:pgmajfault',
        'memory.stat:pgpgin',
        'memory.stat:pgpgout',
        'memory.stat:rss',
        'memory.stat:rss_huge',
        'memory.usage_in_bytes',
        'memory.use_hierarchy',
        'memory.move_charge_at_immigrate',
        'tasks',
        'cgroup.procs'
    )

    MEMINFO_FIELDS = (
        "memtotal",
        "memfree",
        "buffers",
        "cached",
        "swaptotal",
        "swapfree",
        "memavailable",
        "hugepages_total",
        "hugepages_free",
        "hugepagesize"
    )

    def __init__(self, config):
        self.sample_start_time = time.time()
        self.config = config
        self.sample_time = round(self.sample_start_time)
        self.stats_sample = defaultdict(lambda: dict())
        for subsystem in CG_SUBSYSTEMS:
            mount_dir = self.CG_MOUNTS[subsystem]
            for root, dirs, files in os.walk(mount_dir, topdown=True):
                for file in files:
                    if file in self.STATS_DEF:
                        sd = self.STATS_DEF[file]
                        if subsystem != sd[0]:
                            continue
                        val = cg_get_parameter(root, file)
                        if sd[1] is not None:
                            val = sd[1](val)
                        cg_name = root[len(mount_dir):]
                        if cg_name == '':
                            cg_name = '/'
                        cg_stats = self.stats_sample[cg_name]
                        if isinstance(val, dict):
                            for k, v in val.items():
                                cg_stats[file + ':' + k] = v
                        else:
                            cg_stats[file] = val
        self.read_meminfo()
        self.sample_end_time = time.time()

    def _calculate_stats(self, prior):
        stats_sample = defaultdict(lambda: dict())
        this_sample_time = (self.sample_start_time + self.sample_end_time)/2
        for cg, cg_stats in self.stats_sample.items():
            calculated_stats = stats_sample[cg]
            for k, item in self.CALCULATED_STATS.items():
                if item[0] in cg_stats:
                    if prior and cg in prior.stats_sample:
                        prior_sample_time = (prior.sample_start_time + prior.sample_end_time)/2
                        prior_stats = prior.stats_sample[cg]
                        if item[0] in prior_stats:
                            calculated_stats[k] = item[1](
                                prior_sample_time,
                                this_sample_time,
                                prior_stats[item[0]],
                                cg_stats[item[0]]
                            )
                    else:
                        calculated_stats[k] = item[1](
                            None,
                            this_sample_time,
                            None,
                            cg_stats[item[0]]
                        )
                else:
                    calculated_stats[k] = ''
        return stats_sample

    def dumps(self, prior):
        calculated_stats = self._calculate_stats(prior)
        lines = []
        total_cpu_shares = 0
        total_promised_cpus = 0
        oracle_cg_prefix = "/" + CG_PATH_PREFIX + "/"
        for cg in self.stats_sample.keys():
            if cg.startswith(oracle_cg_prefix):
                total_cpu_shares += int(self.stats_sample[cg][CGP_CPU_SHARES])
                instance_name = os.path.basename(cg)
                if instance_name in self.config:
                    total_promised_cpus += self.config[instance_name][CGA_PROMISED_CPUS]
        for cg in sorted(self.stats_sample.keys()):
            stats = self.stats_sample[cg].copy()
            stats.update(calculated_stats[cg])
            ts = time.strftime(TIME_FORMAT, time.gmtime(self.sample_time))
            prior_ts = time.strftime(TIME_FORMAT, time.gmtime(prior.sample_time))
            row = [ts, cg] + [stats.get(x, '') for x in self.STATS] + [str(self.CPU_COUNT), prior_ts]
            if cg.startswith(oracle_cg_prefix):
                instance_name = os.path.basename(cg)
                if instance_name in self.config:
                    row += [str(self.config[instance_name][CGA_PROMISED_CPUS])]
                else:
                    row += [""]
                row += [str(total_cpu_shares), str(total_promised_cpus)]
            else:
                row += ["", "", ""]
            for f in self.MEMINFO_FIELDS:
                if cg == "/" and f in self.meminfo:
                    row.append(self.meminfo[f])
                else:
                    row.append("")
            lines.append(','.join(row))
        return os.linesep.join(lines) + os.linesep

    def read_meminfo_(self, fd):
        rv = {}
        mem_stats = set(self.MEMINFO_FIELDS)
        lines = fd.read().strip().split(os.linesep)
        for line in lines:
            fields = line.split()
            f = fields[0].strip(':').lower()
            if f not in mem_stats:
                continue
            rv[f] = fields[1]
        return rv

    def read_meminfo(self):
        with open('/proc/meminfo') as fd:
            self.meminfo = self.read_meminfo_(fd)

    @classmethod
    def dumph(cls):
        row = ['timestamp', 'cgroup'] + list(cls.STATS) + \
        ['cpu_count', 'prior_timestamp', 'promised_cpus'] + \
        ['total_cpu_shares', 'total_promised_cpus'] + \
        list(cls.MEMINFO_FIELDS)
        return ','.join(row) + os.linesep

class StatsWriter(object):
    def __init__(self, output_dir):
        self.hostname = get_hostname()
        self.output_dir = output_dir
        self.fd = None
        self.ymdh = None

    def write(self, ts, str):
        FNAME_FORMAT = "{0}-{1:d}{2:02d}{3:02d}{4:02d}.dat" # hostname-YYYYMMDDHH.dat
        ymdh = time.gmtime(ts)[:4]
        if self.fd is None or ymdh != self.ymdh:
            self.ymdh = ymdh
            if self.fd:
                fd = self.fd
                self.fd = None
                fd.close()
            fname = FNAME_FORMAT.format(self.hostname, *ymdh)
            existing_file = os.path.exists(fname)
            fd = open(os.path.join(self.output_dir, fname), 'a')
            if not existing_file:
                fd.write(StatsSample.dumph())
                fd.flush()
            self.fd = fd
        self.fd.write(str)
        self.fd.flush()

def startDaemon():
    cgmounts = get_cgmounts()
    port = os.getpid()
    # #define NETLINK_CONNECTION 11
    # file netlink.h
    # netlink family, 3rd parameter below
    sock = socket.socket(socket.AF_NETLINK, socket.SOCK_DGRAM, 11)
    sock.bind((port, 1))
    # I - unsigned int; H - unsigned short
    data = struct.pack("=IHHIIIIIIHHI", 40, 3, 0, 0, port, 1, 1, 0, 0, 4, 0, 1)
    s = sock.send(data)
    while True:
        try:
            data, ndata = sock.recvfrom(1024)
        except:
            # TODO add exception handling
            print traceback.format_exc()
            continue
        data = data[36:]
        # L - unsiged long; Q - unsigned long long; I - unsigned int
        op, cpu, ts, pid = struct.unpack("=LLQI", data[:20])
        print "%s: CPU=%d, PID=%d, TS=%d" % (op, cpu, pid, ts)
        if (op == 2):
            try:
                with open(os.path.join('/proc', str(pid), 'cmdline')) as fd:
                    cmdline = fd.readline()
                    print "CMDLINE=%s" % cmdline
                    m = re.match(SIDRE, cmdline)
                    if m:
                        sid = m.group(3)
                        classify_oracle_process(cgmounts, sid, pid)
            except:
                # TODO add exception handling
                print traceback.format_exc()
                continue

def sleep_till_next_sample(sample_time, interval):
    tt = int(sample_time) / interval * interval
    t2 = time.time()
    sleep_time = tt + interval - t2
    if sleep_time < 0:
        sleep_time = (int(round(t2)) / interval * interval + interval) - t2
    time.sleep(sleep_time)

def validate_interval(interval):
    if not isinstance(interval, int):
        raise ValueError("Interval should be an integer")
    if interval <= 0:
        raise ValueError("Interval should be > 0")
    if (interval < 60 and 60 % interval != 0) or (interval >= 60 and interval % 60 != 0):
        raise ValueError(
            "Interval should be either multiple of minute or exact fraction of minute")

def add_logging_options(parser, enable_console_logging=True):
    default_base_dir = os.path.dirname(os.path.realpath(__file__))
    parser.add_argument(
        "--base_dir",
        default=default_base_dir,
        help="base directory, default: %(default)s",
        metavar="DIR")
    log_levels = ["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"]
    parser.add_argument(
        "--log_level", 
        default="DEBUG",
        help="log level, choices are {0}, default %(default)s".format(log_levels),
        metavar="LEVEL",
        choices=set(log_levels))
    parser.add_argument(
        "--console_logging",
        default=enable_console_logging,
        help="enable console logging, default %(default)s",
        type=str2bool, nargs='?')

def str2bool(v):
    v = v.lower()
    if v in ('yes', 'true', 't', 'y', '1'):
        return True
    elif v in ('no', 'false', 'f', 'n', '0'):
        return False
    else:
        raise argparse.ArgumentTypeError("Boolean value expected")

def add_prog(parser):
    parser.set_defaults(prog=parser.prog.split(" ")[-1])

def mount_cg(path, subsystem):
    if not os.path.exists(path):
        raise RunTimeError("path {0} does not exist".format(path))
    if not os.path.isdir(path):
        raise RunTimeError("{0} is not a directory".format(path))
    cgroup_dir = os.path.join(path, subsystem)
    if not os.path.exists(cgroup_dir):
        makedirs(cgroup_dir)
    cmd = [
        "mount",
        "-t",
        "cgroup",
        "-o",
        subsystem,
        subsystem,
        cgroup_dir
    ]
    execute(cmd)
    logger.debug("mounted cgroup {0} on {1}".format(subsystem, cgroup_dir))

def mount_cgroup_root(path):
    cmd = [
        "mount",
        "-t",
        "tmpfs",
        "cgroup_root",
        path
    ]
    execute(cmd)
    logger.debug("mounted cgroup_root tmpfs on {0}".format(path))

def makedirs(dir_name):
    os.makedirs(dir_name)
    logger.debug("created directory {0}".format(dir_name))

def enable_memory_use_hierarchy(cgmounts):
    if int(get_muh(cgmounts)):
        logger.info("memory.use_hierarchy is already enabled")
        return (R_SUCCESS, False)
    try:
        set_muh(cgmounts)
        logger.info("enabled memory.use_hierarchy")
        return (R_SUCCESS, True)
    except Exception as e:
        # TODO add exception handling
        logger.warning("failed to enable to memory.use_hierarchy")
        logger.warning(str(e))
        return (R_WARNING, False)

def check_cpu_mount(cgmounts):
    rs = R_SUCCESS
    cpu_mount = cgmounts[CGS_CPU]
    same_mount_subsystems = []
    for k, v in cgmounts.items():
        if k == CGS_CPU:
            continue
        if v == cpu_mount:
            same_mount_subsystems.append(k)
    if same_mount_subsystems:
        logger.warning(
            "The following subsystems are mounted " \
            "to the same hierarchy as {0}: {1}".format(
                CGS_CPU,
                same_mount_subsystems))
        rs = R_WARNING
    if rs == R_SUCCESS:
        logger.info("cpu subsystem is mounted to separate hierarchy")
    return (rs, False)

def get_muh(cgmounts):
    return cg_get_parameter(cgmounts[CGS_MEMORY], CGP_MEMORY_USE_HIERARCHY)

def set_muh(cgmounts):
    cg_set_parameter(cgmounts[CGS_MEMORY], CGP_MEMORY_USE_HIERARCHY, "1")

def f_check(args):
    cginfo = get_cginfo()
    rs = R_SUCCESS
    for ss in CG_SUBSYSTEMS:
        if ss not in cginfo:
            logger.error("Can not get info on {0} subsystem".format(ss))
            rs = R_ERROR
            continue
        info = cginfo[ss]
        if not info.enabled:
            logger.error("Subsystem {0} is not enabled".format(ss))
            rs = R_ERROR
            continue
        if not info.hierarchy:
            logger.error("Subsystem {0} is not mounted".format(ss))
            rs = R_ERROR
            continue
        logger.info("Subsystem {0} is enabled and mounted".format(ss))
    if rs == R_ERROR:
        return (rs, False)
    cgmounts = get_cgmounts()
    s, _ = check_cpu_mount(cgmounts)
    if s > rs: rs = s
    if int(get_muh(cgmounts)):
        logger.info("{0} is enabled".format(CGP_MEMORY_USE_HIERARCHY))
    else:
        logger.warning("{0} is not enabled".format(CGP_MEMORY_USE_HIERARCHY))
        if rs < R_WARNING: rs = R_WARNING
    return (rs, False)

def f_prepare(args):
    changed = False
    cginfo = get_cginfo()
    rs = R_SUCCESS
    for ss in CG_SUBSYSTEMS:
        if ss not in cginfo:
            logger.error("Can not get info on {0} subsystem".format(ss))
            rs = R_ERROR
            continue
        info = cginfo[ss]
        if not info.enabled:
            logger.error("Subsystem {0} is not enabled".format(ss))
            rs = R_ERROR
            continue
        logger.info("Subsystem {0} is enabled".format(ss))
    if rs == R_ERROR:
        return (rs, False)
    config_file = get_config_file(args)
    logger.info("Using configuration file {0}".format(config_file))
    if os.path.exists(config_file):
        s, c = check_config_file(config_file)
        if s > rs: rs = s
    else:
        with open(config_file, "w") as fd:
            fd.write("{}")
        logger.info("Created new empty configuration file {0}".format(config_file))
        changed = True
    cgmounts = get_cgmounts()
    if len(cgmounts) == 0: # None of the group hierarchies are mounted
        default_cgroup_root = "/sys/fs/cgroup"
        if os.path.exists(os.path.dirname(default_cgroup_root)):
            if not os.path.exists(default_cgroup_root):
                makedirs(default_cgroup_root)
                changed = True
            mounted = False
            with open("/proc/mounts") as fd:
                lines = fd.readlines()
                for line in lines:
                    fields = line.split()
                    if fields[1] == default_cgroup_root:
                        mounted = True
                        break
            if not mounted:
                mount_cgroup_root(default_cgroup_root)
                changed = True
            cp = default_cgroup_root
        else:
            alt_cgroup_root = "/cgroup"
            if not os.path.exists(alt_cgroup_root):
                makedirs(alt_cgroup_root)
                changed = True
            cp = alt_cgroup_root
    else:
        cp = os.path.commonprefix(cgmounts.values())
        if not os.path.exists(cp):
            cp = os.path.dirname(cp)
    for ss in CG_SUBSYSTEMS:
        if ss not in cgmounts:
            mount_cg(cp, ss)
            changed = True
    cgmounts = get_cgmounts()
    s, c = check_cpu_mount(cgmounts)
    if s > rs: rs = s
    if c: changed = c
    s, c = enable_memory_use_hierarchy(cgmounts)
    if s > rs: rs = c
    if c: changed = c
    return (rs, changed)

def main():
    parser = argparse.ArgumentParser(
        description=textwrap.dedent("""\
            Cgroups based Oracle DB resouce manager and monitor.
            Valid commands are listed below"""),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    subparsers = parser.add_subparsers(
        help="Run '%(prog)s command -h' for additional help",
        title="commands")
    #
    help = "Check if the system has been configured to use cgroups"
    sp_check = subparsers.add_parser(
        "check",
        help=help,
        description=help)
    add_standard_options(sp_check)
    sp_check.set_defaults(func=f_check)
    #
    help = "Prepare system for using cgroups"
    description = \
        help + \
        " including mounting cgroup hierarchy and setting default parameters"
    sp_prepare = subparsers.add_parser(
        "prepare",
        help=help,
        description=description)
    add_standard_options(sp_prepare)
    sp_prepare.set_defaults(func=f_prepare)
    # adddb
    help = "Add database instance"
    description = \
        help + \
        " to configuration file and create or update" + \
        " corresponding cgroup. If instance is already in" + \
        " config file, make sure that attributes are in sync."
    sp_adddb = subparsers.add_parser(
        "adddb",
        help=help,
        description=description)
    add_standard_options(sp_adddb)
    sp_adddb.set_defaults(func=f_adddb)
    required_named = sp_adddb.add_argument_group('required named arguments')
    required_named.add_argument(
        "--instance_name",
        help="Instance name, case sensitive",
        required=True)
    sp_adddb.add_argument(
        "--cpu_shares",
        default=DEFAULT_CPU_SHARES,
        type=int,
        help="CPU shares out of {0} total, default %(default)s".format(TOTAL_CPU_SHARES))
    sp_adddb.add_argument(
        "--promised_cpus",
        default=0,
        type=int,
        help="Promised number of CPUs, default %(default)s")
    # deldb
    help = "Delete database instance"
    description = \
        help + \
        " from configuration file and delete " + \
        " corresponding cgroup. If instance is still running" + \
        " cgroup is not is not deleted, but cpu.shares is set" + \
        " to default value and promised_cpus is set to 0."
    sp_deldb = subparsers.add_parser(
        "deldb",
        help=help,
        description=description)
    add_standard_options(sp_deldb)
    sp_deldb.set_defaults(func=f_deldb)
    required_named = sp_deldb.add_argument_group('required named arguments')
    required_named.add_argument(
        "--instance_name",
        help="Instance name, case sensitive",
        required=True)
    # listdb
    help = "List configured databases"
    description = \
        help + \
        " along with corresponding cpu_shares and promised_cpus"
    sp_listdb = subparsers.add_parser(
        "listdb",
        help=help,
        description=description)
    add_standard_options(sp_listdb)
    add_output_format_option(sp_listdb)
    sp_listdb.set_defaults(func=f_listdb)
    # monitor
    help = "Run monitoring loop"
    description = \
        help + \
        ". Start supplemental monitoring process(s)" + \
        " and then start main monitoring loop"
    sp_monitor = subparsers.add_parser(
        "monitor",
        help=help,
        description=description)
    add_standard_options(sp_monitor, enable_console_logging=False)
    sp_monitor.add_argument(
        "-i",
        "--sample_interval",
        default=5,
        type=int,
        metavar="INTERVAL",
        help="Stats sample interval in seconds, default %(default)s")
    sp_monitor.add_argument(
        "-c",
        "--config_sample_interval",
        default=300,
        type=int,
        metavar="INTERVAL",
        help="Configuration sample interval in seconds, default %(default)s")
    sp_monitor.set_defaults(func=f_monitor)
    #
    args = parser.parse_args()
    main_wrapper(args)(args.func)(args)

def main_wrapper(namespace):
    def wrapper(func):
        @wraps(func)
        def wrap(*args, **kwargs):
            validate_logging_options(namespace)
            check_is_root()
            config_logging(namespace)
            log_args(namespace, logger)
            logger.info("Starting {0}".format(namespace.prog))
            try:
                rv = func(*args, **kwargs)
            except BaseException as e:
                tbf = traceback.format_exc()
                for line in tbf.split(os.linesep):
                    logger.error(line)
                sys.exit(R_ERROR)
            change_msg = "changes to the system configuration have been made"
            if rv[1]:
                logger.info(change_msg)
            else:
                logger.info("no " + change_msg)
            logger.info(
                "End of {0}, status {1}".format(
                    namespace.prog,
                    R_STATUS[rv[0]]
                )
            )
            sys.exit(rv[0])
        return wrap
    return wrapper

def validate_logging_options(args):
    if not os.path.exists(args.base_dir):
        raise RuntimeError("directory does not exist: {0}".format(args.base_dir))
    if not os.path.isdir(args.base_dir):
        raise RuntimeError("not a directory: {0}".format(args.base_dir))
    if not os.access(args.base_dir, os.W_OK | os.X_OK | os.R_OK):
        raise RuntimeError("not writable: {0}".format(args.base_dir))

def get_hostname():
    return socket.getfqdn()

def get_log_file_name(prog):
    return ":".join([
        get_hostname(),
        prog,
        time.strftime("%Y%m%d%H%M%S", time.gmtime()),
        str(os.getpid()) + ".log"])

def config_logging(args, logger_=None):
    base_dir = args.base_dir
    log_dir = os.path.join(base_dir, "logs")
    if not os.path.exists(log_dir):
        makedirs(log_dir)
    log_file = os.path.join(log_dir, get_log_file_name(args.prog))
    log_level = getattr(logging, args.log_level)
    log_format = "%(asctime)s|%(levelname)s|%(message)s"
    if logger_ is None:
        logger_ = logger
    logger_.setLevel(log_level)
    fh = logging.FileHandler(log_file)
    fh.setLevel(log_level)
    fh.setFormatter(logging.Formatter(log_format))
    logger_.addHandler(fh)
    if args.console_logging:
        ch = logging.StreamHandler()
        ch.setLevel(log_level)
        ch.setFormatter(logging.Formatter(log_format))
        logger_.addHandler(ch)

def log_args(args, logger):
    logger.info("Program arguments:")
    for arg in args._get_kwargs():
        logger.info("{0} = {1}".format(*arg))
    logger.info("End of program arguments")

def add_config_file_option(parser):
    default_config_file = os.path.splitext(
        os.path.basename(
            os.path.realpath(__file__)))[0] + ".conf"
    parser.add_argument(
        "--config_file",
        default=default_config_file,
        help="configuration file, default: %(default)s",
        metavar="CONF")

def add_output_format_option(parser):
    parser.add_argument(
        "--output_format",
        default="TAB",
        choices=set(["TAB", "CMD"]),
        help="Output format. The choices are TAB and CMD." + \
            " TAB is tabular format and CMD outputs command that can" + \
            " be used to recreate configuration",
        metavar="FORMAT")

def add_standard_options(parser, enable_console_logging=True):
    add_logging_options(parser, enable_console_logging)
    add_prog(parser)
    add_config_file_option(parser)

def read_config_file(config_file):
    with open(config_file) as fd:
        fcntl.flock(fd, fcntl.LOCK_EX)
        config = json.loads(fd.read())
    return config

def check_config_file(config_file):
    logger.info("Checking configuration file {0}".format(config_file))
    try:
        read_config_file(config_file)
        logger.info("Configuration file OK")
        return (R_SUCCESS, False)
    except Exception as e:
        logger.error("Can not validate configuration file: {0}, {1!s}".format(
            config_file,
            e))
        return R_ERROR, False

def f_adddb(args):
    rs = R_SUCCESS
    changed = False
    config_file = get_configi_file(args)
    s, c = check_config_file(config_file)
    if s > rs: rs = s
    changed = changed or c
    if rs == R_ERROR: return (rs, changed)
    validate_cpu_shares(args.cpu_shares)
    validate_promised_cpus(args.promised_cpus)
    changed = cgcreate(
        config_file,
        get_cgmounts(),
        args.instance_name,
        args.cpu_shares,
        args.promised_cpus)
    return (rs, changed)

def f_deldb(args):
    rs = R_SUCCESS
    changed = False
    config_file = get_config_file(args)
    s, c = check_config_file(config_file)
    if s > rs: rs = s
    changed = changed or c
    if rs == R_ERROR: return (rs, changed)
    changed = cgdelete(config_file, get_cgmounts(), args.instance_name)
    return (rs, changed)

def f_listdb(args):
    rs = R_SUCCESS
    changed = False
    config_file = get_config_file(args)
    s, c = check_config_file(config_file)
    if s > rs: rs = s
    changed = changed or c
    if rs == R_ERROR: return (rs, changed)
    s, c = list_databases(config_file, args)
    if s > rs: rs = s
    changed = changed or c
    return (rs, changed)

def list_databases(config_file, args):
    config = read_config_file(config_file)
    total_cpu_shares = 0
    total_promised_cpus = 0
    header_line = \
        "Instance Name CPU Shares % Total Promised CPUs"
    separator_line = \
        "------------- ---------- ------- -------------"
    if args.output_format == "TAB":
        logger.info(header_line)
        logger.info(separator_line)
    for instance_name in config.keys():
        cpu_shares = config[instance_name][CGS_CPU][CGP_CPU_SHARES]
        promised_cpus = config[instance_name][CGA_PROMISED_CPUS]
        total_cpu_shares += cpu_shares
        total_promised_cpus += promised_cpus
    for instance_name in sorted(config.keys()):
        cpu_shares = config[instance_name][CGS_CPU][CGP_CPU_SHARES]
        promised_cpus = config[instance_name][CGA_PROMISED_CPUS]
        if args.output_format == "TAB":
            logger.info("{0:13s} {1:10d}{2:7.1f}% {3:13d}".format(
                instance_name,
                cpu_shares,
                cpu_shares * 100.0 / total_cpu_shares,
                promised_cpus))
        elif args.output_format == "CMD":
            logger.info(
                "adddb --instance_name {0} --cpu_shares {1} --promised_cpus {2}".format(
                    instance_name,
                    cpu_shares,
                    promised_cpus))
    if args.output_format == "TAB":
        logger.info(separator_line)
    logger.info("Total CPU Shares: {0}".format(total_cpu_shares))
    logger.info("Total Promised CPUs: {0}".format(total_promised_cpus))
    return (R_SUCCESS, False)

def validate_cpu_shares(cpu_shares):
    if cpu_shares < 2:
        raise ValueError(
            "cpu_shares must be an integer greater than 2"
        )

def validate_promised_cpus(promised_cpus):
    if promised_cpus < 0:
        raise ValueError(
            "promised_cpus must be positive integer"
        )

class ConfigMonitor(object):
    def __init__(self, args, out_queue):
        self.args = copy.copy(args)
        self.args.prog = self.__class__.__name__
        self.out_queue = out_queue
        
    def monitor_loop(self):
        logger = logging.getLogger(self.__class__.__name__)
        config_logging(self.args, logger)
        interval = self.args.config_sample_interval
        config_file = get_config_file(self.args)
        out_queue = self.out_queue
        log_args(self.args, logger)
        logger.info("Starting main config monitoring loop")
        try:
            while True:
                config = read_config_file(config_file)
                out_queue.put(config)
                logger.info("Sent config to the queue")
                time.sleep(interval)
        except KeyboardInterrupt:
            logger.info("Got KeyboardInterrupt. Exiting...")
        except BaseException as e:
            tbf = traceback.format_exc()
            logger.error("Unhandled exception during main config monitoring loop:")
            for line in tbf.split(os.linesep):
                logger.error(line)
            raise

def get_config_file(args):
    return os.path.join(args.base_dir, args.config_file)

def get_logs_dir(args):
    return os.path.join(args.base_dir, "logs")

def get_stats_dir(args):
    return os.path.join(args.base_dir, "stats")

def f_monitor(args):
    config_file = get_config_file(args)
    validate_interval(args.sample_interval)
    validate_interval(args.config_sample_interval)
    config_queue = Queue()
    config_monitor = ConfigMonitor(args, config_queue)
    config_monitor_proc = Process(
        target=config_monitor.monitor_loop,
        args=()
    )
    config_monitor_proc.daemon = True
    config_monitor_proc.start()
    logger.info(
        "Started config monitor process, pid = {0}".format(config_monitor_proc.pid))
    stats_dir = get_stats_dir(args)
    if not os.path.exists(stats_dir):
        os.makedirs(stats_dir)
    if not os.path.isdir(stats_dir):
        raise RuntimeError("{0} is not a directory".format(stats_dir))
    logger.info("Using {0} directory for stats output".format(stats_dir))
    stats_writer = StatsWriter(stats_dir)
    config = read_config_file(config_file)
    monitor_loop(
        args.sample_interval,
        stats_writer,
        config,
        config_queue)

def monitor_loop(interval, writer, config, config_queue):
    prior_sample = StatsSample(config)
    sleep_till_next_sample(prior_sample.sample_time, interval)
    while True:
        sample = StatsSample(config)
        writer.write(sample.sample_time, sample.dumps(prior_sample))
        prior_sample = sample
        try:
            config = config_queue.get(False)
            logger.debug("Got configuration from queue")
        except QueueEmpty:
            pass
        sleep_till_next_sample(sample.sample_time, interval)

class sigterm_handler(object):
    def __init__(self):
        pass
    def handler(self, signum, frame):
        raise TerminatedException()
    def __enter__(self):
        self.oldhandler = signal.signal(signal.SIGTERM, self.handler)
    def __exit__(self, *args):
        signal.signal(signal.SIGTERM, self.oldhandler)

class Command(object):
    def __init__(self, *args, **kwargs):
        self.args = args
        self.kwargs = kwargs
        self.process = None

    def run(self, timeout=None, stdin=None):
        def target(stdin):
            self.process = Popen(*self.args, **self.kwargs)
            self.stdout, self.stderr = self.process.communicate()

        with sigterm_handler():
            try:
                thread = threading.Thread(target=target, args=(stdin,))
                thread.start()
                thread.join(timeout)
                is_alive = thread.is_alive()
                if is_alive:
                    self.process.terminate()
                    thread.join()
                return is_alive
            except TerminatedException:
                if self.process:
                    if self.process.poll() is None:
                        self.process.terminate()
                raise

if __name__ == "__main__":
    main()
