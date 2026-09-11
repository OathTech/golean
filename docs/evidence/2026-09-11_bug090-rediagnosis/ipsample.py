#!/usr/bin/env python3
"""Leaf-IP sampling profiler over ptrace (no rebuild, no perf).

`perf` is unavailable on this box to an unprivileged user
(kernel.perf_event_paranoid = 4), and gdb/valgrind are not installed, so
this samples the instruction pointer of the traced child's RUNNING
non-leader threads with PTRACE_SEIZE/PTRACE_INTERRUPT every --interval-ms
and attributes each sample to the containing function via `nm` over the
mapped ELF files (load bias computed from the PT_LOAD table). The golean
leader thread only waits (observed: state S while a worker thread runs the
interpreter), so it is not seized; a tick on which no thread is running is
counted as idle. SCOPE: a FLAT profile of LEAF functions — no call stacks
(the binary has no frame pointers). It answers "where does the CPU sit",
not "who called it".

Usage: python3 ipsample.py --out prof.json --interval-ms 1 -- <cmd> [args...]
"""
import argparse
import bisect
import ctypes
import json
import os
import subprocess
import time

PTRACE_CONT, PTRACE_GETREGS = 7, 12
PTRACE_SEIZE, PTRACE_INTERRUPT = 0x4206, 0x4207
__WALL = 0x40000000
libc = ctypes.CDLL(None, use_errno=True)
libc.ptrace.restype = ctypes.c_long
libc.ptrace.argtypes = [ctypes.c_long, ctypes.c_long, ctypes.c_void_p, ctypes.c_void_p]


class Regs(ctypes.Structure):
    _fields_ = [(n, ctypes.c_ulonglong) for n in (
        "r15", "r14", "r13", "r12", "rbp", "rbx", "r11", "r10", "r9", "r8", "rax", "rcx",
        "rdx", "rsi", "rdi", "orig_rax", "rip", "cs", "eflags", "rsp", "ss", "fs_base",
        "gs_base", "ds", "es", "fs", "gs")]


def ptrace(req, pid, addr=0, data=0):
    r = libc.ptrace(req, pid, ctypes.c_void_p(addr), ctypes.c_void_p(data))
    if r == -1:
        e = ctypes.get_errno()
        raise OSError(e, f"ptrace({req}, {pid}) failed: {os.strerror(e)}")
    return r


def load_segments(path):
    out = subprocess.run(["readelf", "-lW", path], capture_output=True, text=True).stdout
    return [(int(p[1], 16), int(p[2], 16)) for p in (l.split() for l in out.splitlines())
            if p and p[0] == "LOAD"]  # (offset, vaddr)


def load_symbols(path):
    out = subprocess.run(["nm", "-n", "--defined-only", path], capture_output=True, text=True).stdout
    if not out.strip():
        out = subprocess.run(["nm", "-D", "-n", "--defined-only", path], capture_output=True, text=True).stdout
    addrs, names = [], []
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] in "TtWwiI":
            addrs.append(int(parts[0], 16)); names.append(parts[2])
    return addrs, names


def read_maps(pid):
    maps = []
    with open(f"/proc/{pid}/maps") as f:
        for line in f:
            parts = line.split()
            if len(parts) < 6 or "x" not in parts[1] or not parts[5].startswith("/"):
                continue
            start, end = (int(x, 16) for x in parts[0].split("-"))
            maps.append((start, end, int(parts[2], 16), parts[5]))
    return maps


def thread_state(pid, tid):
    with open(f"/proc/{pid}/task/{tid}/stat") as f:
        s = f.read()
    return s[s.rindex(")") + 2]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--interval-ms", type=float, default=1.0)
    ap.add_argument("--top", type=int, default=40)
    ap.add_argument("cmd", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
    # Pre-load the executable's symbol table (100k symbols take ~0.4 s to
    # parse) so the first sample is not delayed past a short child's exit.
    symtabs = {os.path.realpath(cmd[0]): load_symbols(os.path.realpath(cmd[0]))}
    t0 = time.monotonic()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    pid = proc.pid
    maps, biases = None, {}
    seized, dead = set(), set()
    samples, per_thread = {}, {}
    total = idle_ticks = leader_running_ticks = 0
    regs = Regs()
    interval = a.interval_ms / 1000.0
    while proc.poll() is None:
        time.sleep(interval)
        try:
            tids = [int(t) for t in os.listdir(f"/proc/{pid}/task")]
        except FileNotFoundError:
            break
        if maps is None:
            try:
                maps = read_maps(pid)
            except FileNotFoundError:
                break
            for (start, end, off, path) in maps:
                if path not in symtabs:
                    symtabs[path] = load_symbols(path)
                for (soff, svaddr) in load_segments(path):
                    if (soff & ~0xfff) == off:
                        biases[(start, path)] = start - (svaddr & ~0xfff)
                        break
                else:
                    biases[(start, path)] = start - off
        sampled_this_tick = False
        for tid in tids:
            if tid == pid or tid in dead:
                if tid == pid:
                    try:
                        if thread_state(pid, tid) == "R":
                            leader_running_ticks += 1
                    except (FileNotFoundError, ProcessLookupError):
                        pass
                continue
            try:
                if thread_state(pid, tid) != "R":
                    continue
                if tid not in seized:
                    ptrace(PTRACE_SEIZE, tid)
                    seized.add(tid)
                ptrace(PTRACE_INTERRUPT, tid)
                wtid, status = os.waitpid(tid, __WALL)
            except (OSError, ChildProcessError):
                dead.add(tid)
                continue
            if os.WIFEXITED(status) or os.WIFSIGNALED(status):
                dead.add(tid)
                continue
            if not os.WIFSTOPPED(status):
                continue
            sig, event = os.WSTOPSIG(status), status >> 16
            try:
                ptrace(PTRACE_GETREGS, tid, 0, ctypes.addressof(regs))
            except OSError:
                dead.add(tid)
                continue
            rip = regs.rip
            key = "?? (unmapped)"
            for (start, end, off, path) in maps:
                if start <= rip < end:
                    vaddr = rip - biases[(start, path)]
                    addrs, names = symtabs[path]
                    i = bisect.bisect_right(addrs, vaddr) - 1
                    mod = os.path.basename(path)
                    key = f"{mod}:{names[i]}" if i >= 0 else f"{mod}:?? +0x{vaddr:x}"
                    break
            samples[key] = samples.get(key, 0) + 1
            per_thread[tid] = per_thread.get(tid, 0) + 1
            total += 1
            sampled_this_tick = True
            inject = sig if (event == 0 and sig != 0) else 0
            try:
                ptrace(PTRACE_CONT, tid, 0, inject)
            except OSError:
                dead.add(tid)
        if not sampled_this_tick:
            idle_ticks += 1
        # Reap traced threads that exited: a seized non-leader thread stays a
        # zombie until its tracer waits on it, and the leader's own exit is
        # not reported until every other thread is gone.
        for tid in list(seized - dead):
            try:
                wtid, status = os.waitpid(tid, os.WNOHANG | __WALL)
            except ChildProcessError:
                dead.add(tid)
                continue
            if wtid == 0:
                continue
            if os.WIFEXITED(status) or os.WIFSIGNALED(status):
                dead.add(tid)
            elif os.WIFSTOPPED(status):
                try:
                    ptrace(PTRACE_CONT, tid, 0, 0)
                except OSError:
                    dead.add(tid)
    out, err = proc.communicate()
    wall = time.monotonic() - t0
    ranked = sorted(samples.items(), key=lambda kv: -kv[1])
    by_module = {}
    for k, v in samples.items():
        by_module[k.split(":")[0]] = by_module.get(k.split(":")[0], 0) + v
    result = {
        "cmd": cmd, "exit": proc.returncode, "wall_s_under_tracer": round(wall, 3),
        "interval_ms": a.interval_ms, "samples": total, "idle_ticks": idle_ticks,
        "leader_running_ticks_unsampled": leader_running_ticks,
        "samples_per_thread": {str(k): v for k, v in per_thread.items()},
        "scope": "leaf instruction pointer only, running non-leader threads, no call stacks",
        "by_module": by_module,
        "top": [{"symbol": k, "samples": v, "pct": round(100.0 * v / max(total, 1), 2)}
                for k, v in ranked[:a.top]],
        "child_stdout_tail": out.strip()[-300:], "child_stderr_tail": err.strip()[-300:],
    }
    with open(a.out, "w") as f:
        json.dump(result, f, indent=1)
        f.write("\n")
    print(f"samples={total} idle_ticks={idle_ticks} exit={proc.returncode} wall={wall:.2f}s")
    for row in result["top"][:25]:
        print(f"  {row['pct']:6.2f}%  {row['samples']:6d}  {row['symbol']}")


if __name__ == "__main__":
    main()
