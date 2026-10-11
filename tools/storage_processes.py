"""Stop a gate's observed descendants, including children in new sessions."""
import os
import signal
import subprocess
import time


def stop_tree(root_pid):
    table = subprocess.check_output(['ps', '-eo', 'pid=,ppid='], text=True)
    parents = {int(p): int(parent) for p, parent in (line.split() for line in table.splitlines())}
    selected = {root_pid}
    while True:
        expanded = selected | {pid for pid, parent in parents.items() if parent in selected}
        if expanded == selected:
            break
        selected = expanded
    # pidfds pin identities across the grace interval; never signal a reused
    # PID. This guard is Linux-specific, like the repository's capped runner.
    handles = []
    try:
        for pid in selected:
            try:
                handles.append(os.pidfd_open(pid))
            except ProcessLookupError:
                pass
        for handle in handles:
            try:
                signal.pidfd_send_signal(handle, signal.SIGTERM)
            except ProcessLookupError:
                pass
        time.sleep(5)  # allow audit handlers to seal their compact evidence
        for handle in handles:
            try:
                signal.pidfd_send_signal(handle, signal.SIGKILL)
            except ProcessLookupError:
                pass
    finally:
        for handle in handles:
            os.close(handle)
