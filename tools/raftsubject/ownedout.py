"""ownedout.py — the raft instruments' scratch-directory OWNERSHIP (deep-clean review
2026-10-26, DC10 / validation V4; [USER] ruling of 2026-10-26, relayed).

`runprobe.py --out`, `codeccheck.py --out` and `tracereplay.py`'s per-trace scratch used to
`shutil.rmtree(out, ignore_errors=True)` whatever the path named — a populated directory the
tool never created, even with `--keep` (the deletion happens BEFORE the run), and a failed
deletion was swallowed. Here a directory is claimed only when it is new, empty, or carries
this marker from an earlier run of one of these tools; anything else is refused by name, and a
deletion that fails is reported as the invocation's failure.
"""

import os
import shutil
import sys

MARKER = ".golean-raftsubject-scratch"


def claim(out, tool):
    """Return the absolute path of `out`, freshly created and marked as `tool`'s scratch.

    An existing directory is re-created only when it is empty or carries MARKER (a previous
    run of these tools left it); a populated directory without the marker, a non-directory,
    or a symlink is a refusal (exit 2) — never deleted."""
    out = os.path.abspath(out)
    if os.path.lexists(out):
        if os.path.islink(out) or not os.path.isdir(out):
            sys.exit("%s: --out %s exists and is not a plain directory (a symlink or a file) — refusing to delete it" % (tool, out))
        entries = os.listdir(out)
        if entries and MARKER not in entries:
            sys.exit("%s: --out %s is a populated directory this tool did not create (%d entries, no %s marker) — "
                     "refusing to delete it; pass a new or empty directory, or one an earlier run of these tools left behind"
                     % (tool, out, len(entries), MARKER))
        try:
            shutil.rmtree(out)
        except OSError as e:
            sys.exit("%s: could not remove the earlier scratch directory %s: %s" % (tool, out, e))
    os.makedirs(out)
    with open(os.path.join(out, MARKER), "w") as f:
        f.write("scratch of tools/raftsubject/%s — created by it, deleted by it (unless --keep)\n" % tool)
    return out


def release(out, tool):
    """Delete `out`, which `claim` created in this invocation. A missing marker or a failed
    deletion is reported on stderr and returns False (the caller's exit must not be a pass)."""
    if not os.path.isfile(os.path.join(out, MARKER)):
        sys.stderr.write("%s: NOT deleting %s — its ownership marker is gone\n" % (tool, out))
        return False
    try:
        shutil.rmtree(out)
    except OSError as e:
        sys.stderr.write("%s: could not remove the scratch directory %s: %s\n" % (tool, out, e))
        return False
    return True


def machine_exit_agrees(returncode, status):
    """golean native-json-run's exit-code contract (docs/cli.md §2.1): 0 iff the observation's
    status is `ok`, 1 for every other status; anything else — a signal (negative under
    subprocess), 2 (a usage/decoder refusal), 124/137 through a wrapper — produced no verdict.
    Returns None when status and code agree, else the reason they do not."""
    if returncode not in (0, 1):
        if returncode < 0:
            return "the machine process died on signal %d (no verdict)" % -returncode
        return "the machine process exited %d, neither 0 (ok) nor 1 (a stop) — no verdict" % returncode
    if (returncode == 0) != (status == "ok"):
        return "the machine's exit status %d and its observation status %r disagree (0 iff ok)" % (returncode, status)
    return None
