# W4.2 census + rendered-tier evidence (2026-08-21)

Tracked records for numbers `docs/raft-w42-log.md` quotes. They exist
because the pre-merge audit found the log calling `artifacts/w42/sweep-*`
"the tracked artifact pair" (finding B-F4) when `artifacts/` is
gitignored — and because the rendered-tier family table had been computed
by a classifier that was never committed (finding B-F5). A number nobody
can re-derive from tracked material is not a record.

| file | produced by | what it pins |
|---|---|---|
| `sweep-pre.txt` | `tools/raftsubject/sweep.py --tree <pre-swap tree>` | the PRE-swap census: 14 quarantined subject declarations, **0 LIVE**, 30 imported stdlib stubs, residual sinks NONE (census closed) |
| `sweep-post-swap.txt` | `tools/raftsubject/sweep.py` (default tree = `raftsubject/`) | the POST-swap census: 24 quarantined, **5 LIVE** + 2 LIVE imported stubs, 7 residual sinks — the W4.2 item-1 headline |
| `tracefamilies.txt` | `tools/raftsubject/tracefamilies.py` | the 309 rendered-expectation blocks by renderer family, under both the command-anchored and content-anchored rules |

## Reproducing

`sweep-post-swap.txt` regenerates from the tree in the repo:

    GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend
    tools/raftsubject/sweep.py

`sweep-pre.txt` needs the PRE-swap subject tree — `raftsubject/` with the
D-5 no-op `logger.go` overlay in place of the verbatim upstream file, as
it stood before W4.2 item 1. That tree is exactly `raftsubject/` at the
parent of the item-1 commit (verified file-for-file; the only difference
from the scratch copy the arc swept is `README.md`, which `sweep.py`
ignores):

    git archive <item-1 commit>^ raftsubject | tar -x -C <scratch>
    tools/raftsubject/sweep.py --tree <scratch>/raftsubject --out <out>

Both reports were re-run after the branch was rebased onto `main`, against
a frontend rebuilt from `main`'s `tools/nativefrontend`, and reproduce
byte-for-byte apart from the header's frontend path.

`tracefamilies.txt` needs only `deps/raft` (`scripts/setup-deps`):

    tools/raftsubject/tracefamilies.py

## Reading notes

- The `# sweep.py — frontend ...` header line carries the ABSOLUTE path of
  the frontend binary the run used, so it will differ per worktree. That
  line is provenance, not a number; nothing else in the report depends on
  it.
- The delta between the two sweeps is exactly the ten `DefaultLogger`
  formatting methods joining the quarantine (and the `log` package's
  declaration-only stubs joining the imported set). Nothing leaves. The
  argument that all seven live entries are dead DYNAMICALLY, with both
  halves probed, is item 1 of the log — the census does not make it and
  is not meant to.
- `tracefamilies.txt` prints two readings on purpose; they agree on
  `pure log lines` 58, `raft-state` 30, `status` 18, `raft-log` 15 and
  differ on how the `stabilize`/`process-ready`/`deliver-msgs` mass
  splits. The load-bearing numbers are the four they agree on.
