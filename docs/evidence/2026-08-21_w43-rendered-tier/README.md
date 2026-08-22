# W4.3 rendered-tier evidence (2026-08-21)

Added 2026-08-22 (launch audit D7-evidence-F1: this was the only one
of 26 evidence dirs with no README).

Provenance: the W4.3/W4.4 trace-differential milestone
(`docs/raft-w43-log.md`; merged at `35b18794`). All runs are
`tools/raftsubject/tracereplay.py` over `deps/raft`'s own datadriven
testdata (28 traces, 558 blocks), frontend + golean built at
`95145bc3` unless a file says otherwise.

- `go-side-rendered-148.txt` — the go-side rendered-tier census: per
  trace, `rendered a/b` per family; sums to 148/148 across 7
  families. Reproduce: `tracereplay.py --no-machine` at the recorded
  commit and project the rendered columns (re-reproduced byte-for-byte
  by the launch audit's D5 and D7 delegates).
- `trace-final-p1.txt` — the machine-tier partition-1 report text
  (the artifacts/ originals are gitignored; these are the tracked
  copies).
- `trace-final-p3-replicate-pause.txt` — partition 3. Partition 2
  (`probe_and_replicate`) has NO file here: its detached run was
  still in flight at the milestone (26/27 is the honest machine-tier
  number); the output inode died with the pruned worktree and was
  rescued live to `.tmp/p2-recovery/` (launch audit D5-F1).
- `sweep-post-widening.txt` — the post-widening sweep from the
  audit-fix rounds. Its first line's bare worktree path is historical
  (`raft-w43`, since pruned); the run is reproducible from the
  commands in `docs/raft-w43-log.md` wave 6.
