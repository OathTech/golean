# Semantic interface review evidence

[AGENT], 2026-09-05. Source base `700128f3`; implementation files are bound
by `reviewed-source.sha256`, whose paths are relative to the worktree root.
`SHA256SUMS` binds this evidence directory's files and is checked from here.

The independent report is preserved unchanged as `review.md`. Its A1/A2
gate logs, A2 differential result/metadata, source-equivalence checks and
import graph are retained. `tracked-code.diff` records tracked-file changes;
the source manifest also covers the added files, which were untracked during
review. `coordinator-ci.log` is the separate ordinary CI PASS; its corpus
and negative comparisons explicitly use older recorded results. The first
interface-only log is retained as an earlier diagnostic run, with its own
source fingerprint; it is not substituted for the final source binding.

`promoted-audit-probe.py` is the exact executed independent mutation script.
Its compile log is empty except for its appended exit marker (success), and
all three rejection logs name the unused promoted-origin axiom. To reproduce
after building the three packages, copy that script into a fresh directory
one level below the repository's `.tmp`, then execute the copy with Python.
Its `parents[2]` root calculation relies on that original scratch layout;
running it directly inside this evidence directory is not supported. It
creates isolated copied build trees and leaves scratch for inspection.

Ordinary reproduction from the repository root:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash spikes/gate-a1/check
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash spikes/iris-customer/check
```

Core and customer builds used independent local caches at exact tracked-clean
dependency pins, plus fresh module elaborations. No clean network bootstrap
or complete fresh upstream dependency elaboration is claimed. The new
interface changes no interpreter/frontend/corpus baseline behavior. The
three customer cases were freshly measured; the full corpus was not rerun
by this review. BUG-103 and A3 combined-tree validation are separate records.
