# BUG-103 integration with the Iris customer

[AGENT], 2026-09-05. The user authorized executing the landing sequence:
A2 first, then rebased/re-gated BUG-103, followed by separate interface and
A3 worktrees. This note records the second step. No push is authorized.

## Integrated tree and conflict disposition

A2 main: `700128f37c60740a370ec275ff6c6d1ca6bccdf3`.
Original BUG-103 reviewed tip:
`8fc63ba71b82660c037e051cedadb353b0f532f4`, retained as
`snapshot/bug103-before-a2-integration-20260905`.
Rebased and tested tip:
`8d8f54879328d748c15ac97178bcb2ccc7d7b81c`.

The only rebase conflict was the two added root `HANDOFF.md` files.
Their exact original bytes now live at:

- `docs/2026-09-05_iris-customer-handoff.md`;
- `docs/2026-09-05_bug103-array-conversion-handoff.md`.

The root handoff gives the current integration status and points to them.
Their old review/authorization statements are historical. The original
BUG-103 evidence's `HANDOFF.md` checksum refers to its original bytes,
which remain verifiable at the second dated path. No original sealed
evidence was rewritten to describe a later state.

All 174 original BUG-103 changed paths other than its root handoff retain
their source-reviewed bytes. Neither spike changed during integration.
There was no semantic, proof, frontend, fixture, baseline, dependency-pin,
or gate change introduced by the rebase. The runtime change remains the
reviewed array-value conversion normalization and its location-bound proof.

Independent source reviews remain
`docs/2026-09-05_iris-customer-review.md` and
`docs/2026-09-05_bug103-array-conversion-review.md`, both PASS.
The integration agent separately inspected the conflict resolution and
verified the byte comparisons above; that inspection is not represented
as another independent source audit.

## Fresh combined-tree validation

All Lean/Lake work used `scripts/capped`, `GOLEAN_MEM_MAX=16G`, and
`LEAN_NUM_THREADS=3`. Root build caches were lane-local; A1 and A2 caches
were independent copies of the completed A2 lane, with no symlink escaping
this worktree. Upstream tracked symlinks and exact pins were preserved.
This was not a clean network bootstrap or a full upstream rebuild.

- `scripts/capped scripts/ci --diff`: **PASS, exit 0**.
  Warning-free core build, frontend unit and harness checks, **202 eval
  checks**, and fresh negative oracle checks **394/394 PASS**.
- Full differential: **3,598 cases, 3,353 PASS / 245 FAIL**. Every ID,
  result and failure stage matches the original BUG-103 full measurement;
  the checked-in baseline matches without changes. Existing stage
  alternatives remain intact. The differential runner's exit 1 records
  those known failures; CI correctly judges the complete failing set.
- One slow-tier case, `imported-goose/channel/google-search`, retains
  its visibly reported cached certificate with fresh sampling/coupling
  checks. Its complete allowed set was not re-certified. No frontend file
  changed, so the special merged-tip frontend `--slow` rule is not triggered.
- `bash spikes/gate-a1/check`: **PASS, exit 0**. All spike modules freshly
  elaborated, 12 required exports, 529 constants checked against only the
  classical trio, and all three compiled poisoned-import controls rejected.
- `bash spikes/iris-customer/check`: **PASS, exit 0**. Ten customer
  modules plus aggregate freshly elaborated, 18 required exports, 941
  constants checked against only the classical trio, all three poison
  controls rejected, fresh native lowering matched the complete artifact,
  and all **3/3** customer differential controls passed.
- The report-only reconciler retains the existing C13 and C5 medium
  findings; no high finding. They were not silently treated as resolved.

Go oracle: `go1.26.5`; Lean: `leanprover/lean4:v4.32.2`.
The result records bind to the clean tested commit above. Generic
differential metadata says `full_run=unknown`; the full claim here comes
from CI's regenerated full corpus and exact 3,598/3,598 ID/baseline check,
not from interpreting that metadata field as true.

## Evidence and remaining boundary

`docs/evidence/2026-09-05_bug103-integration/README.md` indexes complete
logs, exit statuses, raw full/negative/customer records, source hashes and
integration checks. Its source inventory binds 3,691 files, including core,
frontend, corpus, baselines, harness and both spikes; all hashes were
rechecked after the gates. The final integration commit adds only this
record, evidence and handoff status to the tested source tree.

A2 still validates a bounded sequential customer; normalization still does
not establish Go static typing or conversion admissibility. The semantic
interface and A3 checker belong to their own lanes. This integration is
ready for the coordinator's authorized fast-forward merge into main.
