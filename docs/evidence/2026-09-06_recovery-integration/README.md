# Recovery static contract integration evidence

[AGENT], 2026-09-06. This seals the reviewed static recovery increment
`e8a665e9` merged into `c2057e78`, with its separately reviewed four-file
public promotion. The seven semantic and five test modules match the author
commit exactly; the promotion matches independent review `f569eb7f` exactly.
The initial independent review `1ae77483` required distinct diagnostic
classes. Follow-up `c2057e78` closes RS-1, including a generic proof against
the separately compiled original checker that accepted programs are unchanged.

Fresh capped ordinary `scripts/ci` completed with exit 0 (session 36327).
It includes a warning-free default build, interface audit (72 exports,
13,328 constants, all 15 compiled poison controls), recovery audit (46
exports, 10,879 constants, all five compiled poisons), the Boolean and
admission gates, frontend pins/tests, and all 202 eval checks. The report-only
reconciler has three MEDIUM findings and no HIGH finding: historical version
citations, one frontier citation and four dangling BUG references. Those
findings remain visible; this increment does not claim their resolution.

Session 84146 subsequently completed with exit 0 for all three fresh gates:

- `scripts/check-recovery-typing`: native artifact checks and all five
  Go/Lean cases pass. Independent controls distinguish input dependence,
  LIFO handler order, and direct versus indirect recovery.
- `spikes/gate-a1/check`: 12 required exports, 13,565 checked constants,
  all three compiled poison controls and counterexamples pass.
- `spikes/iris-customer/check`: 18 exports, 13,976 checked constants,
  all three poison controls, fresh artifact check, and all three native
  normal/recovered/uncaught differential cases pass.

All commands used `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3` through
`scripts/capped`, with unchanged Lean/Go/dependency pins. The logs preserve
original source paths and metadata. Source files remained frozen throughout
these gates; documentation and evidence bookkeeping followed.

The 3,607-case executable record (3,363 PASS / 244 known FAIL) and 394-case
negative record are explicitly **cached**, from the preceding full renderer
integration. `runtime-reuse.json` lists every changed member of that sealed
source inventory, and records the rebuilt binary hash without asserting
binary identity. The runtime and frontend implementation remain unchanged.
No fresh full corpus or slow certification is claimed here.

This is static O2 admission, with a useful second native witness. Generic
recovery setup, runtime preservation/readout, reusable Iris rules, B7/I1 and
the final sprint gates remain incomplete. `sources.sha256` binds the tested
source relative to the integration worktree; `SHA256SUMS` seals this evidence.
