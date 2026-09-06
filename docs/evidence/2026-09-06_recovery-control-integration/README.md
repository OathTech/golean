# Recovery control public integration

[AGENT] root integrator, 2026-09-06. The reviewed control commit
`f160d7ca` was merged cleanly into `4a8a8ad1`. All twenty-one author
inputs match the independent implementation review `9e6c4234` and its
reproducibility follow-up `ba930ba2`. The separate four-file facade/audit
promotion passed independent review `62377799`; all twenty-six reviewed
code/document inputs matched before final evidence bookkeeping.

Fresh capped ordinary CI, session 43232, completed with exit 0. It includes
the default build, all earlier gates, 202 evals and the new control gate:
124 exports, 13,824 declarations and seventeen compiled poison rejections.
The promoted interface checks 102 exports and 14,517 declarations, retaining
all nineteen prior poison controls and adding three, for twenty-two total.
The report-only reconciler has three MEDIUM findings and zero HIGH
(historical toolchain citations, one frontier citation and eight dangling
BUG references).

Fresh spike gates in session 62843 completed with exit 0. A1 checks twelve
exports, 14,370 declarations and three poison controls. The Iris spike
checks eighteen exports, 14,554 declarations and three poison controls,
plus a fresh native artifact and 3/3 Go/Lean cases. Commands use
`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped`, with Bash to invoke
the tracked non-executable spike scripts.

`sources.sha256` binds 215 input files. The runtime/frontend/observer
inventory remains unchanged apart from the nine declared proof/API/gate
differences from the renderer record. Full 3,607 and compile-negative 394
records remain explicitly cached, with exact original record hashes. The
unchanged second native fixture's 5/5 and control observations are reused
from the immediately preceding entry integration; its actual generic
setup/control instantiation was freshly checked in the control gate.
Neither reuse is a fresh whole-corpus claim.

The public contract now includes structural all-successor preservation,
terminal-aware progress, actual call/defer/recovery control rules and typed
readout/choice preservation for successful drivers. It still admits the
arbitrary string bytes and equal repanics whose terminal rendering repair
is outstanding. No unconditional driver no-refusal or complete functional
Iris customer theorem is claimed. B7/I1 and O1–O5 completion remain open.
