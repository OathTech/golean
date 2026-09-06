# Recovery entry public integration

[AGENT] coordinator, 2026-09-06. Reviewed entry `63769964` was merged
cleanly into `4158368f`, with public facade/audit promotion. The entry
implementation has independent review `997d74ed`; promotion has separate
review `29ac266d`. All eighteen reviewed inputs matched before the
post-validation documentation update. The only change to an original entry
code input removes one extra final LF from the Python audit script; its AST
is identical and the promotion review checked this explicitly.

Fresh validation on the frozen promoted source:

| Check | Result |
|---|---|
| Capped ordinary CI, session 63627 | Terminal exit 0; default build, frontend gates and 202 evals pass |
| Public interface | 84 exports; 14,046 declarations; all 19 compiled poison controls rejected |
| Recovery setup | 37 exports; 11,241 declarations; all 9 compiled poisons rejected |
| Full recovery typing/native gate | 46 exports; 5/5 differential cases and input/order/directness controls pass |
| Gate A1 | 12 exports; 13,752 declarations; all 3 poison controls rejected |
| Iris customer | 18 exports; 14,163 declarations; all 3 poisons, fresh native artifact and 3/3 differential cases pass |

Commands used the unchanged `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3`
envelope and `scripts/capped`. The first native/spike chain (session 20187)
completed the native gate, then exited 126 when directly executing the
tracked mode-100644 A1 shell script. That launch failure is retained in
`a1.log`. Session 22601 invoked both scripts through `bash`, as their file
mode requires, and completed with exit 0. No source, permission, profile or
resource cap changed to run those scripts. The CI reconciler reports three
MEDIUM findings and zero HIGH: historical toolchain citations, one frontier
citation and seven dangling BUG references. These remain report-only.

`sources.sha256` binds 196 source/gate inputs. `runtime-reuse.json` compares
the original renderer inventory: its only nine differences are proof/API/
gate files. The original full 3,607-case record (3,363 PASS, 244 known FAIL)
and 394 compile-negative records are explicitly cached, with their original
metadata and hashes. This proof-only increment makes no fresh whole-corpus
or binary-byte-identity claim. The full final runtime gates remain owed.

This milestone establishes actual generic setup, typed initialized storage,
derived structural well-formedness, readout and ordinary/deferred call
entry. It does not accept the separate control draft, renderer changes,
reusable Iris rules, B7/I1, or the final sprint decision packet.
