# I1 declaration type boundary — first review response

[AGENT] 2026-09-08, `land/i1-declarations`, responding to the coordinator's
independent review of `8b4a1aec`. [USER], firsthand in this session: “Can you
review, make fixes, then pause for a second review. You can also make other
improvements if they are obviously needed in the light of the review comments”.
The end state for this round is a fixed, validated branch awaiting that second
review. No merge or push is authorized by this request.

The [supplied review](evidence/2026-09-08_i1-declarations/coordinator-review.md)
is retained verbatim, SHA256
`11e316483ec9dbb337796faa390c0998f3fd5d5b9e0134ef2d9d272de43ddf36`.
Its independent corpus-wire comparison and gate results are the reviewer's
evidence at `8b4a1aec`; they do not certify the corrections below. The earlier
[landing record](2026-09-08_i1-declaration-landing.md) remains the history of
the initial implementation, superseded by this response for review status.

## Dispositions

| Finding | Disposition and control |
|---|---|
| R1 — discarded identity alarms | Fixed. Before returning success, the private declaration emitter checks both `checkKeyPathGrammar` and `displayConflictRefusal`, including alarms raised by nested identities. Four new red-first controls reproduced the bug: dotted path, middle-dot path, non-ASCII path and conflicting displays for one key. A legal foreign ASCII path stays positive. Every case also checks unchanged outer emitter state and whole-program executable bytes. No second key grammar or F7 widening is introduced. |
| R2 — member export/package mismatch | Fixed for fields and methods. Unexported names require a package; exported names require an empty package. Go uses Unicode Lu, whereas Lean's `Char.isUpper` is ASCII-only, so a small generated adapter table is byte-checked against the pinned Go oracle and its lookup compared against `unicode.IsUpper` at all 1,114,112 code points. ASCII, accented/Greek/supplementary uppercase, lowercase and Unicode titlecase controls exercise the actual byte decoder. Source identifier validity remains a source-checking obligation. |
| R3 — duplicate fields | Fixed by rejecting duplicate nonblank `MemberId`s without reordering. Repeated `_` fields stay valid, as required by pinned `deps/go/src/go/types/struct.go`; distinct private package identities remain distinct. Controls check refusals, repeated blanks, package distinctions and order sensitivity. |
| R4 — audit copies retained on success | Fixed. Scratch uses a package overlay of symlinks to unchanged build files; the poisoned module and every sidecar are excluded from aliases before compilation. Only the private poisoned source/artifacts and logs are written. All eight controls (including the new Unicode adapter and its test) must compile and then fail the post-import audit by name. A final import without overlays checks for poison leakage. Success removes only that invocation's freshly allocated scratch; failure retains it and its logs. Existing scratch is untouched. |
| R5 — nesting abort | Fixed. Raw JSON permits at most 64 nested containers, with a named refusal before further descent. Positive-at-limit, negative-above-limit and 10,000-level controls run normally. Public `decode(Json)` also gets a 64-type-node bound so callers cannot bypass the protection by constructing JSON themselves. These are adapter budgets, not Go type limits. |
| R6 — numeric exponent abort/allocation | Fixed. Numeric tokens are limited to 256 characters, and absolute decimal exponents to 1,024, before the pinned Lean numeric constructor runs. Valid numbers retain the original parser's value representation. Controls cover positive limits, both exponent signs, oversized tokens and `1e10000000000`, all with named budget refusals. |
| R7 — numeric cause lost | Fixed for the reported cases. Numeric grammar is checked before container parsing resumes: leading zero, missing integer/fraction/exponent digit and invalid numeric character are distinguished. `[01]`, `[.1]`, `[+1]`, `[NaN]`, `[1.]` and `[1e]` have cause-checking controls. |
| R8 — no declaration set/inventory producer | Recorded limitation, unchanged. This chunk serializes and decodes closed declaration TYPE identities. The complete nominal inventory, declaration-set closure, checked-source provenance and production package integration remain future I1 work. The three-entry inventory belongs only to the 24-type fixture. |
| R9 — diagnostic accounting | Clarified. The producer has eleven new refusal formats: ten in the unclassified inventory, while `declaration method %s has no signature` is covered by the existing `frontend-invariant` classifier. R1 reuses existing identity diagnostics. No classifier threshold is weakened. |
| R10 — no fixture re-pin guard | Recorded limitation, deferred. The byte pin and corrupt-artifact negative control detect producer drift against the checked-in expectation. They do not prevent a reviewer-approved change to producer and expectation together; there is no dedicated re-pin authorization guard. The fixture README requires a written reason, fresh output and matrix review. This round changes neither pin nor fixture bytes; a broader re-pin policy is not invented here. |
| R11 — cross-worktree scratch | Fixed. `check-declarations` sets its subprocess TMPDIR to this checkout's `.tmp`; the Python audit independently chooses that same local parent. A failure control with a foreign TMPDIR confirms it remains unused and diagnostics stay in the worktree. |

## Validation and handoff

Focused frontend and lowerdiag package tests pass. The updated declaration
gate passes the existing fixture pin/576-pair matrix, the new member/field and
resource controls, all-code-point Unicode comparison and compiled poison
controls. The named failure control retains its audit log and `failure.txt`
locally while ignoring the foreign TMPDIR. Full correction-gate results and
the clean committed source will be recorded here before the second-review
handoff. No second review has been run by this author.

**Candidate gate, [AGENT] 2026-09-08.** The full capped `scripts/ci --diff`
passed, actual exit 0, at frozen index tree
`da44f64574e6b959a64bb8923f669a58013a708d` over `8b4a1aec`. The index tree
was verified again after completion. This certifies the dirty candidate,
not a commit: 3,654 executable rows (3,403 PASS / 251 expected FAIL) and
394 negative PASS match their baselines, including allowed stage alternatives;
207 eval PASS. Eight compiled poisons were rejected, the final clean import
passed, and successful audit scratch was removed. Reconciler remains two
existing findings (C13/C5), zero HIGH. The run used 32 GiB, three Lean threads,
twelve workers and the box-wide lock. It used cached certification for slow
rows, as the review requested `--diff`; no fresh `--slow` claim is made.
See the [candidate gate](evidence/2026-09-08_i1-declarations/review-candidate-gate.txt)
and [measurements](evidence/2026-09-08_i1-declarations/review-candidate-measurements.json).
Only these documentation/evidence additions follow the validated candidate;
the clean committed-tip gate is next.
