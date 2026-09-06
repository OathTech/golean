# Independent hybrid crash-channel design review

2026-09-06; reviewer: typed-preflight. **Bounded design PASS for implementation;
production acceptance remains open.** The frozen system classifier's previous
CHANGES REQUIRED verdict (`80bf1251`) is unchanged. This review neither approves
a baseline update nor counts an observation refusal as conformance.

The design uses a distinct, owned, same-execution runtime crash file to locate
ordinary panic output. Entire raw-suffix equality now distinguishes the concrete
printed-prefix/literal pair that defeated the previous positive-stack classifier.
The stack check constrains the channel's supported report shape; it does not
authenticate arbitrary caller-supplied files. The ownership and supported-source
assumptions are explicit. No recover/defer wrapper changes the subject's panic
chain. Separate diagnostic oracle copies preserve semantic frontend inputs.

I inspected the pinned runtime implementation: SetCrashOutput duplicates the
descriptor, and writeErrData copies output only once the runtime is dying. Thus
the proposed ordinary-panic partition and the missing pre-dying fatal boundary
have concrete source explanations. The fallback counts every marker, including
LF-TAB continuations, and refuses ambiguous chains. It does not infer a panic
from expected status or from the absence of a recognized fatal frame.

Independent `probe.py` execution (`probe-2.log`, exit 0) checks nine actual Go
programs, including two race-instrumented runs. Six byte-exact panic observations
pass: the minimal printed prefix, its literal counterpart, NUL/SOH/CR/LF/TAB and
Unicode output, a printed forged positive runtime origin, a glued prefix, and
first-line payload markers with CR. Three controls explicitly refuse: a forged
init report, fatal during panic unwind, and invalid UTF8. The source and all raw
stdout/stderr/crash/acknowledgement bytes are retained in `results.json`.

The first probe attempt was a reviewer test-generation error: default Python
JSON escaping emitted surrogate escapes invalid in Go source. Its log is retained
as `probe.log`; the corrected probe emits literal Unicode. It is not an observer
failure or a conformance result. All nine final assertions passed.

## Exact prospective loss

I independently read the author's complete 40-row bounded oracle experiment and
verified that it contains exactly one refusal, saved as `prospective-refusal.json`:

- `sync/mutex-unlock-fatal/during-panic-unwind`: previous **PASS**; prospective
  **go-observation refusal**, “fatal message/output not authenticated before
  m.dying”. The registration succeeds and a crash trace exists; that trace omits
  the earlier fatal/panic bytes needed to partition program output faithfully.

My fresh native fatal-unwind control reproduces the same refusal. The remaining
39 records are the author's oracle observations, not freshly rerun Go/Lean
differentials in this review. The single loss is an honest apparatus limitation,
not a GoCore semantic regression, an accepted fatal observation, a proof of
impossibility, or an automatic exemption from the sprint's acceptance conditions.
Root must retain and reconcile this exact delta explicitly. B7 correspondence
must not silently include this observer repair as a supposedly equivalent change.

## Obligations before production acceptance

- Implement the shared checked report view once for actual-kind, message and
  output, without expected metadata selecting authentication. Retain the exact
  Go version/source-origin pin; the Python design prototype assumes the recorded
  pinned toolchain rather than itself validating a version argument.
- Validate paired files, acknowledgement content, per-draw resets, setup errors,
  and success/race paths. Successful paired observations require registration
  and an empty crash file. Empty init evidence may use strict fallback; malformed
  or unpaired evidence must refuse. These production branches are design
  obligations, not behavior established by the prototype's exit-2 function.
- Preserve stdout/stderr separation, raw bytes, sampling behavior, and exact
  semantic source copies. Compile meaningful mutations for lost output, raw
  payload selection, suffix omission, stale evidence and setup failure; reproduce
  focused actual Go/Lean outcomes and every intentional stage delta.
- The existing invalid-UTF8 representation obligation remains open. A named
  refusal is the current prototype behavior, not completion of R-1. Supported
  source must continue to exclude apparatus reconfiguration; three quarantined
  examples do not prove that boundary for arbitrary Go or a hostile filesystem.

`reviewed-sources.json` binds the inspected design, prototype, census, challenges,
source-boundary probes and three local runtime source files. `reviewed-prototype.py`
and `reviewed-design.md` preserve the reviewed candidate. `sources.sha256` seals
this report and the independent evidence. No production source was modified.
