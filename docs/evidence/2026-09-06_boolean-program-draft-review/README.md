# Draft Boolean setup/invariant bridge review

[AGENT], 2026-09-06; independent reviewer `typed-preflight`.
**Statement review PASS: no circularity or missing initialization premise
found.** The supplied draft was not compiled by the reviewer, was not public,
and was inspected during the separate renderer integration. This is not a
kernel-validation or final integrated O1 verdict.

`Program-draft.lean` preserves the exact reviewed draft. `provenance.json`
binds its original path, relevant imported contracts, current integration
revision/status and review mode. No parent source was edited.

`setup_typed` derives actual setup from A3a's independently proved setup
theorem, then takes `FunctionTyped` from stronger whole-program admission.
The actual name-coverage result yields `Covers (initialContext f) env`;
all-binding `EnvRoots` remains a separate, supplied storage fact. Together
they establish structural initial control at the real empty driver barrier.
`booleanEntry_wf` supplies the independent address/configuration bounds.
These construct all five `Inv` fields without a premise about future steps,
successful execution or an already established invariant. The theorem accepts
an arbitrary admitted argument array, not just one canonical list spelling.

`setup_typed_exact_inv` uses the stronger exact setup result to establish the
same invariant on the canonical environment, value layout and result pins.
It retains exact setup and argument arity alongside `Inv`; it does not replace
the separately exposed initialization/value equations with mere typedness.

`runProgram_typed` composes actual setup with the invariant's arbitrary-fuel,
arbitrary-choice `runConfig` success-or-fuel-out result. In its successful
branch, the actual terminal store supplies typed `loadMany`, and the result
length is linked to the selected function's declared result count. Setup's
unchanged choice stream justifies passing the same `ch` to the body. In the
other branch the actual driver returns exactly fuel exhaustion. No sufficient
fuel, termination witness, successful run, or desired final value is hidden
in the premise.

Two limits must remain clear when exposing this increment:

- `runProgramM` is the sequential driver and constructs a readout whose
  output field defaults to empty. This equality alone does not prove behavior
  of the shipped pool driver that folds output events. The later pool bridge
  must use the profile's semantic silence/absence of pool actions and connect
  actual output, scheduler and terminal behavior. The parent owns that work.
- The sequential public driver discards residual choices. Retain the existing
  `Inv.run_choices` and step/trace contracts separately; do not relabel its
  output-only result as a residual-choice correspondence theorem.

These are scope limits rather than blockers to compiling the stated bridge.
The docstring already identifies sequential execution and disclaims a
termination bound. Publishing requires successful elaboration, facade/export
integration, complete imported-declaration/poison audits and the relevant
integrated gates. Whole O1, O2, and the pool/output bridge remain distinct
completion claims. B7 may begin only after the intended setup/invariant
checkpoint actually integrates; this review does not by itself establish it.
