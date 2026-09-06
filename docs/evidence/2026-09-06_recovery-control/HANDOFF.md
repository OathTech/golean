# Recovery control checkpoint

- Base: reviewed actual setup `63769964`; fifteen new semantic control/proof
  modules plus two test/audit modules. See `source.sha256` and contract note.
- Dedicated gate PASS, ordinary CI PASS exit 0, independent bounded review
  PASS `9e6c4234` + reproducibility packaging `ba930ba2`. All inputs frozen
  throughout the final gate, CI and review. No main merge/push performed.
- Public core API: `RecoveryRuntime.setup_inv`, `control_stepFn`,
  `control_step`, `Inv.step`, `Inv.steps`, `Inv.iter`, `Inv.progress`,
  `Inv.reachable_progress`, `Inv.readout`, `Inv.loop_readout`,
  `Inv.run_readout`, `Inv.loop_choices`, `Inv.run_choices`,
  `Inv.reachable_silent`.
- Progress separately classifies normal terminal, nonempty semantic abort,
  and a relational successor. The grammar additionally requires a real
  caller continuation for nonempty frame writeback; synthetic violations
  are rejected by kernel tests. No successful-execution premise defines
  admission or the invariant.
- Parent owns facade promotion, observer/renderer integration and broader
  sprint integration. The string-renderer lane is preparing total explicit
  boxed-string `abortMsg` contracts; use these to close actual driver
  terminal/fuel/no-refusal classification without narrowing admission.
- Next customer slice needs generic multi-cell Iris allocation, exact
  ordinary/deferred call layout and shared continuation-sensitive call/
  recover/unwind rules. Keep one owned Boolean pointee through aliased
  captured slots. Refactor A2 and prove the independent Shared fixture's
  normal/recovered functional results through the same rules and actual
  setup/readout/pool contracts.
- Unreviewed next-slice prototype is retained only in ignored scratch
  `/home/dev/projects/golean/.tmp/recovery-iris-layout.sJAuGN/CallLayout.lean`.
  Its `enterFrame_layout`/`enterFramePick_layout` compiles and reuses reviewed
  exact bind/allocate/pin lemmas. It is excluded from this commit and review.
