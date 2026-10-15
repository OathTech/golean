import RelationalCodeX
import Joint
import U1RD8.Audit

/-! Reuse the reviewed U1 closure scan, now in the combined environment.
The separate implementation result is reported as FAIL while findings remain. -/
#eval auditRD8

open Lean in
run_elab do
  let env ← getEnv
  let names := [`Joint, `O1Compatibility, `RD8Acceptance]
  for name in names do
    unless env.header.moduleNames.contains name do throwError "Missing module {name}"
  unless env.header.moduleNames.any (fun m => m.getRoot == `GoLeanIrisExamples) do
    throwError "Missing original example modules"
  let mut count : Nat := 0
  for (n, info) in env.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i => (names ++ [`GoLeanIrisExamples]).contains env.header.moduleNames[i.toNat]!.getRoot
      | none => false
    unless ours do continue
    for ax in (← collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Non-standard axiom: {n}: {ax}"
    if info.isUnsafe || (Compiler.getImplementedBy? env n).isSome || isExtern env n then
      throwError "Implementation finding in integration adapter: {n}"
    if let .defnInfo d := info then
      if d.safety == .partial then
        match env.find? n.getPrefix with
        | some (.defnInfo parent) =>
          unless parent.safety == .safe do throwError "Partial integration declaration: {n}"
        | _ => throwError "Partial integration declaration without transparent total parent: {n}"
    count := count + 1
  logInfo m!"Joint helper audit: PASS; {count} declarations; standard axioms only"

#eval do
  checkBody ``I2.quiet_iff [``O1Compatibility.emit_projection, ``I2.reflects]
  checkBody ``I2.source_paths [``U1RD8.paths, ``I2.path_policy]
  checkBody ``I2.source_traversal [``U1RD8.traversal, ``I2.traversal_policy]
  checkBody ``I2.plan_source [``RelationalCodeX.Sweep.Plan.rec, ``I2.quiet_iff]
  checkBody ``I2.projected_source [``I2.plan_source]
  checkBody ``RD8Acceptance.agreement [``O1Compatibility.emit_projection]
  checkBody ``RD8Acceptance.prefix_history
    [``RD8Acceptance.agreement, ``RelationalCodeX.Observed.prefix_acceptance]
  checkBody ``RD8Acceptance.guarded
    [``RD8Acceptance.agreement, ``RelationalCodeX.Observed.observed_step]
  checkBody ``U1RD8.closed_guarded
    [``U1RD8.simulation, ``RelationalCodeX.Sweep.guarded_acceptance]
  checkBody ``U1RD8.simulation
    [``U1RD8.traversal, ``U1RD8.interpret, ``GoLean.GoCore.Machine.Step.unseqEnter,
      ``GoLean.Logic.Frame.defaults]
  checkBody ``U1RD8.traversal
    [``GoLean.GoCore.Relational.Unseq.Ranked.traversal, ``U1RD8.paths]
  checkBody ``U1RD8.paths
    [``GoLean.GoCore.Relational.ReadOnlyExprFor.variable,
      ``GoLean.GoCore.Relational.ReadOnlyExprFor.add_int,
      ``GoLean.GoCore.Relational.read_root,
      ``GoLean.GoCore.Relational.Unseq.ready_produced]
  checkBody ``U1RD8.interpret
    [``GoLean.GoCore.Relational.Unseq.Traversal.rec,
      ``GoLean.GoCore.Relational.Unseq.scheduler_cover,
      ``GoLean.GoCore.Relational.Unseq.binder_effect,
      ``GoLean.GoCore.Relational.Unseq.completion_path,
      ``U1RD8.path_plan, ``U1RD8.write_at]
  checkBody ``GoLean.GoCore.Relational.Unseq.Domain.all_schedules
    [``GoLean.GoCore.Relational.Unseq.Ranked.traversal,
      ``GoLean.GoCore.Relational.Unseq.Domain.occurrence]
