import RelationalCodeX
import CallerAcceptance
import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

/-! Check every declaration belonging to the experiment and its imported
GoLean modules, including private/generated declarations. Toolchain modules
are the pinned trust base. Kernel replay is a separate command. -/
open Lean

def auditPhases : CoreM Unit := do
  let env ← getEnv
  let modules := env.header.moduleNames
  let ours := modules.map fun m => [`GoLean, `GoLeanIris, `GoLeanIrisExamples, `RelationalCodeX, `PhaseAcceptance, `CallerAcceptance].contains m.getRoot
  let mut count : Nat := 0
  let mut findings : Nat := 0
  let mut totalImplementations : Nat := 0
  for (name, info) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => ours[i.toNat]!
      | none => true
    unless selected do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom: {name} depends on {ax}"
    if info.isUnsafe then
      logInfo m!"TRUST FINDING: unsafe declaration {name}"
      findings := findings + 1
    if let .defnInfo d := info then
      if d.safety == .partial then
        -- Lean also generates these compiler implementations for transparent,
        -- total definitions (including `certify`). They are not new opaque
        -- mathematical definitions. Report that inventory separately.
        match env.find? name.getPrefix with
        | some (.defnInfo parent) =>
          if parent.safety == .safe then
            totalImplementations := totalImplementations + 1
          else
            logInfo m!"TRUST FINDING: partial declaration {name}"
            findings := findings + 1
        | _ =>
          logInfo m!"TRUST FINDING: partial implementation without transparent total parent: {name}"
          findings := findings + 1
    if (Compiler.getImplementedBy? env name).isSome then
      logInfo m!"TRUST FINDING: implemented_by {name}"
      findings := findings + 1
    if isExtern env name then
      logInfo m!"TRUST FINDING: extern {name}"
      findings := findings + 1
    count := count + 1
  for m in modules do
    if [`GoLean, `GoLeanIris, `GoLeanIrisExamples, `RelationalCodeX, `PhaseAcceptance, `CallerAcceptance].contains m.getRoot then
      logInfo m!"REPLAY_MODULE {m}"
  logInfo "REPLAY_MODULE PhaseAudit"
  logInfo m!"Observed phase axiom audit: PASS; {count} declarations; standard axioms only"
  logInfo m!"Compiler inventory: {totalImplementations} generated partial implementations have transparent total kernel definitions"
  if findings > 0 then
    logInfo m!"Trust implementation scan: FAIL; {findings} findings above (not waived)"
  else
    logInfo "Trust implementation scan: PASS"


#eval auditPhases
#print axioms GoLean.GoCore.Relational.StoreEffectFor.forget
#print axioms GoLean.GoCore.Relational.OrderedWritesFor.forget
#print axioms GoLean.GoCore.Relational.OperandPathsFor.forget
#print axioms GoLean.GoCore.Relational.Observed.StorePath.weaken
#print axioms GoLean.GoCore.Relational.Observed.ReadOnlyExpr.variable
#print axioms GoLean.GoCore.Relational.Observed.ReadOnlyExpr.reference
#print axioms GoLean.GoCore.Relational.Observed.ReadOnlyExpr.add_int
#print axioms GoLean.GoCore.Relational.Observed.variable_assignment_phases
#print axioms GoLean.GoCore.Relational.Observed.pointer_rhs_phases
#print axioms GoLean.GoCore.Relational.Observed.variable_expression_phases
#print axioms GoLean.GoCore.Relational.Observed.SavedCaller.entry_phases
#print axioms GoLean.GoCore.Relational.Observed.CallBoundary.delivery_phases
#print axioms PhaseAcceptance.path
#print axioms PhaseAcceptance.effect
#print axioms PhaseAcceptance.writes
#print axioms PhaseAcceptance.assignment
#print axioms PhaseAcceptance.entry
#print axioms PhaseAcceptance.delivery
#print axioms PhaseAcceptance.callee
#print axioms PhaseAcceptance.caller
#print axioms PhaseAcceptance.hist_code
#print axioms PhaseAcceptance.adequate
#print axioms PhaseAcceptance.caller_prefix
#print axioms PhaseAcceptance.outcomes

/-- The established visited-set proof-value traversal, with positive and
negative edges. Types alone do not establish operational proof reuse. -/
def proofClosure (root : Name) : CoreM NameSet := do
  let env ← getEnv
  unless env.contains root do throwError "Missing root {root}"
  let mut seen : NameSet := {}
  let mut pending := [root]
  repeat
    match pending with
    | [] => break
    | n :: rest =>
      pending := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some info := env.find? n | throwError "Missing dependency {n}"
      if let some value := info.value? (allowOpaque := true) then
        pending := value.getUsedConstants.toList ++ pending
  return seen

def checkDependencies (root : Name) (present absent : List Name) : CoreM Unit := do
  let env ← getEnv
  let closure ← proofClosure root
  for n in present ++ absent do
    unless env.contains n do throwError "Missing endpoint {n}"
  for n in present do
    unless closure.contains n do throwError "Missing proof dependency {root} -> {n}"
  for n in absent do
    if closure.contains n then throwError "Unexpected proof dependency {root} -> {n}"
  logInfo m!"PROOF_CLOSURE {root}: required {present}; excluded {absent}"

#eval do
  checkDependencies ``PhaseAcceptance.assignment
    [``GoLean.GoCore.Relational.Observed.variable_assignment_phases,
     ``GoLean.GoCore.Relational.read_variable] []
  checkDependencies ``PhaseAcceptance.entry
    [``GoLean.GoCore.Relational.Observed.SavedCaller.entry_phases,
     ``GoLean.GoCore.Relational.ReadOnlyExprFor.variable] []
  checkDependencies ``PhaseAcceptance.delivery
    [``GoLean.GoCore.Relational.Observed.CallBoundary.delivery_phases,
     ``GoLean.GoCore.Relational.Boundary.Returns.intro] []
  checkDependencies ``PhaseAcceptance.callee
    [``PhaseAcceptance.assignment, ``RelationalCodeX.Observed.wp_variable_assignment] []
  checkDependencies ``PhaseAcceptance.caller
    [``PhaseAcceptance.entry, ``PhaseAcceptance.delivery,
     ``RelationalCodeX.Observed.call_rule_value, ``RD8Acceptance.guarded,
     ``GoLean.Logic.Frame.roots_valid]
    [``RelationalCodeX.ObservedCaller.identity_body,
     ``RelationalCodeX.ObservedCaller.callee_acceptance]
  checkDependencies ``PhaseAcceptance.hist_code
    [``RelationalCodeX.ObservedCaller.caller_acceptance,
     ``RelationalCodeX.ObservedCaller.callee_acceptance] []
  checkDependencies ``PhaseAcceptance.adequate
    [``PhaseAcceptance.assignment, ``PhaseAcceptance.entry, ``PhaseAcceptance.delivery,
     ``GoLean.Logic.ProgramExecution.observed_entry_adequacy] []
  checkDependencies ``PhaseAcceptance.caller_prefix
    [``GoLean.Logic.ProgramExecution.closed_program_prefix] []
  checkDependencies ``PhaseAcceptance.outcomes
    [``GoLean.Logic.ProgramExecution.closed_program_outcomes_hist] []
