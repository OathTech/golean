import Derivation
import SemanticLinks
import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

/-! Check every declaration belonging to the experiment and its imported
GoLean modules, including private/generated declarations. Toolchain modules
are the pinned trust base. Kernel replay is a separate command. -/
open Lean

def reviewRenderers : CoreM Unit := do
  let env ← getEnv
  let modules := env.header.moduleNames
  let ours := modules.map fun m => [`GoLean, `Derivation, `SemanticLinks].contains m.getRoot
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
    if [`GoLean, `Derivation, `SemanticLinks].contains m.getRoot then
      logInfo m!"REPLAY_MODULE {m}"
  logInfo "REPLAY_MODULE ReviewAudit"
  logInfo m!"Renderer axiom audit: PASS; {count} declarations; standard axioms only"
  logInfo m!"Compiler inventory: {totalImplementations} generated partial implementations have transparent total kernel definitions"
  if findings > 0 then
    logInfo m!"Trust implementation scan: FAIL; {findings} findings above (not waived)"
  else
    logInfo "Trust implementation scan: PASS"


#eval reviewRenderers
#print axioms GoLean.GoCore.Ty.reprPrec_eq_render

#print axioms GoLean.GoCore.Ty.repr_eq_render

#print axioms GoLean.GoValue.reprPrec_eq_render

#print axioms GoLean.GoValue.repr_eq_render

#print axioms GoLean.GoCore.Expr.reprPrec_eq_render

#print axioms GoLean.GoCore.Expr.repr_eq_render

#print axioms GoLean.RendererDerivation.ty_equation

#print axioms GoLean.RendererDerivation.govalue_equation

#print axioms GoLean.RendererDerivation.expr_equation

#print axioms GoLean.RendererLinks.dynamic_type_refusal

#print axioms GoLean.RendererLinks.valueEq_bool_unit

#print axioms GoLean.RendererLinks.preprint_unboxed

#print axioms GoLean.RendererLinks.unseq_nonatom
