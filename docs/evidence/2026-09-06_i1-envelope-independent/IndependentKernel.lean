import GoLean.NativeDeclarationPackage
import Lean
open GoLean.GoCore.Declaration
namespace IndependentI1Envelope
 theorem selected_signature_unique {c : Context} {id : GoLean.GoCore.FuncId}
    {a b : Signature} (ha : c.methodMatches id a = true)
    (hb : c.methodMatches id b = true) : a = b := by
  have ha' := (Context.methodMatches_exact c id a).mp ha
  have hb' := (Context.methodMatches_exact c id b).mp hb
  rw [ha'] at hb'
  exact Option.some.inj hb'
end IndependentI1Envelope
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!.getRoot == `GoLean
      | none => true
    if selected then
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do throwError "Independent I1 audit: {name} depends on {ax}"
      checked := checked + 1
  logInfo s!"Independent I1 audit PASS: {checked} declarations; classical trio only"
