import Tests.UnseqHarness

/-! A fresh negative control through the existing actual pool drivers. This
uses invocation and an aliased write, deliberately outside the deterministic
expression-only U1 domain. Enumeration is confined to this negative control;
it is not the proof of the general sequentialization theorem. -/
namespace U1.AliasControl
open GoLean GoCore GoCore.Machine Tests.UnseqScheduler

def mutation : Func := {
  id := ⟨"mutateAlias"⟩, args := #[⟨0, .pointer .int⟩], results := #[⟨1,.int⟩]
  body := .seqn #[.assign (.addr (.var 0)) (.intLit 7),
    .assign (.var 1) (.intLit 0)] }

def graph : UnseqGraph := {
  cells := [⟨3,.int⟩,⟨4,.int⟩,⟨5,.int⟩]
  occs := [⟨"writeAlias", .invoke [3] (.var 2) [], [], none⟩,
    ⟨"readAlias", .eval 4 (.var 1), [], none⟩,
    ⟨"dependentSum", .eval 5 (.add (.var 3) (.var 4)), [], none⟩,
    ⟨"resultTarget", .target 6 (.var 0), [], none⟩]
  stores := [(6,5)] }

def program : Program := { funcs := #[{
  id := ⟨"aliasMain"⟩, args := #[], results := #[⟨0,.int⟩]
  body := .block #[⟨1,.int⟩,⟨2,.funcType [.pointer .int] [.int] false⟩]
    #[.assign (.var 1) (.intLit (-2)),
      .assign (.var 2) (.funcVal ⟨"mutateAlias"⟩ #[.ref 1]),
      .unseq graph (.seqn #[])] }, mutation] }

def check : IO Unit := do
  let a ← expectSet "U1 fresh alias: real schedules retain {-2,7}"
    program "aliasMain" [okZ (-2),okZ 7]
  let b ← expectDedupSet "U1 fresh alias: checked behavior-set certificate"
    program "aliasMain" [okZ (-2),okZ 7]
  unless a && b do throw (IO.userError "U1 alias control failed")

end U1.AliasControl

def main := U1.AliasControl.check
