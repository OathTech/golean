import Concurrency.Constraints
import Lean

namespace Concurrency
open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- A disposable finite-prefix certificate generator, not a transition
relation. It calls the existing step and detector and refuses every terminal
front (including exit windows). Its theorem produces the existing PoolPrefix. -/
def live (ctx : ProgramCtx) (m : MultiConfig) : Bool :=
  m.panicMsg?.isNone && m.mainOutcome?.isNone &&
    !(runnableIdxs ctx m.shared m.threads).isEmpty

abbrev Certificate := List DriverEvent × MultiConfig × RaceState × Choices

def certify (ctx : ProgramCtx) : Nat → MultiConfig → RaceState → Choices → Except Stop Certificate
  | 0, m, r, ch => .ok ([], m, r, ch)
  | n + 1, m, r, ch => do
      if !live ctx m then throw (.internal "certificate requires a live nonterminal front")
      let (m', ch', ev) ← stepMulti ctx m ch
      let r' ← raceUpdate ev m' r
      let (events, mf, rf, tail) ← certify ctx n m' r' ch'
      return (⟨[], ev⟩ :: events, mf, rf, tail)

theorem live_continue {ctx : ProgramCtx} {m : MultiConfig} (h : live ctx m = true)
    (ch : Choices) : Continue ctx m ch ch [] := by
  simp only [live, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
    List.isEmpty_eq_false_iff] at h
  exact .running h.1.1 h.1.2 h.2

theorem certify_sound {ctx : ProgramCtx} {n : Nat} {m mf : MultiConfig}
    {r rf : RaceState} {ch tail : Choices} {events : List DriverEvent}
    (h : certify ctx n m r ch = .ok (events, mf, rf, tail)) :
    PoolPrefix ctx n m r ch events mf rf tail := by
  induction n generalizing m r ch events with
  | zero =>
    simp only [certify, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact .done
  | succ n ih =>
    cases hl : live ctx m <;> simp only [certify, hl, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    case false => contradiction
    case true =>
      cases hs : stepMulti ctx m ch with
      | error e => simp [hs] at h
      | ok result =>
        rcases result with ⟨m', ch', ev⟩
        cases hr : raceUpdate ev m' r with
        | error e => simp [hs, hr] at h
        | ok r' =>
          cases ht : certify ctx n m' r' ch' with
          | error e => simp [hs, hr, ht] at h
          | ok result =>
            rcases result with ⟨es, mf', rf', tail'⟩
            simp only [hs, hr, ht, Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            exact .step (live_continue hl ch) hs hr (ih ht)

open Lean Elab Term Meta in
/-- Normalize witness data at elaboration time, refusing errors. The acceptance
theorem separately checks the certificate equation through the kernel. -/
elab "sample% " source:term : term => do
  let e ← elabTerm source none
  let reduced ← Lean.Meta.Tactic.Cbv.cbvEntry e
  let result := match reduced with
    | .rfl .. => e
    | .step e' _ _ _ => e'
  unless result.isAppOfArity ``Except.ok 3 do
    throwError "prefix certificate did not succeed: {result}"
  return result.getAppArgs[2]!

end Concurrency
