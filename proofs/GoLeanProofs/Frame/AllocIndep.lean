import GoLeanProofs.Frame.Transfer

/-!
# Allocator independence (the quotient corollary; user direction 2026-08-13)

Go promises NO address determinism: a conforming implementation hands
out whatever fresh addresses it likes (and moves stacks intra-run,
transparently — unobservable without `unsafe`, which the fragment
refuses). The machine keeps ONE canonical realization — the sequential
allocator (`ExecState.freshLoc` = `nextAddr`, incremented) — and this
corollary is the discharge that the choice is a QUOTIENT REPRESENTATIVE,
not a fidelity claim:

* the modeled observable surface for pointers is EQUALITY ONLY
  (`valueEqFuel`'s `.addr` arm is `Loc`-structural `==`; no pointer
  order, no hashing, no int↔ptr conversion, no `%p`-style output
  observable exists in the fragment — design note §3);
* equality is invariant under any INJECTION on addresses;
* two conforming fresh-address choices for the same run differ by
  exactly such an injection on the fresh region (`ShiftSpec` — the
  canonical sequential sequence composed with any injective relabeling;
  the design's uniform shift is one instance, `swapShift` below a
  deliberately NON-uniform one);
* so `execStmtLoop_ren` — same fuel, same choice stream, same outcome
  tag, `FrameSim`-related terminals — says every conforming address
  choice yields an OBSERVATIONALLY EQUAL execution. Stated here at the
  empty frame (`fr = []`): pure relocation, no other memory involved.

Honest scope: the quotient covers the MODELED observable fragment. A
future observation channel that exposes addresses (e.g. modeling `%p`
output, pointer order, or `unsafe` conversions) would re-open the
allocation-addressing pin; the latitude-inventory entry records this
as the re-opening condition.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- **Allocator independence**: a run under the canonical sequential
allocator transfers to the placement produced by ANY conforming
fresh-address relabeling (any `ShiftSpec` injection carried by a
`FrameSim` seed at the empty frame) — same fuel, same nondeterminism
stream, same outcome tag, terminal states related by the relabeling.
Every modeled observation (pointer equality included) is
injection-invariant, so the two executions are observationally equal. -/
theorem allocatorIndependence {ρ : Nat → Nat} {na₀ na : Nat}
    {σ σF : ExecState} (hS : FrameSim ρ na₀ na [] σ σF)
    {fuel : Nat} {c : Config} {ch ch' : Choices} {out : ExecOutcome}
    (h : execStmtLoop fuel σ c ch = .ok (out, ch')) :
    ∃ outF : ExecOutcome,
      execStmtLoop fuel σF (renameConfig ρ c) ch = .ok (outF, ch')
        ∧ OutSim ρ na₀ na [] (out, ch') (outF, ch') :=
  execStmtLoop_ren fuel hS h

/-! ## A non-uniform injection instance (the generalized-ρ witness)

The frame theorem's `ρ` is ANY injection with the fresh-region shift
law — not just the design's uniform shift (build handoff §3 finding 1).
`swapShift` witnesses the width: it permutes the two pre-existing
addresses (a relocation of the INPUT cells) while shifting the fresh
region — no `uniformShift` instance does this. -/

/-- Swap the two low addresses, shift the fresh region `[2, ∞) ≃ [na, ∞)`. -/
def swapShift (na : Nat) : Nat → Nat
  | 0 => 1
  | 1 => 0
  | x => x - 2 + na

theorem swapShift_spec {na : Nat} (h : 2 ≤ na) :
    ShiftSpec (swapShift na) 2 na := by
  constructor
  · intro x y hxy
    match x, y with
    | 0, 0 => rfl
    | 0, 1 => simp [swapShift] at hxy
    | 0, z + 2 => simp [swapShift] at hxy; omega
    | 1, 0 => simp [swapShift] at hxy
    | 1, 1 => rfl
    | 1, z + 2 => simp [swapShift] at hxy; omega
    | z + 2, 0 => simp [swapShift] at hxy; omega
    | z + 2, 1 => simp [swapShift] at hxy; omega
    | w + 2, z + 2 => simp [swapShift] at hxy; omega
  · intro k
    show swapShift na (2 + k) = na + k
    have : 2 + k = k + 2 := by omega
    rw [this]
    show k + 2 - 2 + na = na + k
    omega

/-- The non-uniform witness is genuinely outside the uniform family:
no `uniformShift na₀ na'` equals `swapShift na` (they differ at 0 or 1). -/
theorem swapShift_not_uniform (na na₀ na' : Nat) :
    swapShift na ≠ uniformShift na₀ na' := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [swapShift, uniformShift] at h0 h1
  split at h0 <;> split at h1 <;> omega

end GoLean.Frame
