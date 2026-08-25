import GoLeanProofs.Specs.Raft.NativeS23Chain

/-! # C4 — the non-vacuity witness for the S2/S3 ghost-history chain
(scoping lane `campaign-arc4b`, unit C4, 2026-08-27; the
witness-in-same-slice lane convention — C3's lesson (a), now
binding.)

A concrete six-step T1-shaped run — the twin's deliver-loop shape
at `ldr = 1`, `tm = 2` (the S1 chain's output instantiated): noop
propose, command propose, leader commit to 3, follower 2 accepts
the slice with commit advance, both nodes apply their windows —
discharging EVERY `HStep` premise by computation (each `hwin`/
`hok`/`hk` a closed instance of the quoted obligation members), and
driving the S2/S3 leaves end-to-end: `wNoViol` applies `s23_leaf`
with the delta Props themselves as the minimal checker-interface
instantiation, and the sanity theorems show the final net REALLY
applied entries (the leaf is not vacuous over it).

The `certified` parameter is instantiated `fun _ => True` — the
witness exercises the O-C2 seam's SHAPE, not its content (the
match-evidence concretization is the S2-wave's, per the chain
module's scope note). -/

namespace GoLean.RaftSeam.NativeSpec

def wCert : Nat → Prop := fun _ => True

/-- The boot hist: the seeded snapshot entry (twin-lib.go:198-202). -/
def wH0 : Hist := [(1, 1, 0)]

/-- The boot node: snapshot applied, nothing else. -/
def whnode : HNode :=
  { log := wH0, committed := 1, applied := 1, appliedLog := wH0 }

def wM0 : HNet := { hist := wH0, node := fun _ => whnode }

/-- Steps 1-2: the leader's noop and one command proposal (each net
is the constructor's target expression verbatim, so the step
theorems are bare constructor applications). -/
def wM1 : HNet :=
  updHNode wM0 1
    { wM0.node 1 with
        log := (wM0.node 1).log ++ [(wM0.hist.length + 1, 2, 0)] }
    (wM0.hist ++ [(wM0.hist.length + 1, 2, 0)])

def wM2 : HNet :=
  updHNode wM1 1
    { wM1.node 1 with
        log := (wM1.node 1).log ++ [(wM1.hist.length + 1, 2, 7)] }
    (wM1.hist ++ [(wM1.hist.length + 1, 2, 7)])

/-- Step 3: leader commits to 3. -/
def wM3 : HNet :=
  updHNode wM2 1 { wM2.node 1 with committed := 3 } wM2.hist

/-- Step 4: follower 2 accepts the slice (k = 3), commit to 3. -/
def wM4 : HNet :=
  updHNode wM3 2
    { wM3.node 2 with
        log := wM3.hist.take (max (wM3.node 2).log.length 3),
        committed := 3 }
    wM3.hist

/-- Steps 5-6: nodes 1 and 2 apply their committed windows. -/
def wM5 : HNet :=
  updHNode wM4 1
    { wM4.node 1 with
        applied := 3,
        appliedLog := (wM4.node 1).appliedLog ++
          (((wM4.node 1).log.drop (wM4.node 1).applied).take
            (3 - (wM4.node 1).applied)) }
    wM4.hist

def wM6 : HNet :=
  updHNode wM5 2
    { wM5.node 2 with
        applied := 3,
        appliedLog := (wM5.node 2).appliedLog ++
          (((wM5.node 2).log.drop (wM5.node 2).applied).take
            (3 - (wM5.node 2).applied)) }
    wM5.hist

-- Landing rename (C2c slice 0): `wStep1`–`wStep4` collided with
-- `NativeS1Witness`'s same-namespace theorems under JOINT import into the
-- aggregator (each lane module was verified green STANDALONE only); the
-- H-chain steps are `wHStep*` since the landing. Statements unchanged.
theorem wHStep1 : HStep 1 2 wCert wM0 wM1 := .propose wM0 0
theorem wHStep2 : HStep 1 2 wCert wM1 wM2 := .propose wM1 7
theorem wHStep3 : HStep 1 2 wCert wM2 wM3 :=
  .leaderCommit wM2 3 ⟨by decide, by decide⟩ ⟨by decide, Or.inr trivial⟩
theorem wHStep4 : HStep 1 2 wCert wM3 wM4 :=
  .deliverAppend wM3 2 3 3 3 (by decide) ⟨by decide, by decide⟩
theorem wHStep5 : HStep 1 2 wCert wM4 wM5 :=
  .applyStep wM4 1 3 ⟨by decide, by decide⟩
theorem wHStep6 : HStep 1 2 wCert wM5 wM6 :=
  .applyStep wM5 2 3 ⟨by decide, by decide⟩

/-- The whole run. -/
theorem wRun : Star (HStep 1 2 wCert) wM0 wM6 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.refl _) wHStep1)
    wHStep2) wHStep3) wHStep4) wHStep5) wHStep6

/-- The seed satisfies the chain invariant (every field computed on
the boot data). -/
theorem wSeedInv : HistInv 1 2 wM0 where
  histIdx := by
    intro k e hk
    match k with
    | 0 =>
      have he : (1, 1, 0) = e := Option.some.inj hk
      rw [← he]
    | k + 1 => exact nomatch hk
  histTermMono := by
    intro k k' e e' hkk hk hk'
    match k, k' with
    | 0, 0 =>
      have he : (1, 1, 0) = e := Option.some.inj hk
      have he' : (1, 1, 0) = e' := Option.some.inj hk'
      rw [← he, ← he']
      exact Nat.le_refl _
    | 0, k' + 1 => exact nomatch hk'
    | k + 1, _ => exact nomatch hk
  histTermsLe := by decide
  leaderLog := rfl
  logsPrefix := fun _ => ⟨1, rfl⟩
  commitWindow := fun _ => by
    show whnode.committed ≤ whnode.log.length; decide
  applyWindow := fun _ => by
    show whnode.applied ≤ whnode.committed; decide
  appliedTake := fun _ => rfl

/-! ## The witnesses -/

/-- Sanity: the run REALLY applied the full history at both nodes —
the leaf below is not vacuous over this net. -/
theorem wApplied :
    (wM6.node 1).appliedLog = [(1, 1, 0), (2, 2, 0), (3, 2, 7)] ∧
    (wM6.node 2).appliedLog = [(1, 1, 0), (2, 2, 0), (3, 2, 7)] := by
  constructor <;> rfl

/-- The chain invariant transported to the final net (the
preservation induction computed on a real run). -/
theorem wFinalInv : HistInv 1 2 wM6 := histInv_reachable wSeedInv wRun

/-- The S2/S3 deltas over the final net, verbatim the interface's
soundness shapes (so `id` is the minimal checker-side instance). -/
def wViolS2 : Prop :=
  ∃ i j e e', e ∈ (wM6.node i).appliedLog ∧
    e' ∈ (wM6.node j).appliedLog ∧ e.1 = e'.1 ∧ e ≠ e'

def wViolS3 : Prop :=
  ∃ i p q : Nat, ∃ ep eq : Nat × Nat × Nat, p < q ∧
    (wM6.node i).appliedLog[p]? = some ep ∧
    (wM6.node i).appliedLog[q]? = some eq ∧
    (eq.1 ≤ ep.1 ∨ eq.2.1 < ep.2.1)

/-- **THE C4 WITNESS** — the S2/S3 leaf end-to-end on the concrete
run: every premise discharged, the interface instantiated at its
minimal (delta-Prop) form, both checks silent. -/
theorem wNoViol : ¬ wViolS2 ∧ ¬ wViolS3 :=
  s23_leaf wSeedInv wRun ⟨id, id⟩

end GoLean.RaftSeam.NativeSpec
