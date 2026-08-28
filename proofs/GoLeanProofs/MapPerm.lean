import GoLeanProofs.MapMem
import GoLeanProofs.MapLoops

/-!
# The (M) mechanism — map-order pick-family composition (W3, w3-m)

Design note: `docs/2026-08-27_m-mechanism-design.md` (LINEAGE: the
multiset-abstraction / iterate-then-canonicalize classic + the
permutation-quotient observational argument; the divergence — the
carrier is NEVER canonicalized, the quotient lives only in the spec
vocabulary and the family is threaded ∃-out/∀-in between CallSpecs —
and the quantifier-audit table live there).

The problem (the U3.1-A park blocker (M), `docs/w3-init-log.md`): Go
map-range iteration draws one pick per step, and in the confchange
`Restore`/`Simple`/`apply` chain the drawn ASSOCIATION ORDER PERSISTS
in the built maps — the composed family over the init chain is ≥10⁴
leaves that never re-converge. This module is the family carrier:

* **Layer 1 — the order-quotient readback** (pure list lemmas):
  `NodupKeys`/`lookupP` with the quotient-crossing lemma
  `lookupP_perm`, and `sortedLT_eq_of_perm` (unique sorted
  representative — the `Slice`/`VoterNodes`/`Visit`-class converging
  read). The decode transports `mapPairs_perm`/`mapPairsD_perm` (a
  permuted `mapData` reads back as a permuted abstract list) live
  TARGET-SIDE in `Specs/Raft/MapPermRead.lean` — they are stated
  over the raft reader module's decoders, and the import-direction
  lint (general ↛ Specs) is right that they do not belong here (the
  triage plan's recorded altitude smell, resolved at the landing by
  this split rather than by a lint exception).
* **Layer 2 — the value-generic machine facts**: `MapMem`'s pick-step
  family (`candidates`/`mandatory`/`pick`/`done`/`rangeStart`/
  `mapAssign`) generalized off the u64→u64 counts encoding to
  ARBITRARY map values (`toEntriesV`) — demanded by the three
  confchange/tracker value types (`struct{}`, `*tracker.Progress`,
  `bool`); keys stay uint64 (every demanding consumer is uint64-keyed;
  a string-keyed consumer generalizes the key column when it bites —
  recorded boundary).
* **Layer 3 — the composition rule**: `mapPickLoop_perm`, the
  Perm-CONSERVATION instantiation of the landed W2
  `mapPickLoop_generic`: a collect-shaped iteration drains the
  snapshot with the accumulator a PERMUTATION of the canonical image,
  ∃-packaged, at every choice stream.

Everything here is UNTRUSTED METHOD (proof-side; StepKit's banner
applies): no name below may appear in a headline statement closure.

Triage landing (2026-08-27): the CallSpec judgment family this
carrier originally threaded through was [USER]-cancelled and deleted
(archived at `archive/callspec-era`); the carrier itself is
judgment-free and lands as the soundness content of the tier-3
map-range law unit (G-MAPITER — key+value, mutation-tolerant,
demonic-order `wp_map_iter` with a Perm-of-draws readback).

Non-vacuity, layer by layer (sharpened 2026-08-27 by the pre-merge
audit, claim-dimension F1 — the earlier version of this paragraph
reported layer 3's scaffold status but was silent about layer 2,
which is in exactly the same position):

- **Layer 1** (the order-quotient readback) is LIVE: its
  quotient-crossing class is consumed in-module by the salvaged
  order-insensitive readback family (`idsFam_population`/
  `idsFam_lookup_agree`/`idsFam_sorted_collapse`, end of file).
- **Layer 2** (the value-generic machine facts) is **SCAFFOLD**:
  every consumer it was built for was a CallSpec member, and all of
  them were deleted at the triage. Seven lemmas now sit at zero
  consumers — `candidates_toEntriesV`, `mandatory_true_of_allV`,
  `stepFn_iter_doneV`, the pick-step pair `stepFn_pick_bindV`/
  `stepFn_pick_keyV`, `rangeStart_toEntriesV`, and
  `mapAssignValue_toEntriesV`. See the layer-2 section header for the
  resume condition; it is the same one layer 3 carries.
- **Layer 3** (the composition rule) is **SCAFFOLD** — see
  `mapPickLoop_perm`'s label.

Two of three layers being scaffold is not a defect to hide: the
carrier's algebra is what the triage kept, and the machine facts are
retained precisely because G-MAPITER will need them. But they are
retained on a promise, and the promise is written down at each site.
-/

namespace GoLean.MapPerm

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-! ## Layer 1 — the order-quotient readback -/

/-- Duplicate-free key column (the well-formedness a Go map's entry
list always has — `mapAssign` updates in place or appends a FRESH
key, so machine-built entry lists satisfy it by construction). -/
def NodupKeys {κ ν : Type} (es : List (κ × ν)) : Prop :=
  (es.map Prod.fst).Nodup

/-- First-match association lookup (the readers' lookup vocabulary).

Citation repaired 2026-08-27 (pre-merge audit, claim-dimension F4):
this docstring named `Invariant.lean`'s `lookupI` as the `κ = Int`
instance, but `Specs/RaftPilot/Invariant.lean` was ARCHIVED at the
triage and no `lookupI` exists in the tree. The archived original is
at `archive/callspec-era`; abstractly, the instance it named is just
`lookupP` at `κ = Int` over an id-keyed association list, which is
what the `idKV` family at the end of this file uses directly. -/
def lookupP {κ ν : Type} [DecidableEq κ] : List (κ × ν) → κ → Option ν
  | [], _ => none
  | p :: rest, t => if p.1 = t then some p.2 else lookupP rest t

theorem lookupP_eq_some_of_mem {κ ν : Type} [DecidableEq κ] :
    ∀ {es : List (κ × ν)} {k : κ} {v : ν},
      NodupKeys es → (k, v) ∈ es → lookupP es k = some v := by
  intro es
  induction es with
  | nil => intro k v _ h; cases h
  | cons p rest ih =>
      intro k v hnd hmem
      simp only [NodupKeys, List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with hp | hp
      · subst hp
        simp [lookupP]
      · have hne : p.1 ≠ k := fun hc =>
          hnd.1 (List.mem_map.mpr ⟨(k, v), hp, by simp [hc]⟩)
        simp only [lookupP, if_neg hne]
        exact ih hnd.2 hp

theorem mem_of_lookupP_eq_some {κ ν : Type} [DecidableEq κ] :
    ∀ {es : List (κ × ν)} {k : κ} {v : ν},
      lookupP es k = some v → (k, v) ∈ es := by
  intro es
  induction es with
  | nil => intro k v h; cases h
  | cons p rest ih =>
      intro k v h
      simp only [lookupP] at h
      by_cases hk : p.1 = k
      · rw [if_pos hk] at h
        injection h with h
        exact List.mem_cons.mpr (.inl (by rw [← hk, ← h]))
      · rw [if_neg hk] at h
        exact List.mem_cons.mpr (.inr (ih h))

theorem lookupP_eq_none_iff {κ ν : Type} [DecidableEq κ] :
    ∀ {es : List (κ × ν)} {k : κ},
      lookupP es k = none ↔ k ∉ es.map Prod.fst := by
  intro es
  induction es with
  | nil => intro k; simp [lookupP]
  | cons p rest ih =>
      intro k
      simp only [lookupP, List.map_cons, List.mem_cons]
      by_cases hk : p.1 = k
      · simp [hk]
      · simp only [if_neg hk, ih]
        constructor
        · intro h hc
          rcases hc with hc | hc
          · exact hk hc.symm
          · exact h hc
        · intro h hc
          exact h (.inr hc)

/-- `NodupKeys` crosses the permutation quotient. -/
theorem nodupKeys_of_perm {κ ν : Type} {es es' : List (κ × ν)}
    (hperm : List.Perm es es') (hnd : NodupKeys es) : NodupKeys es' :=
  (hperm.map Prod.fst).nodup_iff.mp hnd

/-- **THE QUOTIENT-CROSSING LEMMA**: on duplicate-free keys, lookup is
invariant under any permutation of the association list — the reason
every lookup-vocabulary postcondition transfers across the (M)
family. -/
theorem lookupP_perm {κ ν : Type} [DecidableEq κ]
    {es es' : List (κ × ν)} (hperm : List.Perm es es')
    (hnd : NodupKeys es) (k : κ) :
    lookupP es k = lookupP es' k := by
  cases h : lookupP es k with
  | some v =>
      exact (lookupP_eq_some_of_mem (nodupKeys_of_perm hperm hnd)
        (hperm.mem_iff.mp (mem_of_lookupP_eq_some h))).symm
  | none =>
      have hk := lookupP_eq_none_iff.mp h
      have hk' : k ∉ es'.map Prod.fst := fun hc =>
        hk ((hperm.map Prod.fst).mem_iff.mpr hc)
      exact (lookupP_eq_none_iff.mpr hk').symm

/-- Any indexed element heads a permutation of the erase — the
pick-step's list algebra (mirrors the machine's candidate erase). -/
theorem perm_cons_eraseIdx {α : Type} :
    ∀ {l : List α} {i : Nat} {p : α}, l[i]? = some p →
      List.Perm l (p :: l.eraseIdx i) := by
  intro l
  induction l with
  | nil => intro i p h; cases h
  | cons a t ih =>
      intro i p h
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          rw [List.eraseIdx_cons_zero]
      | succ n =>
          simp only [List.getElem?_cons_succ] at h
          rw [List.eraseIdx_cons_succ]
          exact ((ih h).cons a).trans (List.Perm.swap p a _)

/-- **Unique sorted representative** (the converging-read discharge:
`slices.Sort` after a pick-ordered collect — `MajorityConfig.Slice`,
`VoterNodes`, `Visit` — lands every family member on ONE value). -/
theorem sortedLT_eq_of_perm :
    ∀ {l l' : List Int}, List.Perm l l' →
      l.Pairwise (· < ·) → l'.Pairwise (· < ·) → l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' hperm _ _
      have hlen := hperm.length_eq
      cases l' with
      | nil => rfl
      | cons b t' => simp at hlen
  | cons a t ih =>
      intro l' hperm hs hs'
      cases l' with
      | nil =>
          have hlen := hperm.length_eq
          simp at hlen
      | cons b t' =>
          simp only [List.pairwise_cons] at hs hs'
          have hab : a = b := by
            have hamem : a ∈ b :: t' :=
              hperm.mem_iff.mp (List.mem_cons_self ..)
            have hbmem : b ∈ a :: t :=
              hperm.mem_iff.mpr (List.mem_cons_self ..)
            rcases List.mem_cons.mp hamem with h1 | h1
            · exact h1
            · rcases List.mem_cons.mp hbmem with h2 | h2
              · exact h2.symm
              · have hba := hs'.1 a h1
                have hab' := hs.1 b h2
                omega
          subst hab
          have htp := hperm.cons_inv
          rw [ih htp hs.2 hs'.2]

/-! ## Layer 2 — the value-generic machine facts

`MapMem`'s pick-step family (u64→u64 counts encoding) generalized to
arbitrary map VALUES: `toEntriesV` wraps only the keys; values ride
raw. The confchange/tracker consumers' value types — `struct{}`
(MajorityConfig/Learners), `*tracker.Progress` (ProgressMap), `bool`
(Votes) — were the demanded instances, and the ≥2 promotion bar WAS
met at birth. Keys stay uint64 (the recorded boundary; every
demanding consumer was uint64-keyed).

**SCAFFOLD (triage landing, 2026-08-27 — labeled per the witness
ruling, plan §1.4; label added by the pre-merge audit,
claim-dimension F1).** Past tense above is the point: the instances
that satisfied the promotion bar were CallSpec members, and the
triage deleted all of them. This layer is now at **zero consumers**,
so the ≥2 justification is HISTORICAL, not current — the earlier
wording ("the demanded instances (promotion ≥2 satisfied at birth)")
read as a live census and was corrected. The archived instances are
recoverable at `archive/callspec-era`.

Every lemma from here to the layer-3 header therefore carries the
same status, and the SAME resume condition as `mapPickLoop_perm`:
**a live consumer is OWED AT THE G-MAPITER UNIT** — the tier-3
map-range law (key+value, mutation-tolerant, demonic-order
`wp_map_iter` with a Perm-of-draws readback), whose soundness
argument is exactly what these machine facts feed. Retirement
condition: G-MAPITER consumes them, or G-MAPITER's design supersedes
them and they are DELETED. They are kept because a named unit will
need them, not because they build green. -/

/-- The machine encoding of a value-generic association list:
insertion-ordered `mapData` entries with wrapped-uint64 keys and raw
values. -/
def toEntriesV (kvs : List (Int × GoValue)) : Array (GoValue × GoValue) :=
  ⟨kvs.map (fun kv => (.int kv.1 .uint64, kv.2))⟩

theorem toEntriesV_getElem? (kvs : List (Int × GoValue)) (j : Nat)
    {p : Int × GoValue} (h : kvs[j]? = some p) :
    (toEntriesV kvs)[j]? = some (.int p.1 .uint64, p.2) := by
  simp [toEntriesV, List.getElem?_map, h]

theorem toEntriesV_size (kvs : List (Int × GoValue)) :
    (toEntriesV kvs).size = kvs.length := by
  simp [toEntriesV]

theorem toEntriesV_eraseIdx (kvs : List (Int × GoValue)) (i : Nat)
    (h : i < (toEntriesV kvs).size) :
    (toEntriesV kvs).eraseIdx i h = toEntriesV (kvs.eraseIdx i) := by
  apply Array.toList_inj.mp
  simp [toEntriesV, map_eraseIdx]

/-- The pick-time filter over the value-generic encoding (values are
never inspected — the filter is key-only). -/
theorem filterCandidateList_toEntriesV (σ : ExecState) (ks : List Int) :
    ∀ kvs : List (Int × GoValue),
      filterCandidateList σ (.int .uint64) (toKeys ks)
        (kvs.map (fun kv => ((.int kv.1 .uint64 : GoValue), kv.2)))
        = .ok ((kvs.filter (fun p => !ks.contains p.1)).map (fun kv =>
          ((.int kv.1 .uint64 : GoValue), kv.2))) := by
  intro kvs
  induction kvs with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [List.map_cons, filterCandidateList, keyInKeys_toKeys,
        Bind.bind, Except.bind, ih, List.filter_cons]
      by_cases hk : ks.contains k
      · have hmem : k ∈ ks := by simpa using hk
        simp [hk, hmem]
      · have hmem : k ∉ ks := by simpa using hk
        simp only [Bool.not_eq_true] at hk
        simp [hk, hmem]

private theorem snapshot_normV (types : TypeEnv) (valTy : Ty) :
    ∀ kvs : List (Int × GoValue),
    (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
      ∧ isNormalForTy types valTy p.2 = true) →
    snapshotEntriesSelfNormalizedList types (.int .uint64) valTy
      (kvs.map (fun kv => ((.int kv.1 .uint64 : GoValue), kv.2)))
      = true := by
  intro kvs
  induction kvs with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro hkv
      have hp := hkv p (by simp)
      have hrest := ih (fun q hq => hkv q (by simp [hq]))
      simp only [List.map_cons, snapshotEntriesSelfNormalizedList]
      rw [hrest, hp.2]
      simp [isNormalForTy, isNormalForTyFuel, typeResolutionFuel, hp.1]

/-- Pick-time candidates over the value-generic encoding: LOAD the
cell, filter by the produced keys, validated by normalization (the
value normal-form condition enters as the consumer-discharged
hypothesis `hkv`).

**SCAFFOLD** (layer 2; zero consumers since the triage deleted the
CallSpec members — resume: consumed at G-MAPITER, or deleted if that
unit's design supersedes it. See the layer-2 section header). -/
theorem candidates_toEntriesV {σ : ExecState} {a : Addr} {dty : Option Ty}
    {valTy : Ty} {kvs : List (Int × GoValue)} {ks : List Int}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntriesV kvs)⟩)
    (hkv : ∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
      ∧ isNormalForTy σ.types valTy p.2 = true) :
    mapIterCandidates σ (.int .uint64) valTy
      (some (.base a)) (toKeys ks)
      = .ok (toEntriesV (kvs.filter (fun p => !ks.contains p.1))) := by
  have hnorm := snapshot_normV σ.types valTy
    (kvs.filter (fun p => !ks.contains p.1))
    (fun p hp => hkv p (List.mem_filter.mp hp).1)
  have hfil := filterCandidateList_toEntriesV σ ks kvs
  simp only [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
    Bind.bind, Except.bind, pure, Except.pure]
  rw [show (toEntriesV kvs).toList = kvs.map (fun kv =>
      ((.int kv.1 .uint64 : GoValue), kv.2)) from rfl, hfil]
  simp only [snapshotEntriesSelfNormalized, List.toList_toArray, hnorm,
    if_pos]
  rfl

/-- Mandatory-remains over the value-generic encoding (value-blind). -/
theorem mandatory_toEntriesV (σ : ExecState) (ss : List Int) :
    ∀ rem : List (Int × GoValue),
      mapIterMandatoryRemains σ (.int .uint64) (toEntriesV rem) (toKeys ss)
        = .ok (rem.any (fun p => ss.contains p.1)) := by
  intro rem
  induction rem with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [mapIterMandatoryRemains, toEntriesV, List.map_cons,
        List.toList_toArray, mandatoryInList, keyInKeys_toKeys,
        Bind.bind, Except.bind, List.any_cons] at ih ⊢
      by_cases hk : ss.contains k
      · have hmem : k ∈ ss := by simpa using hk
        simp [hk, hmem]
      · have hmem : k ∉ ss := by simpa using hk
        simp only [Bool.not_eq_true] at hk
        simp [hk, hmem, ih]

/-- Nonempty candidates whose keys all sit in the start set have a
mandatory member (value-generic).

**SCAFFOLD** (layer 2; zero consumers since the triage deleted the
CallSpec members — resume: consumed at G-MAPITER, or deleted if that
unit's design supersedes it. See the layer-2 section header). -/
theorem mandatory_true_of_allV (σ : ExecState) {ss : List Int}
    {rem : List (Int × GoValue)} (hne : rem ≠ [])
    (hall : ∀ p ∈ rem, ss.contains p.1) :
    mapIterMandatoryRemains σ (.int .uint64) (toEntriesV rem) (toKeys ss)
      = .ok true := by
  rw [mandatory_toEntriesV]
  congr 1
  rw [List.any_eq_true]
  cases rem with
  | nil => exact absurd rfl hne
  | cons p rest => exact ⟨p, by simp, hall p (by simp)⟩

/-- The DONE step at any value type: no candidate remains, the frame
pops (no choice consumed — exhaustion is not a draw).

**SCAFFOLD** (layer 2; zero consumers since the triage deleted the
CallSpec members — resume: consumed at G-MAPITER, or deleted if that
unit's design supersedes it. See the layer-2 section header). -/
theorem stepFn_iter_doneV {σ : ExecState} {base : Option Loc}
    {valTy : Ty} {produced start : Array GoValue}
    {ko vo : Option String} {body : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices}
    (hcands : mapIterCandidates σ (.int .uint64) valTy
      base produced = .ok #[]) :
    stepFn σ
      (.next (.mapIterK ko vo (.int .uint64) valTy body
        base produced start env k)) ch
      = .ok (.next k, σ, ch) := by
  simp [stepFn, hcands, Bind.bind, Except.bind, pure, Except.pure]

/-- **The choice-pick step at any value type and binder shape**: the
value-generic sibling of `MapMem.stepFn_pick_bind` — candidates and
the mandatory bit are state facts supplied as premises
(`candidates_toEntriesV`/`mandatory_toEntriesV` compute them), ONE
choice of width `candidates + stop` is consumed, the picked key joins
the produced set, and the bindings/allocation are whatever
`bindIterVars` says.

**SCAFFOLD** (layer 2, the pick-step family; zero consumers since
the triage deleted the CallSpec members — resume: consumed at
G-MAPITER, or deleted if that unit's design supersedes it. See the
layer-2 section header). -/
theorem stepFn_pick_bindV {σ σ' : ExecState} {base : Option Loc}
    {valTy : Ty} {produced start : Array GoValue}
    {rem : List (Int × GoValue)} {mand : Bool}
    {idx : Nat} {ch ch' : Choices} {ko vo : Option String} {body : Stmt}
    {env env' : LocalEnv} {k : Cont} {p : Int × GoValue}
    (hcands : mapIterCandidates σ (.int .uint64) valTy
      base produced = .ok (toEntriesV rem))
    (hmand : mapIterMandatoryRemains σ (.int .uint64) (toEntriesV rem) start
      = .ok mand)
    (hconsume : Choices.consume ch
      (rem.length + (if mand then 0 else 1)) = (idx, ch'))
    (hidx : idx < rem.length)
    (hp : rem[idx]? = some p)
    (hbind : bindIterVars env.pushScope σ ko vo (.int .uint64) valTy
      (.int p.1 .uint64) p.2 = .ok (env', σ')) :
    stepFn σ
      (.next (.mapIterK ko vo (.int .uint64) valTy body
        base produced start env k)) ch
      = .ok (.exec body env'
          (.mapIterK ko vo (.int .uint64) valTy body
            base (produced.push (.int p.1 .uint64)) start env k),
        σ', ch') := by
  have hne : (toEntriesV rem).isEmpty = false := by
    cases rem with
    | nil => cases hidx
    | cons q rest => rfl
  have hsz : (toEntriesV rem).size = rem.length := toEntriesV_size rem
  have hget : (toEntriesV rem)[idx]? = some (.int p.1 .uint64, p.2) :=
    toEntriesV_getElem? rem idx hp
  simp only [stepFn, Choices.consumeAt_mapIter, hcands, Bind.bind,
    Except.bind, hne, Bool.false_eq_true, if_false, hmand]
  rw [show (if mand = true then 0 else 1) = (if mand then 0 else 1)
      from rfl]
  rw [hsz, hconsume]
  dsimp only
  split
  · rename_i hnone
    rw [hget] at hnone
    cases hnone
  · rename_i key value hsome
    rw [hget] at hsome
    injection hsome with h1
    injection h1 with hk hv2
    subst hk
    subst hv2
    simp only [hbind, pure, Except.pure]

/-- The pick at a KEY-ONLY binder (`for id := range m` — the shape of
EVERY confchange/tracker collect loop): the picked key's cell is
freshly allocated at the current `nextAddr`, the binder declared over
a pushed scope, the VALUE untouched (`bindIterVars` skips it).

**SCAFFOLD** (layer 2, the pick-step family; zero consumers since
the triage deleted the CallSpec members — "the shape of EVERY
confchange/tracker collect loop" describes the Go code, not a live
Lean consumer. Resume: consumed at G-MAPITER, or deleted if that
unit's design supersedes it. See the layer-2 section header). -/
theorem stepFn_pick_keyV {σ : ExecState} {base : Option Loc}
    {valTy : Ty} {produced start : Array GoValue}
    {rem : List (Int × GoValue)} {mand : Bool}
    {idx : Nat} {ch ch' : Choices} {kv : String} {body : Stmt}
    {env : LocalEnv} {k : Cont} {p : Int × GoValue}
    (hcands : mapIterCandidates σ (.int .uint64) valTy
      base produced = .ok (toEntriesV rem))
    (hmand : mapIterMandatoryRemains σ (.int .uint64) (toEntriesV rem) start
      = .ok mand)
    (hconsume : Choices.consume ch
      (rem.length + (if mand then 0 else 1)) = (idx, ch'))
    (hidx : idx < rem.length)
    (hp : rem[idx]? = some p)
    (hknorm : IntKind.normalize .uint64 p.1 = p.1) :
    stepFn σ
      (.next (.mapIterK (some kv) none (.int .uint64) valTy body
        base produced start env k)) ch
      = .ok (.exec body (env.pushScope.declare kv (.base ⟨σ.nextAddr⟩))
          (.mapIterK (some kv) none (.int .uint64) valTy body
            base (produced.push (.int p.1 .uint64)) start env k),
        { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some (.int .uint64), .int p.1 .uint64⟩,
            nextAddr := σ.nextAddr + 1 },
        ch') := by
  refine stepFn_pick_bindV hcands hmand hconsume hidx hp ?_
  simp only [bindIterVars, Bind.bind, Except.bind, pure, Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int p.1 .uint64)
      = .ok (.int p.1 .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hknorm]]
  simp only [Bind.bind, Except.bind, pure, Except.pure, ExecState.alloc,
    ExecState.freshLoc]

/-- The range START over the value-generic encoding: base cell +
START-KEY set (keys column only — values are read live at
production).

**SCAFFOLD** (layer 2; zero consumers since the triage deleted the
CallSpec members — resume: consumed at G-MAPITER, or deleted if that
unit's design supersedes it. See the layer-2 section header). -/
theorem rangeStart_toEntriesV {σ : ExecState} {a : Addr}
    {kvs : List (Int × GoValue)} {dty : Option Ty}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntriesV kvs)⟩) :
    mapRangeStartSets σ (.map ⟨some (.base a)⟩)
      = .ok (some (.base a), toKeys (kvs.map (·.1))) := by
  simp only [mapRangeStartSets, valueAsMap, Bind.bind,
    Except.bind, pure, Except.pure, loadLoc, hlook]
  rw [show (toEntriesV kvs).map (·.1) = toKeys (kvs.map (·.1)) from by
    simp [toEntriesV, toKeys, List.map_map, Function.comp]]

/-! ### The insert model (persistence's primitive): the value-generic
key scan and `mapAssignValue` update-or-append -/

/-- First index of key `w` (value-generic mirror of `MapMem.idxOf?`). -/
def idxOfV? : List (Int × GoValue) → Int → Option Nat
  | [], _ => none
  | (k, _) :: rest, w => if k = w then some 0 else (idxOfV? rest w).map (· + 1)

/-- Update the first occurrence, or append (the machine's
update-or-insert on the entry list, value-generic). -/
def setkV : List (Int × GoValue) → Int → GoValue → List (Int × GoValue)
  | [], w, v => [(w, v)]
  | (k, c) :: rest, w, v =>
      if k = w then (k, v) :: rest else (k, c) :: setkV rest w v

theorem idxOfV?_none_setkV {kvs : List (Int × GoValue)} {w : Int}
    (h : idxOfV? kvs w = none) (v : GoValue) :
    kvs ++ [(w, v)] = setkV kvs w v := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOfV?] at h
      by_cases hk : k = w
      · simp [hk] at h
      · simp only [if_neg hk] at h
        simp only [List.cons_append, setkV, if_neg hk]
        exact congrArg _
          (ih (by cases hidx : idxOfV? rest w <;> simp [hidx] at h ⊢))

theorem idxOfV?_some_setkV {kvs : List (Int × GoValue)} {w : Int} {j : Nat}
    (h : idxOfV? kvs w = some j) (v : GoValue) :
    kvs.set j (w, v) = setkV kvs w v := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOfV?] at h
      by_cases hk : k = w
      · simp only [if_pos hk] at h
        cases h
        simp [setkV, hk, List.set]
      · simp only [if_neg hk] at h
        cases hidx : idxOfV? rest w with
        | none => simp [hidx] at h
        | some j' =>
            simp only [hidx, Option.map_some] at h
            cases h
            simp only [List.set, setkV, if_neg hk]
            exact congrArg _ (ih hidx)

/-- A FRESH key is absent from the scan (the collect loops' case: the
target map never holds the inserted key yet). -/
theorem idxOfV?_none_of_not_mem {kvs : List (Int × GoValue)} {w : Int}
    (h : w ∉ kvs.map Prod.fst) : idxOfV? kvs w = none := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [List.map_cons, List.mem_cons] at h
      have hk : k ≠ w := fun hc => h (.inl hc.symm)
      simp only [idxOfV?, if_neg hk,
        ih (fun hc => h (.inr hc)), Option.map_none]

/-- `valueEq` at wrapped uint64 keys (private mirror of
`MapMem.valueEq_u64`). -/
private theorem valueEq_u64V (σ : ExecState) (l r : Int) :
    valueEq σ (.int .uint64) (.int l .uint64) (.int r .uint64)
      = .ok (l == r) := by
  simp [valueEq, valueEqFuel, typeResolutionFuel]

/-- The key-scan engine over the value-generic encoding (private
mirror of `MapMem.scan_generic` — the values ride untouched). -/
private theorem scan_genericV {w : Int}
    (f : GoValue × GoValue → Option (Option Nat) × Nat →
      Except GoError (ForInStep (Option (Option Nat) × Nat)))
    (hf : ∀ (k : Int) (v : GoValue) (r : Option (Option Nat) × Nat),
      f (.int k .uint64, v) r
        = .ok (if k = w then .done ⟨some (some r.snd), r.snd⟩
               else .yield ⟨none, r.snd + 1⟩)) :
    ∀ (kvs : List (Int × GoValue)) (i : Nat),
    (forIn (m := Except GoError) (toEntriesV kvs)
      (⟨none, i⟩ : Option (Option Nat) × Nat) f)
      = pure (match idxOfV? kvs w with
        | some j => ⟨some (some (j + i)), j + i⟩
        | none => ⟨none, i + kvs.length⟩) := by
  intro kvs
  induction kvs with
  | nil => intro i; simp [toEntriesV, idxOfV?]
  | cons kv rest ih =>
      intro i
      obtain ⟨k, c⟩ := kv
      simp only [toEntriesV, List.map_cons, ← Array.forIn_toList] at ih ⊢
      rw [List.forIn_cons, hf]
      by_cases hk : k = w
      · simp [hk, idxOfV?, Bind.bind, Except.bind]
      · simp only [if_neg hk, idxOfV?, Bind.bind, Except.bind]
        rw [ih (i + 1)]
        cases hidx : idxOfV? rest w with
        | none =>
            simp only [Option.map_none, List.length_cons]
            rw [show i + 1 + rest.length = i + (rest.length + 1) from by
              omega]
        | some j =>
            simp only [Option.map_some]
            rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The machine's key scan over the value-generic encoding is the
list-model first-index scan (the values ride — the scan compares keys
only). -/
theorem mapEntryIndex?_toEntriesV (σ : ExecState)
    (kvs : List (Int × GoValue)) (w : Int) (b : Bool) :
    mapEntryIndex? σ (.int .uint64) (toEntriesV kvs) (.int w .uint64) b
      = .ok (idxOfV? kvs w) := by
  unfold mapEntryIndex?
  rw [show checkKeyHashable σ (.int w .uint64) b (!(toEntriesV kvs).isEmpty)
      = .ok () from by simp [checkKeyHashable, valueHashability]]
  simp only [letFun]
  rw [scan_genericV (w := w) _ ?hf kvs 0]
  case hf =>
    intro k v r
    simp only [valueEq_u64V, Bind.bind, Except.bind]
    by_cases hk : k = w
    · simp [hk]
    · have hkb : (k == w) = false := by simpa using hk
      simp [hkb, hk]
  cases h : idxOfV? kvs w <;> simp [Bind.bind, Except.bind, pure, Except.pure]

private theorem toEntriesV_setkV {kvs : List (Int × GoValue)} {w : Int}
    {v : GoValue} :
    (match idxOfV? kvs w with
      | some i => (toEntriesV kvs).set! i (.int w .uint64, v)
      | none => (toEntriesV kvs).push (.int w .uint64, v))
      = toEntriesV (setkV kvs w v) := by
  cases hidx : idxOfV? kvs w with
  | none =>
      show (toEntriesV kvs).push _ = _
      apply Array.toList_inj.mp
      simp [toEntriesV, ← idxOfV?_none_setkV hidx v]
  | some j =>
      show (toEntriesV kvs).set! j _ = _
      apply Array.toList_inj.mp
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
        toEntriesV, ← idxOfV?_some_setkV hidx v, List.map_set]

/-- **The value-generic map-elem write** (`m[w] = v`):
`mapAssignValue`'s update-or-append on the abstract association list
is `setkV` — the PERSISTENCE PRIMITIVE (a fresh key appends at the
END, so the built order is exactly the pick order). The value's
normal form enters as the consumer-discharged store hypothesis
`hnv`.

**SCAFFOLD** (layer 2; zero consumers since the triage deleted the
CallSpec members — resume: consumed at G-MAPITER, or deleted if that
unit's design supersedes it. See the layer-2 section header). -/
theorem mapAssignValue_toEntriesV {σ : ExecState} {a : Addr}
    {valTy : Ty} {kvs : List (Int × GoValue)} {w : Int} {v : GoValue}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (toEntriesV kvs)⟩)
    (hw : IntKind.normalize .uint64 w = w)
    (hnv : normalizeValueForTy σ valTy v = .ok v) :
    mapAssignValue σ (.int .uint64) valTy
      (.map ⟨some (.base a)⟩) (.int w .uint64) v
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨none, .mapData (toEntriesV (setkV kvs w v))⟩) } := by
  simp only [mapAssignValue, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int w .uint64)
      = .ok (.int w .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hw]]
  rw [hnv]
  simp only [mapEntries, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndex?_toEntriesV]
  cases hidx : idxOfV? kvs w with
  | some j =>
      show storeLoc σ (.base a)
        (.mapData ((toEntriesV kvs).set! j (.int w .uint64, v))) = _
      rw [show (toEntriesV kvs).set! j
          ((.int w .uint64 : GoValue), v) = toEntriesV (setkV kvs w v)
          from by
        have h := toEntriesV_setkV (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
        pure, Except.pure]
  | none =>
      show storeLoc σ (.base a)
        (.mapData ((toEntriesV kvs).push (.int w .uint64, v))) = _
      rw [show (toEntriesV kvs).push
          ((.int w .uint64 : GoValue), v) = toEntriesV (setkV kvs w v)
          from by
        have h := toEntriesV_setkV (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
        pure, Except.pure]

/-! ## Layer 3 — the composition rule -/

/-- A raw tape pop's remainder is a suffix (kept local — the killed
judgment layer carried a `Choices.consume_suffix` twin, archived at
`archive/callspec-era`; [AGENT] finding, recorded in the w3-m log:
the landed `mapPickLoop_generic` does not EXPOSE the tape-suffix
discipline, so the Perm sibling below carries its own induction with
the suffix conclusion — a promotion-ledger candidate to fold back
into `MapLoops` when a second suffix-needing loop consumer bites). -/
private theorem consume_suffix' (ch : Choices) (bound : Nat) :
    (Choices.consume ch bound).2 <:+ ch := by
  cases ch with
  | nil => exact List.suffix_refl _
  | cons c rest => exact ⟨[c], rfl⟩

/-- **THE PERM-COLLECT LOOP** — the (M) mechanism's composition rule:
a collect-shaped iteration — picking `p` from the snapshot extends
the accumulator observer by exactly `g p` — drains the snapshot at
EVERY choice stream, with the final accumulator a PERMUTATION of
`acc₀ ++ rem₀.map g` (∃-packaged) and the remaining tape a suffix
(the judgment's discipline). The image `g` is pure at the OBSERVER
level (the reader-level decode, where per-iteration fresh-address
indirection cancels — design note §carrier); the machine-level heap
rides inside `δ`. Same induction as the landed W2
`mapPickLoop_generic` (one consumed choice + one erased candidate per
iteration), extended by the Perm-conservation and tape-suffix
conclusions.

**SCAFFOLD (triage landing, 2026-08-27 — labeled per the witness
ruling, plan §1.4):** this rule's sole discharge instance
(`jointConfigIDs_callSpecR`) died with the CallSpec member corpus; a
live discharge witness is OWED AT THE G-MAPITER UNIT (the tier-3
map-range law this rule's Perm algebra feeds — the mini-IDs corpus
program is its named gate instance). The prior discharge is archived
at `archive/callspec-era` (`MapOrderSpecs.lean:864`,
`jointConfigIDs_callSpecR` — the full-permutation-family member over
the real `quorum.JointConfig.IDs`). Retirement condition: the
G-MAPITER witness lands, or the unit's design supersedes this rule.
(`mapPickLoop_generic`'s own live consumers are unaffected:
`Examples/Histogram/HarnessR.lean` and
`Examples/WordCount/RangeGeneric.lean:481` — the latter is the real
second consumer; `Examples/WordFreq/Count.lean` is a re-derivation,
not a consumer.) -/
theorem mapPickLoop_perm {α β δ : Type}
    (T : δ → ExecState) (cfg : δ → List α → Config)
    (exitCfg : Config) (Q : δ → List α → Prop)
    (acc : δ → List β) (g : α → β) (c e : Nat)
    (hIter : ∀ (d : δ) (rem : List α) (idx : Nat)
      (p : α) (ch ch₂ : Choices),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p → Q d rem →
      ∃ (k : Nat) (d' : δ), k ≤ c ∧ Q d' (rem.eraseIdx idx)
        ∧ acc d' = acc d ++ [g p]
        ∧ stepFnIter k (T d) (cfg d rem) ch
            = .ok (cfg d' (rem.eraseIdx idx), T d', ch₂))
    (hExit : ∀ (d : δ) (ch : Choices), Q d [] →
      stepFnIter e (T d) (cfg d []) ch = .ok (exitCfg, T d, ch)) :
    ∀ (m : Nat) (rem : List α), rem.length = m →
    ∀ (d : δ) (ch : Choices), Q d rem →
    ∃ (k : Nat) (d' : δ) (ch' : Choices),
      k ≤ c * m + e ∧ Q d' []
      ∧ List.Perm (acc d') (acc d ++ rem.map g)
      ∧ ch' <:+ ch
      ∧ stepFnIter k (T d) (cfg d rem) ch = .ok (exitCfg, T d', ch') := by
  intro m
  induction m with
  | zero =>
      intro rem hm d ch hQ
      have hnil : rem = [] := List.eq_nil_of_length_eq_zero hm
      subst hnil
      exact ⟨e, d, ch, by omega, hQ, by simp,
        List.suffix_refl _, hExit d ch hQ⟩
  | succ m ih =>
      intro rem hm d ch hQ
      rcases hcons : Choices.consume ch rem.length with ⟨idx, ch₂⟩
      have hidx : idx < rem.length := by
        have := GoLean.MapLoops.consume_lt ch
          (show 0 < rem.length by omega)
        rw [hcons] at this
        exact this
      obtain ⟨p, hp⟩ : ∃ p, rem[idx]? = some p :=
        ⟨_, List.getElem?_eq_getElem hidx⟩
      obtain ⟨k₁, d₁, hk₁, hQ₁, hacc, hrun₁⟩ :=
        hIter d rem idx p ch ch₂ hcons hidx hp hQ
      obtain ⟨k₂, d₂, ch', hk₂, hQ₂, hperm₂, hsuf₂, hrun₂⟩ :=
        ih (rem.eraseIdx idx)
          (by rw [GoLean.MapLoops.eraseIdx_length_of_lt hidx]; omega)
          d₁ ch₂ hQ₁
      have hsuf : ch' <:+ ch := by
        refine hsuf₂.trans ?_
        have := consume_suffix' ch rem.length
        rw [hcons] at this
        exact this
      refine ⟨k₁ + k₂, d₂, ch', ?_, hQ₂, ?_, hsuf,
        stepFnIter_chain hrun₁ hrun₂⟩
      · have hms : c * (m + 1) = c * m + c := by
          rw [Nat.mul_add, Nat.mul_one]
        omega
      · -- acc d₂ ~ acc d₁ ++ erase.map g
        --        = acc d ++ [g p] ++ erase.map g
        --        ~ acc d ++ rem.map g
        rw [hacc, List.append_assoc] at hperm₂
        refine hperm₂.trans (List.Perm.append_left (acc d) ?_)
        have hmapperm : List.Perm (rem.map g)
            (g p :: (rem.eraseIdx idx).map g) := by
          have h := (perm_cons_eraseIdx hp).map g
          simpa using h
        simpa using hmapperm.symm

/-! ## The salvaged order-insensitive READBACK consumers (moved from
the killed `Specs/RaftPilot/MapOrderSpecs.lean` at the triage
landing, 2026-08-27 — the judgment-free ~100-line salvage of plan
L-3; the quotient-crossing consumer class of layer 1, in the
Base-clause reader vocabulary). -/

/-- The `struct{}{}` value (the machine's struct-lit at the empty
struct type — probe-confirmed shape). -/
def unitV : GoValue := .struct ⟨"struct{}"⟩ #[]

/-- An id list as a `map[uint64]struct{}` association list (the (M)
family's canonical spelling: the ORDER of `ids` is the family
parameter). -/
def idKV (ids : List Int) : List (Int × GoValue) :=
  ids.map (fun i => (i, unitV))

theorem idKV_keys : ∀ ids : List Int, (idKV ids).map Prod.fst = ids := by
  intro ids
  induction ids with
  | nil => rfl
  | cons a t ih => simpa [idKV] using ih

theorem idKV_filter (ids done : List Int) :
    (idKV ids).filter (fun p => !done.contains p.1)
      = idKV (ids.filter (fun i => !done.contains i)) := by
  simp [idKV, List.filter_map]
  rfl

/-- **The population readback** (the `Pair.progress`-clause shape —
"tracker population = the voter set", here at the built IDs map):
ACROSS THE WHOLE FAMILY, membership in the built map's key column is
membership in `ids`, and lookup is DEFINED at exactly the voter ids —
order-insensitively (any family member gives the same answers). -/
theorem idsFam_population {ids ids' : List Int}
    (hperm : List.Perm ids' ids) (hnd : ids.Nodup) :
    ((idKV ids').map Prod.fst = ids'
      ∧ ∀ i, i ∈ ids' ↔ i ∈ ids)
    ∧ ∀ v ∈ ids, lookupP (idKV ids') v = some unitV := by
  refine ⟨⟨idKV_keys ids', fun i => hperm.mem_iff⟩, ?_⟩
  intro v hv
  have hnd' : NodupKeys (idKV ids') := by
    show ((idKV ids').map Prod.fst).Nodup
    rw [idKV_keys]
    exact (hperm.nodup_iff).mpr hnd
  exact lookupP_eq_some_of_mem hnd'
    (List.mem_map.mpr ⟨v, hperm.mem_iff.mpr hv, rfl⟩)

/-- **The lookup-agreement readback**: any two members of the same
(M) family answer every lookup identically — the quotient-crossing
lemma consumed at a member's decode (what makes every
lookup-vocabulary invariant clause order-insensitive).

Citation repaired 2026-08-27 (pre-merge audit, claim-dimension F4):
the clause vocabulary was named `lookupI`, from the archived
`Specs/RaftPilot/Invariant.lean` (`archive/callspec-era`). The
property is stated here over `lookupP` and holds for any
first-match association lookup, which is the durable form; G-INV
re-designs the clause inventory that will consume it. -/
theorem idsFam_lookup_agree {ids l₁ l₂ : List Int}
    (h₁ : List.Perm l₁ ids) (h₂ : List.Perm l₂ ids) (hnd : ids.Nodup) :
    ∀ v, lookupP (idKV l₁) v = lookupP (idKV l₂) v := by
  intro v
  have hp : List.Perm (idKV l₁) (idKV l₂) :=
    (List.Perm.map _ (h₁.trans h₂.symm))
  have hnd₁ : NodupKeys (idKV l₁) := by
    show ((idKV l₁).map Prod.fst).Nodup
    rw [idKV_keys]
    exact h₁.nodup_iff.mpr hnd
  exact lookupP_perm hp hnd₁ v

/-- **The sorted-readback consumer** (the `VoterNodes`/`Slice`-class
converging read): sorting ANY family member's key column yields ONE
value — the whole permutation family collapses at a `slices.Sort`
boundary. -/
theorem idsFam_sorted_collapse {ids l₁ l₂ : List Int}
    (h₁ : List.Perm l₁ ids) (h₂ : List.Perm l₂ ids)
    (s₁ s₂ : List Int)
    (hs₁ : List.Perm s₁ l₁) (hs₂ : List.Perm s₂ l₂)
    (hsort₁ : s₁.Pairwise (· < ·)) (hsort₂ : s₂.Pairwise (· < ·)) :
    s₁ = s₂ :=
  sortedLT_eq_of_perm
    ((hs₁.trans h₁).trans (h₂.symm.trans hs₂.symm)) hsort₁ hsort₂

end GoLean.MapPerm
