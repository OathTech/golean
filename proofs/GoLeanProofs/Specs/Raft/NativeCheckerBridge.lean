import GoLeanProofs.Specs.Raft.NativeS1CheckerLeaf
import GoLeanProofs.Specs.Raft.NativeS23Chain
import GoLeanProofs.Specs.TwinProgram
import GoLean.GoCore.SyntaxEqb
import GoLeanProofs.Sym.KernelRfl

/-! # A4-U23 — the checker-interface I2 bridges (S1 + S2/S3)

The interpreter-side halves the arc4b lane left as interface premises
(`S1CheckerInterface`, C3; `S23CheckerInterface`, C4), built in three
layers, each honest about what it does and does not close:

1. **The checker FOLD MODELS** (`s1Step`/`s1Run`, `s23Step`/`s23Run`)
   — the S1 record block (twin-lib.go:266-280) and the `apply` S2/S3
   checks (twin-lib.go:298-335), transcribed branch-for-branch:
   S1 = claims++, leaderOf lookup, viol on `ok && prev != nd.id`,
   overwrite-insert; S2/S3 = the two monotonicity guards against the
   per-node cursors (each counted separately, as the code counts),
   cursor update, the empty-data early return, the byIndex
   first-insert and disagreement guard. The S3 ANOMALY sub-check
   (EntryNormal typing) is OUT per the C4 scope note — the abstract
   vocabulary has no entry-type field; its correspondence rides the
   residual span proof below.
2. **The BRIDGE THEOREMS** (`s1_viol_delta`, `s23_viol_delta`) — a
   firing of the fold's violation counter IS a delta in exactly the
   interface's shape: the leaderOf-disagreement predicate over the
   claims (S1), the cross-node applied-record disagreement and the
   per-node positional monotonicity break (S2/S3). These discharge
   the interfaces' predicate halves COMPLETELY at the model level:
   `s1_interface_of_trace` instantiates `S1CheckerInterface` given
   only the `ClaimTrace` premise (the run-correspondence half — the
   T1 assembly's seam, NOT this unit's); `s23_interface_of_run`
   instantiates `S23CheckerInterface` given only the appliedLog
   projection (`hlog` — the ENode↔HNode log-convention projection the
   C4 module names as I2's absTwinRead concern) plus positive indexes
   (DERIVED from `HistInv` in the composed corollary). The composed
   corollaries (`s1_model_silent`, `s23_model_silent`) run the arc4b
   leaves end-to-end: the model checker is SILENT on conforming runs.
3. **The SHAPE PINS** — the model's guard vocabulary is EXACTLY the
   pinned lowering's: the four violation guards (S3 idx/term, S2
   disagreement, S1 disagreement) occur verbatim among the if-guards
   of `main.twin.apply` / `main.twin.harvest` (collected recursively,
   compared by the sound `Expr.eqbF` — the DriverNet shape-pin
   pattern). A frontend re-lowering that reshapes a guard turns the
   pin red.

**THE HONEST RESIDUAL (stated bluntly):** the span-computes-model
theorem — that the interpreter walking the checker's spans performs
exactly `s1Step`/`s23Step` on the absState projection, for SYMBOLIC
checker state — is NOT here. It needs DriverNet-grade compositional
span lemmas over the apply/record spans, whose viol branches build
strings through `utoa` (a data-dependent digit loop with no kit lemma
yet); ~1 unit at U20's measured rate, priced in the log. What stands
in its place today: the guards pinned verbatim (layer 3). (Triage
hygiene 2026-08-27, P-2: the round-run kernel checks cited here —
`RoundMaLemma`/`RoundVoteLemma`, violations 0 → 0 readouts at real
fixtures — were fixed-trajectory-era modules, W0-killed and archived
at `archive/fixed-trajectory-era`; the cond-loop kit lemma the viol
branches' `utoa` needed has since landed as `CondFor.condFor_loop`.)

LINEAGE: assume-guarantee interface decomposition (the C3/C4
pattern's other half); the fold models are ghost-state abstractions
of straight-line code (auxiliary-variable refinement); the bridges
are Floyd-style invariant inductions over the fold. -/

namespace GoLean.RaftSeam.NativeSpec

/-! ## 1. The S1 checker fold (twin-lib.go:266-280) -/

/-- The S1 checker state: `leaderOf` as a newest-first assoc list
(cons + first-match lookup = Go's map overwrite), the two counters. -/
structure S1St where
  leaderOf : List (Nat × Nat)
  claims   : Nat
  viols    : Nat
  deriving Repr, DecidableEq

def lookupTerm : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (t, l) :: rest, t' => if t = t' then some l else lookupTerm rest t'

/-- `ok && prev != nd.id` — the S1 violation guard, verbatim
(pinned below). -/
def s1Fires (st : S1St) (ev : Nat × Nat) : Bool :=
  match lookupTerm st.leaderOf ev.1 with
  | some prev => decide (prev ≠ ev.2)
  | none => false

/-- One S1 record step: `t.claims++`; viol on disagreement;
`t.leaderOf[nd.term] = nd.id`. -/
def s1Step (st : S1St) (ev : Nat × Nat) : S1St :=
  { leaderOf := ev :: st.leaderOf,
    claims := st.claims + 1,
    viols := st.viols + (if s1Fires st ev then 1 else 0) }

/-- The fold over a run's claim events, from the zero state. -/
def s1Run (events : List (Nat × Nat)) : S1St :=
  events.foldl s1Step ⟨[], 0, 0⟩

theorem lookupTerm_mem {lst : List (Nat × Nat)} {t v : Nat}
    (h : lookupTerm lst t = some v) : (t, v) ∈ lst := by
  induction lst with
  | nil => cases h
  | cons p rest ih =>
    obtain ⟨pt, pl⟩ := p
    unfold lookupTerm at h
    by_cases ht : pt = t
    · rw [if_pos ht] at h
      obtain rfl := Option.some.inj h
      subst ht
      exact List.mem_cons_self ..
    · rw [if_neg ht] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- The S1 bridge induction: relative to a fixed full event list `F`,
a fold whose map entries and remaining events all come from `F` fires
only on an `S1Delta F`. -/
theorem s1_bridge_aux (F : List (Nat × Nat)) :
    ∀ (evs : List (Nat × Nat)) (st : S1St),
      (∀ p ∈ st.leaderOf, p ∈ F) → (∀ e ∈ evs, e ∈ F) →
      (0 < st.viols → S1Delta F) →
      0 < (evs.foldl s1Step st).viols → S1Delta F := by
  intro evs
  induction evs with
  | nil => intro st _ _ hv h; exact hv h
  | cons e rest ih =>
    intro st hm he hv h
    simp only [List.foldl_cons] at h
    refine ih (s1Step st e) ?_ ?_ ?_ h
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact he p (List.mem_cons_self ..)
      · exact hm p hp'
    · intro x hx; exact he x (List.mem_cons_of_mem _ hx)
    · intro hpos
      by_cases hf : s1Fires st e
      · -- the fire IS the delta
        unfold s1Fires at hf
        cases hl : lookupTerm st.leaderOf e.1 with
        | none => rw [hl] at hf; cases hf
        | some prev =>
          rw [hl] at hf
          have hne : prev ≠ e.2 := of_decide_eq_true hf
          exact ⟨e.1, prev, e.2, hm _ (lookupTerm_mem hl),
            he e (List.mem_cons_self ..), hne⟩
      · -- no fire: the counter did not move
        have : 0 < st.viols := by
          simp only [s1Step, hf] at hpos
          exact hpos
        exact hv this

/-- **THE S1 BRIDGE**: the fold's violation counter fires only on a
leaderOf-disagreement delta of the events — the interface's
`violationImpliesDelta`, proved about the checker model. -/
theorem s1_viol_delta (events : List (Nat × Nat)) :
    0 < (s1Run events).viols → S1Delta events :=
  s1_bridge_aux events events ⟨[], 0, 0⟩
    (fun _ hp => absurd hp (List.not_mem_nil))
    (fun _ h => h) (fun h => absurd h (Nat.lt_irrefl 0))

/-- **The I2 instantiation of `S1CheckerInterface`** at the model
checker's violation flag: the ONLY remaining premise is `ClaimTrace`
— the run-correspondence half (the T1 assembly's seam; module
docstring). The predicate half is `s1_viol_delta`, closed. -/
theorem s1_interface_of_trace {step : SNet → SNet → Prop} {N₁ : SNet}
    {events : List (Nat × Nat)} (htr : ClaimTrace step N₁ events) :
    S1CheckerInterface step N₁ events (0 < (s1Run events).viols) :=
  ⟨htr, s1_viol_delta events⟩

/-- The composed corollary through the arc4b leaf: **the model
checker is SILENT on every conforming dialect's claim traces** —
`s1_leaf` run end-to-end at the model instance. -/
theorem s1_model_silent {voters : List Nat} {step : SNet → SNet → Prop}
    (ob : ElectObligations voters step) {N₀ N₁ : SNet}
    (hseed : Seed N₀) (h01 : ReachRel step N₀ N₁)
    {events : List (Nat × Nat)} (htr : ClaimTrace step N₁ events) :
    (s1Run events).viols = 0 :=
  Nat.eq_zero_of_not_pos (s1_leaf ob hseed h01 (s1_interface_of_trace htr))

/-! ## 2. The S2/S3 checker fold (twin-lib.go:298-335, `apply`) -/

/-- An apply event: node `i` applies entry `(idx, trm, data)`; `data
= 0` models the empty payload (the leader's noop — twin-lib.go:319's
early return). -/
structure AEv where
  node : Nat
  idx  : Nat
  trm  : Nat
  data : Nat
  deriving Repr, DecidableEq

/-- A node's apply record in the interface's entry vocabulary — the
abstraction the `hlog` premise ties to `(Nf.node i).appliedLog`. -/
def nodeEvents (i : Nat) (events : List AEv) : Hist :=
  (events.filter (fun e => e.node == i)).map (fun e => (e.idx, e.trm, e.data))

/-- The S2/S3 checker state: `byIndex` (idx ↦ term, data, first
applier — insert-if-absent, so at most one entry per index), the
per-node cursors, the two counters (the code counts each S3 guard
separately; the model does too). -/
structure S23St where
  byIndex : List (Nat × Nat × Nat × Nat)
  applied : Nat → Nat
  lastTrm : Nat → Nat
  violS2 : Nat
  violS3 : Nat

def lookupIdx : List (Nat × Nat × Nat × Nat) → Nat → Option (Nat × Nat × Nat)
  | [], _ => none
  | (i, t, d, n) :: rest, i' => if i = i' then some (t, d, n) else lookupIdx rest i'

/-- The S2 disagreement count of one event (0 on the noop path —
twin-lib.go:319 returns before the byIndex block). -/
def s2Hit (st : S23St) (e : AEv) : Nat :=
  if e.data = 0 then 0
  else match lookupIdx st.byIndex e.idx with
    | some (t, d, _) => if t ≠ e.trm ∨ d ≠ e.data then 1 else 0
    | none => 0

/-- One apply step, branch-for-branch with the code (S3 guards
against the cursors, cursor update, noop early-return, byIndex
first-insert + disagreement). -/
def s23Step (st : S23St) (e : AEv) : S23St :=
  { byIndex :=
      if e.data = 0 then st.byIndex
      else match lookupIdx st.byIndex e.idx with
        | some _ => st.byIndex
        | none => (e.idx, e.trm, e.data, e.node) :: st.byIndex,
    applied := fun n => if n = e.node then e.idx else st.applied n,
    lastTrm := fun n => if n = e.node then e.trm else st.lastTrm n,
    violS2 := st.violS2 + s2Hit st e,
    violS3 := st.violS3 + (if e.idx ≤ st.applied e.node then 1 else 0)
                        + (if e.trm < st.lastTrm e.node then 1 else 0) }

def s23Run (events : List AEv) : S23St :=
  events.foldl s23Step ⟨[], fun _ => 0, fun _ => 0, 0, 0⟩

/-! ### The delta shapes (the interface's, over the model's records) -/

/-- The S2 delta over the event model — `s2Sound`'s shape at
`nodeEvents`. -/
def S2DeltaM (F : List AEv) : Prop :=
  ∃ (i j : Nat) (e e' : Nat × Nat × Nat), e ∈ nodeEvents i F ∧ e' ∈ nodeEvents j F
    ∧ e.1 = e'.1 ∧ e ≠ e'

/-- The S3 delta over the event model — `s3Sound`'s shape. -/
def S3DeltaM (F : List AEv) : Prop :=
  ∃ (n p q : Nat) (ep eq : Nat × Nat × Nat), p < q
    ∧ (nodeEvents n F)[p]? = some ep ∧ (nodeEvents n F)[q]? = some eq
    ∧ (eq.1 ≤ ep.1 ∨ eq.2.1 < ep.2.1)

/-! ### List plumbing -/

theorem nodeEvents_append (i : Nat) (P Q : List AEv) :
    nodeEvents i (P ++ Q) = nodeEvents i P ++ nodeEvents i Q := by
  simp [nodeEvents, List.filter_append]

theorem mem_nodeEvents_of_mem {e : AEv} {F : List AEv} (h : e ∈ F) :
    (e.idx, e.trm, e.data) ∈ nodeEvents e.node F := by
  refine List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨h, ?_⟩, rfl⟩
  simp

theorem lookupIdx_mem {lst : List (Nat × Nat × Nat × Nat)} {i t d n : Nat}
    (h : lookupIdx lst i = some (t, d, n)) : (i, t, d, n) ∈ lst := by
  induction lst with
  | nil => cases h
  | cons q rest ih =>
    obtain ⟨qi, qt, qd, qn⟩ := q
    unfold lookupIdx at h
    by_cases hi : qi = i
    · rw [if_pos hi] at h
      have h' := Option.some.inj h
      rw [show ((i, t, d, n) : Nat × Nat × Nat × Nat) = (i, (t, d, n)) from rfl,
        ← h', ← hi]
      exact List.mem_cons_self ..
    · rw [if_neg hi] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ### The S23 bridge induction -/

/-- The fold invariant relative to the full list `F` and processed
prefix `P`: byIndex entries are recorded applies (∈ their node's
record over `F`), the cursors are the node's LAST processed apply,
and fired counters already witness their deltas. -/
structure S23Inv (F P : List AEv) (st : S23St) : Prop where
  bx : ∀ q ∈ st.byIndex, (q.1, q.2.1, q.2.2.1) ∈ nodeEvents q.2.2.2 F
  cur : ∀ n,
    st.applied n = ((nodeEvents n P).getLast?.map (fun x => x.1)).getD 0
    ∧ st.lastTrm n = ((nodeEvents n P).getLast?.map (fun x => x.2.1)).getD 0
  hs2 : 0 < st.violS2 → S2DeltaM F
  hs3 : 0 < st.violS3 → S3DeltaM F

theorem nodeEvents_singleton (n : Nat) (e : AEv) :
    nodeEvents n [e] = if e.node = n then [(e.idx, e.trm, e.data)] else [] := by
  by_cases h : e.node = n <;> simp [nodeEvents, h]

/-- One apply step preserves the bridge invariant (the processed
prefix grows by `e`). -/
theorem s23Inv_step {F P : List AEv} {st : S23St} {e : AEv} {rest : List AEv}
    (hF : P ++ e :: rest = F)
    (hpos : ∀ x ∈ F, 1 ≤ x.idx)
    (hI : S23Inv F P st) :
    S23Inv F (P ++ [e]) (s23Step st e) := by
  have heF : e ∈ F := by
    rw [← hF]; exact List.mem_append_right _ (List.mem_cons_self ..)
  -- the split of the full record at the new prefix
  have hFsplit : ∀ n, nodeEvents n F
      = (nodeEvents n P ++ nodeEvents n [e]) ++ nodeEvents n rest := by
    intro n
    rw [← hF, show P ++ e :: rest = (P ++ [e]) ++ rest by simp,
      nodeEvents_append, nodeEvents_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bx
    intro q hq
    simp only [s23Step] at hq
    by_cases hd : e.data = 0
    · rw [if_pos hd] at hq; exact hI.bx q hq
    · rw [if_neg hd] at hq
      cases hl : lookupIdx st.byIndex e.idx with
      | some v => rw [hl] at hq; exact hI.bx q hq
      | none =>
        rw [hl] at hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact mem_nodeEvents_of_mem heF
        · exact hI.bx q hq'
  · -- cur
    intro n
    have hsplit : nodeEvents n (P ++ [e])
        = nodeEvents n P ++ nodeEvents n [e] := nodeEvents_append ..
    by_cases hn : e.node = n
    · rw [hsplit, nodeEvents_singleton, if_pos hn, List.getLast?_concat]
      subst hn
      simp only [s23Step, if_pos rfl, Option.map_some, Option.getD_some]
      exact ⟨rfl, rfl⟩
    · rw [hsplit, nodeEvents_singleton, if_neg hn, List.append_nil]
      simp only [s23Step]
      rw [if_neg (fun h => hn h.symm), if_neg (fun h => hn h.symm)]
      exact hI.cur n
  · -- hs2
    intro hv
    simp only [s23Step] at hv
    by_cases hd : e.data = 0
    · have : 0 < st.violS2 := by
        simp only [s2Hit, hd, if_pos rfl, Nat.add_zero] at hv; exact hv
      exact hI.hs2 this
    · cases hl : lookupIdx st.byIndex e.idx with
      | none =>
        have : 0 < st.violS2 := by
          simp only [s2Hit, hd, if_neg hd, hl, Nat.add_zero] at hv; exact hv
        exact hI.hs2 this
      | some v =>
        obtain ⟨t, d, n'⟩ := v
        by_cases htd : t ≠ e.trm ∨ d ≠ e.data
        · -- THE S2 FIRE: both records are on the board
          have hmem1 : (e.idx, t, d) ∈ nodeEvents n' F :=
            hI.bx _ (lookupIdx_mem hl)
          have hmem2 : (e.idx, e.trm, e.data) ∈ nodeEvents e.node F :=
            mem_nodeEvents_of_mem heF
          refine ⟨n', e.node, (e.idx, t, d), (e.idx, e.trm, e.data),
            hmem1, hmem2, rfl, ?_⟩
          intro heq
          have h1 : t = e.trm := congrArg (fun z => z.2.1) heq
          have h2 : d = e.data := congrArg (fun z => z.2.2) heq
          rcases htd with h | h
          · exact h h1
          · exact h h2
        · have : 0 < st.violS2 := by
            simp only [s2Hit, hd, if_neg hd, hl, if_neg htd, Nat.add_zero] at hv
            exact hv
          exact hI.hs2 this
  · -- hs3
    intro hv
    simp only [s23Step] at hv
    obtain ⟨hcurA, hcurT⟩ := hI.cur e.node
    -- the shared delta builder, given a fired guard
    have hbuild : ∀ (x : Nat × Nat × Nat),
        (nodeEvents e.node P).getLast? = some x →
        (e.idx ≤ x.1 ∨ e.trm < x.2.1) → S3DeltaM F := by
      intro x hlast hbad
      have hLne : nodeEvents e.node P ≠ [] := by
        intro h; rw [h] at hlast; cases hlast
      have hlen : 0 < (nodeEvents e.node P).length := by
        cases hcl : nodeEvents e.node P with
        | nil => exact absurd hcl hLne
        | cons _ _ => simp
      have hpL : (nodeEvents e.node P)[(nodeEvents e.node P).length - 1]?
          = some x := by
        rw [← List.getLast?_eq_getElem?]; exact hlast
      have hne : nodeEvents e.node [e] = [(e.idx, e.trm, e.data)] := by
        rw [nodeEvents_singleton, if_pos rfl]
      refine ⟨e.node, (nodeEvents e.node P).length - 1,
        (nodeEvents e.node P).length, x, (e.idx, e.trm, e.data),
        by omega, ?_, ?_, hbad⟩
      · rw [hFsplit e.node, hne,
          List.getElem?_append_left (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getElem?_append_left (by omega)]
        exact hpL
      · rw [hFsplit e.node, hne,
          List.getElem?_append_left (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
        exact List.getElem?_concat_length ..
    by_cases hg1 : e.idx ≤ st.applied e.node
    · -- idx guard fired
      cases hlast : (nodeEvents e.node P).getLast? with
      | none =>
        -- cursors zero: contradicts 1 ≤ e.idx
        rw [hlast] at hcurA
        simp only [Option.map_none, Option.getD_none] at hcurA
        have := hpos e heF
        omega
      | some x =>
        rw [hlast] at hcurA
        simp only [Option.map_some, Option.getD_some] at hcurA
        exact hbuild x hlast (Or.inl (hcurA ▸ hg1))
    · by_cases hg2 : e.trm < st.lastTrm e.node
      · cases hlast : (nodeEvents e.node P).getLast? with
        | none =>
          rw [hlast] at hcurT
          simp only [Option.map_none, Option.getD_none] at hcurT
          rw [hcurT] at hg2
          exact absurd hg2 (Nat.not_lt_zero _)
        | some x =>
          rw [hlast] at hcurT
          simp only [Option.map_some, Option.getD_some] at hcurT
          exact hbuild x hlast (Or.inr (hcurT ▸ hg2))
      · have : 0 < st.violS3 := by
          simp only [if_neg hg1, if_neg hg2, Nat.add_zero] at hv
          exact hv
        exact hI.hs3 this

/-- The bridge induction, run over the whole event list. -/
theorem s23_bridge_aux (F : List AEv) (hpos : ∀ x ∈ F, 1 ≤ x.idx) :
    ∀ (evs P : List AEv) (st : S23St), P ++ evs = F →
      S23Inv F P st → S23Inv F F (evs.foldl s23Step st) := by
  intro evs
  induction evs with
  | nil =>
    intro P st hF hI
    rw [List.append_nil] at hF
    subst hF
    exact hI
  | cons e rest ih =>
    intro P st hF hI
    simp only [List.foldl_cons]
    exact ih (P ++ [e]) _ (by rw [List.append_assoc]; simpa using hF)
      (s23Inv_step hF hpos hI)

/-- **THE S2/S3 BRIDGE**: the fold's violation counters fire only on
deltas of the interface's exact shapes over the event records. -/
theorem s23_viol_delta {events : List AEv} (hpos : ∀ x ∈ events, 1 ≤ x.idx) :
    (0 < (s23Run events).violS2 → S2DeltaM events)
      ∧ (0 < (s23Run events).violS3 → S3DeltaM events) := by
  have h0 : S23Inv events [] ⟨[], fun _ => 0, fun _ => 0, 0, 0⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq; cases hq
    · intro n
      simp [nodeEvents]
    · intro h; exact absurd h (Nat.lt_irrefl 0)
    · intro h; exact absurd h (Nat.lt_irrefl 0)
  have hfin := s23_bridge_aux events hpos events [] _ rfl h0
  exact ⟨hfin.hs2, hfin.hs3⟩

/-- **The I2 instantiation of `S23CheckerInterface`** at the model
checker's violation flags: the remaining premises are the appliedLog
projection (`hlog` — the ENode↔HNode convention seam) and index
positivity (derived from the chain in the corollary below). The
predicate halves are closed. -/
theorem s23_interface_of_run {Nf : HNet} {events : List AEv}
    (hlog : ∀ i, (Nf.node i).appliedLog = nodeEvents i events)
    (hpos : ∀ x ∈ events, 1 ≤ x.idx) :
    S23CheckerInterface Nf (0 < (s23Run events).violS2)
      (0 < (s23Run events).violS3) := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨i, j, e, e', he, he', hidx, hne⟩ := (s23_viol_delta hpos).1 hv
    exact ⟨i, j, e, e', by rw [hlog i]; exact he,
      by rw [hlog j]; exact he', hidx, hne⟩
  · obtain ⟨n, p, q, ep, eq, hpq, hp, hq, hbad⟩ := (s23_viol_delta hpos).2 hv
    exact ⟨n, p, q, ep, eq, hpq, by rw [hlog n]; exact hp,
      by rw [hlog n]; exact hq, hbad⟩

/-- The composed corollary through the arc4b leaf: **the model
checker's S2/S3 counters are silent on every reachable final net of
the T1 fragment** — `s23_leaf` run end-to-end at the model instance,
with index positivity DERIVED from the chain's `histIdx`/
`appliedTake` (no extra premise). -/
theorem s23_model_silent {ldr tm : Nat} {certified : Nat → Prop}
    {N₀ Nf : HNet} (h0 : HistInv ldr tm N₀)
    (hr : Star (HStep ldr tm certified) N₀ Nf)
    {events : List AEv}
    (hlog : ∀ i, (Nf.node i).appliedLog = nodeEvents i events) :
    (s23Run events).violS2 = 0 ∧ (s23Run events).violS3 = 0 := by
  have hInv := histInv_reachable h0 hr
  have hpos : ∀ x ∈ events, 1 ≤ x.idx := by
    intro x hx
    have hmem := mem_nodeEvents_of_mem hx
    rw [← hlog x.node, hInv.appliedTake x.node] at hmem
    have hh : (x.idx, x.trm, x.data) ∈ Nf.hist :=
      (List.take_sublist _ _).mem hmem
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hh
    have := hInv.histIdx k _ hk
    simp only at this
    omega
  have hleaf := s23_leaf h0 hr (s23_interface_of_run hlog hpos)
  exact ⟨Nat.eq_zero_of_not_pos hleaf.1, Nat.eq_zero_of_not_pos hleaf.2⟩

/-! ## 3. The shape pins — the model's guard vocabulary IS the pinned
lowering's (the DriverNet pin pattern; every `.any` value #eval'd
true before the kernel pin — `artifacts/probe/BridgeEvalProbe.lean` (untracked scratch)
→ `bridgeeval.out`) -/

section ShapePins

open GoLean.GoCore
open GoLean.Examples.RaftTwin (twinLowered)

set_option maxRecDepth 1000000

/-- twin-lib.go:303 `idx <= nd.applied` — the S3 index guard,
lowered. -/
def s3IdxGuard : Expr :=
  .atMostCmp (.var "idx")
    (.fieldGet (.deref (.var "nd") (.defined ⟨"main.twinNode"⟩))
      ⟨"main.twinNode"⟩ "applied")

/-- twin-lib.go:307 `trm < nd.lastTrm` — the S3 term guard. -/
def s3TermGuard : Expr :=
  .lessCmp (.var "trm")
    (.fieldGet (.deref (.var "nd") (.defined ⟨"main.twinNode"⟩))
      ⟨"main.twinNode"⟩ "lastTrm")

/-- twin-lib.go:327 `s.term != trm || s.data != data` — the S2
disagreement guard. -/
def s2Guard : Expr :=
  .or (.neqCmp (.int .uint64)
        (.fieldGet (.var "s") ⟨"main.slot"⟩ "term") (.var "trm"))
      (.neqCmp .string
        (.fieldGet (.var "s") ⟨"main.slot"⟩ "data") (.var "data"))

/-- twin-lib.go:273 `ok && prev != nd.id` — the S1 disagreement
guard. -/
def s1Guard : Expr :=
  .and (.var "ok")
    (.neqCmp (.int .uint64) (.var "prev")
      (.fieldGet (.deref (.var "nd") (.defined ⟨"main.twinNode"⟩))
        ⟨"main.twinNode"⟩ "id"))

/-- Collect every if-guard (recursively), fuel-structural — the
`collectWhilesF` pattern at guards. -/
def collectIfCondsF : Nat → Stmt → List Expr
  | 0, _ => []
  | fuel + 1, s =>
      match s with
      | .ifThenElse c t e =>
          c :: (collectIfCondsF fuel t ++ collectIfCondsF fuel e)
      | .block _ ss => ss.toList.flatMap (collectIfCondsF fuel)
      | .seqn ss => ss.toList.flatMap (collectIfCondsF fuel)
      | .while _ b => collectIfCondsF fuel b
      | .labeled _ b => collectIfCondsF fuel b
      | .breakable b => collectIfCondsF fuel b
      | .mapRange _ _ _ _ _ b => collectIfCondsF fuel b
      | _ => []

/-- The if-guards of a pinned function's body. -/
def funcIfConds (name : String) : List Expr :=
  match findFunctionIn? twinLowered.funcs ⟨name⟩ with
  | some f => collectIfCondsF 64 f.body
  | none => []

/-- **SHAPE PIN (S3 idx)**: the model's guard occurs verbatim among
`main.twin.apply`'s if-guards. -/
theorem s3IdxGuard_pinned :
    (funcIfConds "main.twin.apply").any
      (fun e => Expr.eqbF 4096 e s3IdxGuard) = true := by
  kernel_rfl

/-- **SHAPE PIN (S3 term)**. -/
theorem s3TermGuard_pinned :
    (funcIfConds "main.twin.apply").any
      (fun e => Expr.eqbF 4096 e s3TermGuard) = true := by
  kernel_rfl

/-- **SHAPE PIN (S2)**. -/
theorem s2Guard_pinned :
    (funcIfConds "main.twin.apply").any
      (fun e => Expr.eqbF 4096 e s2Guard) = true := by
  kernel_rfl

/-- **SHAPE PIN (S1)**: the disagreement guard occurs verbatim among
`main.twin.harvest`'s if-guards (S1 rides inline in harvest — the C1
census). -/
theorem s1Guard_pinned :
    (funcIfConds "main.twin.harvest").any
      (fun e => Expr.eqbF 4096 e s1Guard) = true := by
  kernel_rfl

/-- The Prop forms (via `Expr.eqbF_sound`): the real lowered checker
CONTAINS the proved guards. -/
theorem s3IdxGuard_pinned_prop :
    ∃ c ∈ funcIfConds "main.twin.apply", c = s3IdxGuard := by
  obtain ⟨c, hmem, hb⟩ := List.any_eq_true.mp s3IdxGuard_pinned
  exact ⟨c, hmem, Expr.eqbF_sound _ _ _ hb⟩

theorem s3TermGuard_pinned_prop :
    ∃ c ∈ funcIfConds "main.twin.apply", c = s3TermGuard := by
  obtain ⟨c, hmem, hb⟩ := List.any_eq_true.mp s3TermGuard_pinned
  exact ⟨c, hmem, Expr.eqbF_sound _ _ _ hb⟩

theorem s2Guard_pinned_prop :
    ∃ c ∈ funcIfConds "main.twin.apply", c = s2Guard := by
  obtain ⟨c, hmem, hb⟩ := List.any_eq_true.mp s2Guard_pinned
  exact ⟨c, hmem, Expr.eqbF_sound _ _ _ hb⟩

theorem s1Guard_pinned_prop :
    ∃ c ∈ funcIfConds "main.twin.harvest", c = s1Guard := by
  obtain ⟨c, hmem, hb⟩ := List.any_eq_true.mp s1Guard_pinned
  exact ⟨c, hmem, Expr.eqbF_sound _ _ _ hb⟩

end ShapePins

-- W0 reset (kill-list K-C, 2026-08-27): the fire/clean witness section
-- (s1w_fire/clean/delta, wCleanEvs, s23w_clean/fire2/fire3, wNf,
-- s23w_iface) is deleted — instance-shaped demonstrations, the class the
-- reset removes. The retained non-vacuity demonstrations for the
-- interface premises are NativeS1Witness/NativeS23Witness (kill-list
-- amendment) until W5. Archived at archive/fixed-trajectory-era.

end GoLean.RaftSeam.NativeSpec
