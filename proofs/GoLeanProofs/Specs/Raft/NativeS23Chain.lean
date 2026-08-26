import GoLeanProofs.Specs.Raft.NativeS23Route
import GoLeanProofs.Specs.Raft.NativeS1Chain

/-! # C4 — the T1-scoped S2/S3 ghost-history chain (H1→H4)
(scoping lane `campaign-arc4b`, unit C4, 2026-08-27; SC1's leading
route, `NativeS23Route.lean` §5; design of record §3 I1/I4 + §7
middle-path calibration, binding.)

## What this module is

The T1-scoped ghost-history chain: an append/commit/apply fragment
step relation (`HStep`) whose commit/apply premises are SC1's three
commit-axis obligation members and the apply window QUOTED VERBATIM
(`commitInWindow` / `leaderCommitOk` / `followerCommitOk` /
`appliedWindow` — the obligation consumption is syntactic, visible
in the constructor types), the H1–H4 invariant bundle (`HistInv`)
proved preserved, and the S2/S3 leaves feeding SC1's proved
assemblies (`s2_agree_of_hist` / `s3_term_of_hist`).

## The carrier (a statement-side correction, logged)

SC1's §5 skeleton Props are typed over `SNet`, whose `ENode` has no
applied record — `appliedOf : SNet → ...` has nothing to project
from. The chain therefore lives on the extended carrier `HNet`
below, link-for-link the same logical shape; the SNet-typed
sketches stand superseded (statement-only, zero consumers).
Likewise `Skel_singleWriterHistory` as literally stated (two
independently-reachable nets, prefix-comparable) is falsified by
traces diverging on different proposals; the chain needs and proves
the along-one-trace form (`hist_prefix_star`).

## T1 scoping (§7, binding)

`ldr` and `tm` are the fragment's parameters — supplied at assembly
time by the S1 chain's output (the unique leader and its stable
term: `native_one_leader_per_term` + O5b). The fragment models the
POST-ELECTION deliver loop: only `propose` extends the history
(H1's single-writer shape, structural — justified by the driver's
one pre-loop campaign, twin-chdriver.go:44, and the S1 result), and
message payloads are history slices (the leader's log IS the
history, invariant `leaderLog`). `certified : Nat → Prop` is O-C2's
abstract certification predicate, consumed BY NAME and never
inspected — the recorded seam where the S2-wave's match-evidence
concretization attaches (SC1's `leaderCommitOk` note). The
heartbeat match-soundness member stays OUT per the D3
unreachability refutation (charter-binding; a witness-demonstrated
need would go to the log first). S3's ANOMALY sub-check (EntryNormal
typing) is not representable in the abstract vocabulary — every
abstract entry is by construction a driver proposal or the noop;
the concrete Type-field correspondence rides the I2 interface
premise, recorded here as the scope note.

LINEAGE: history/auxiliary-variable refinement (Abadi–Lamport), the
S2/S3 leaves as property transfer through the mapping — SC1's §5
LINEAGE, unchanged. -/

namespace GoLean.RaftSeam.NativeSpec

/-! ## The generic closure — UNIFIED (arc-4 landing fix round,
2026-08-26): the polymorphic `Star` + `Star.trans` + `star_invariance`
formerly declared here (duplicating C3's SNet-typed `ReachRel` rule
for rule, under a "landing-time unification candidate" tag) now live
ONCE in `NativeS1Chain.lean`, with `ReachRel` as the SNet
abbreviation. This module consumes them via the import above. -/

/-! ## The S2/S3 carrier -/

/-- The fragment node: log as a `Hist` PREFIX (oldest-first, unlike
`ENode`'s newest-first — the projection between the two conventions
is I2's absTwinRead concern), the commit/apply cursors (indexes),
and the applied record in apply order. -/
structure HNode where
  log : Hist
  committed : Nat
  applied : Nat
  appliedLog : Hist

/-- The extended net: the ghost history plus node states. -/
structure HNet where
  hist : Hist
  node : Nat → HNode

def updHNode (N : HNet) (i : Nat) (n : HNode) (H : Hist) : HNet :=
  { hist := H, node := fun j => if j = i then n else N.node j }

theorem updHNode_self (N : HNet) (i : Nat) (n : HNode) (H : Hist) :
    (updHNode N i n H).node i = n := by simp [updHNode]

theorem updHNode_other (N : HNet) {i j : Nat} (n : HNode) (H : Hist)
    (h : j ≠ i) : (updHNode N i n H).node j = N.node j := by
  simp [updHNode, h]

theorem updHNode_hist (N : HNet) (i : Nat) (n : HNode) (H : Hist) :
    (updHNode N i n H).hist = H := rfl

/-! ## The T1 fragment step relation

Every commit/apply premise is an SC1 obligation Prop verbatim. -/

inductive HStep (ldr tm : Nat) (certified : Nat → Prop) :
    HNet → HNet → Prop where
  /-- The leader appends a proposal (or the noop, `d = 0`) at its
  stable term: the ONLY history writer (H1's shape). -/
  | propose (N : HNet) (d : Nat) :
      HStep ldr tm certified N
        (updHNode N ldr
          { N.node ldr with
              log := (N.node ldr).log ++ [(N.hist.length + 1, tm, d)] }
          (N.hist ++ [(N.hist.length + 1, tm, d)]))
  /-- The leader advances its commit: O-C1 (`commitInWindow`) +
  O-C2 (`leaderCommitOk`), both verbatim. -/
  | leaderCommit (N : HNet) (c' : Nat)
      (hwin : commitInWindow (N.node ldr).committed
        (N.node ldr).log.length c')
      (hok : leaderCommitOk certified (N.node ldr).committed c') :
      HStep ldr tm certified N
        (updHNode N ldr { N.node ldr with committed := c' } N.hist)
  /-- A follower accepts an append: its log extends to the delivered
  history slice (payloads are leader-log slices = history slices —
  the single-writer structure), commit advances inside O-C3
  (`followerCommitOk`, verbatim; `lc` is the message's leaderCommit,
  `k` the matched last-new index). `k ≤ |H|` is the payload-is-a-
  history-slice bound. -/
  | deliverAppend (N : HNet) (i k lc c' : Nat)
      (hk : k ≤ N.hist.length)
      (hok : followerCommitOk (N.node i).committed lc k c') :
      HStep ldr tm certified N
        (updHNode N i
          { N.node i with
              log := N.hist.take (max (N.node i).log.length k),
              committed := c' }
          N.hist)
  /-- A node applies its committed window: the applied cursor moves
  to `k` inside `appliedWindow` (verbatim), the applied record
  extends with exactly the log entries in `(applied, k]`, in log
  order (`nextCommittedEnts`' slice shape, log.go:220-244). -/
  | applyStep (N : HNet) (i k : Nat)
      (hwin : appliedWindow (N.node i).applied (N.node i).committed k) :
      HStep ldr tm certified N
        (updHNode N i
          { N.node i with
              applied := k,
              appliedLog := (N.node i).appliedLog ++
                (((N.node i).log.drop (N.node i).applied).take
                  (k - (N.node i).applied)) }
          N.hist)

/-! ## The H1–H4 invariant bundle -/

/-- The chain invariant (the H2/H3/H4 links as one inductive
bundle; H1 is the star lemma below):

- `histIdx`/`histTermMono` = H2 (index-consecutive, term-monotone);
- `histTermsLe` = the fixed-leader-term auxiliary (all history
  terms ≤ `tm` — what makes appends-at-`tm` term-monotone);
- `leaderLog` = the leader's log IS the history (single-writer,
  T1-structural);
- `logsPrefix` = H3 (every log a history prefix, take-form);
- `commitWindow` = the O-C1 window carried (commit ≤ log end);
- `applyWindow` = the apply cursor inside the commit window;
- `appliedTake` = H4 in its strongest T1 form: the applied record
  IS the history prefix of length `applied` (membership-form H4 and
  the S3 order facts are corollaries — the leaves below). -/
structure HistInv (ldr tm : Nat) (N : HNet) : Prop where
  histIdx : ∀ (k : Nat) (e : Nat × Nat × Nat),
    N.hist[k]? = some e → e.1 = k + 1
  histTermMono : ∀ (k k' : Nat) (e e' : Nat × Nat × Nat), k ≤ k' →
    N.hist[k]? = some e → N.hist[k']? = some e' → e.2.1 ≤ e'.2.1
  histTermsLe : ∀ e ∈ N.hist, e.2.1 ≤ tm
  leaderLog : (N.node ldr).log = N.hist
  logsPrefix : ∀ i, ∃ m, (N.node i).log = N.hist.take m
  commitWindow : ∀ i, (N.node i).committed ≤ (N.node i).log.length
  applyWindow : ∀ i, (N.node i).applied ≤ (N.node i).committed
  appliedTake : ∀ i,
    (N.node i).appliedLog = N.hist.take (N.node i).applied

/-! ### List plumbing for the preservation proofs -/

theorem take_stable {α : Type _} {l l' : List α} {a : Nat}
    (h : a ≤ l.length) : (l ++ l').take a = l.take a :=
  List.take_append_of_le_length h

theorem singleton_getElem? {α : Type _} {x e : α} {k : Nat}
    (h : [x][k]? = some e) : k = 0 ∧ e = x := by
  match k with
  | 0 => exact ⟨rfl, (Option.some.inj h).symm⟩
  | k + 1 => simp at h

/-- The applied-record computation at an `applyStep`: prefix + the
next log window = the longer prefix. -/
theorem take_append_window {α : Type _} (H : List α) {m a k : Nat}
    (hak : a ≤ k) (hkm : k ≤ m) :
    H.take a ++ ((H.take m).drop a).take (k - a) = H.take k := by
  rw [List.drop_take, List.take_take]
  have hmin : min (k - a) (m - a) = k - a :=
    Nat.min_eq_left (Nat.sub_le_sub_right hkm a)
  rw [hmin, ← List.take_add]
  congr 1
  omega

/-! ### The preservation induction -/

theorem HistInv.step {ldr tm : Nat} {certified : Nat → Prop}
    {N N' : HNet} (hI : HistInv ldr tm N)
    (hs : HStep ldr tm certified N N') : HistInv ldr tm N' := by
  cases hs with
  | propose d =>
    -- the one history-extending step
    have hIdx : ∀ (k : Nat) (e : Nat × Nat × Nat),
        (N.hist ++ [(N.hist.length + 1, tm, d)])[k]? = some e →
        e.1 = k + 1 := by
      intro k e hk
      by_cases hlt : k < N.hist.length
      · rw [List.getElem?_append_left hlt] at hk
        exact hI.histIdx k e hk
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hk
        obtain ⟨hz, he⟩ := singleton_getElem? hk
        have hkl : k = N.hist.length := by omega
        rw [he, hkl]
    have hMem : ∀ e, e ∈ N.hist ++ [(N.hist.length + 1, tm, d)] →
        e.2.1 ≤ tm := by
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact hI.histTermsLe e h
      · rcases List.mem_singleton.mp h with rfl
        exact Nat.le_refl _
    refine ⟨hIdx, ?_, hMem, ?_, ?_, ?_, ?_, ?_⟩
    · -- term-monotone: old-old by IH; anything-new by histTermsLe
      intro k k' e e' hkk hk hk'
      rw [updHNode_hist] at hk hk'
      by_cases hlt' : k' < N.hist.length
      · have hlt : k < N.hist.length := Nat.lt_of_le_of_lt hkk hlt'
        rw [List.getElem?_append_left hlt] at hk
        rw [List.getElem?_append_left hlt'] at hk'
        exact hI.histTermMono k k' e e' hkk hk hk'
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt')] at hk'
        obtain ⟨-, he'⟩ := singleton_getElem? hk'
        subst he'
        by_cases hlt : k < N.hist.length
        · rw [List.getElem?_append_left hlt] at hk
          exact hI.histTermsLe e (List.mem_of_getElem? hk)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hk
          obtain ⟨-, he⟩ := singleton_getElem? hk
          subst he
          exact Nat.le_refl _
    · -- leaderLog
      rw [updHNode_self, updHNode_hist]
      show (N.node ldr).log ++ _ = _
      rw [hI.leaderLog]
    · -- logsPrefix
      intro i
      by_cases hij : i = ldr
      · subst hij
        rw [updHNode_self, updHNode_hist]
        refine ⟨N.hist.length + 1, ?_⟩
        show (N.node i).log ++ _ = _
        rw [hI.leaderLog]
        rw [List.take_of_length_le (by simp)]
      · rw [updHNode_other _ _ _ hij, updHNode_hist]
        obtain ⟨m, hm⟩ := hI.logsPrefix i
        refine ⟨min m N.hist.length, ?_⟩
        rw [take_stable (by omega), hm, ← List.take_take,
          List.take_length]
    · -- commitWindow
      intro i
      by_cases hij : i = ldr
      · subst hij
        rw [updHNode_self]
        show (N.node i).committed ≤ ((N.node i).log ++ _).length
        have := hI.commitWindow i
        simp only [List.length_append]
        omega
      · rw [updHNode_other _ _ _ hij]
        exact hI.commitWindow i
    · -- applyWindow
      intro i
      by_cases hij : i = ldr
      · subst hij
        rw [updHNode_self]
        exact hI.applyWindow i
      · rw [updHNode_other _ _ _ hij]
        exact hI.applyWindow i
    · -- appliedTake: applied ≤ |hist|, so the take is stable
      intro i
      have happ : (N.node i).applied ≤ N.hist.length := by
        obtain ⟨m, hm⟩ := hI.logsPrefix i
        have h1 := hI.applyWindow i
        have h2 := hI.commitWindow i
        have h3 : (N.node i).log.length ≤ N.hist.length := by
          rw [hm, List.length_take]
          omega
        omega
      by_cases hij : i = ldr
      · subst hij
        rw [updHNode_self, updHNode_hist]
        show (N.node i).appliedLog = _
        rw [take_stable happ]
        exact hI.appliedTake i
      · rw [updHNode_other _ _ _ hij, updHNode_hist,
          take_stable happ]
        exact hI.appliedTake i
  | leaderCommit c' hwin hok =>
    refine ⟨hI.histIdx, hI.histTermMono, hI.histTermsLe, ?_, ?_,
      ?_, ?_, ?_⟩
    · by_cases hij : (ldr : Nat) = ldr
      · rw [updHNode_self]; exact hI.leaderLog
      · exact absurd rfl hij
    · intro i
      by_cases hij : i = ldr
      · subst hij; rw [updHNode_self]; exact hI.logsPrefix i
      · rw [updHNode_other _ _ _ hij]; exact hI.logsPrefix i
    · intro i
      by_cases hij : i = ldr
      · subst hij; rw [updHNode_self]; exact hwin.2
      · rw [updHNode_other _ _ _ hij]; exact hI.commitWindow i
    · intro i
      by_cases hij : i = ldr
      · subst hij
        rw [updHNode_self]
        exact Nat.le_trans (hI.applyWindow i) hok.1
      · rw [updHNode_other _ _ _ hij]; exact hI.applyWindow i
    · intro i
      by_cases hij : i = ldr
      · subst hij; rw [updHNode_self, updHNode_hist]
        exact hI.appliedTake i
      · rw [updHNode_other _ _ _ hij, updHNode_hist]
        exact hI.appliedTake i
  | deliverAppend i₀ k lc c' hk hok =>
    -- new log length: min (max len k) |H|
    obtain ⟨m₀, hm₀⟩ := hI.logsPrefix i₀
    have hlen : (N.node i₀).log.length ≤ N.hist.length := by
      rw [hm₀, List.length_take]; omega
    refine ⟨hI.histIdx, hI.histTermMono, hI.histTermsLe, ?_, ?_,
      ?_, ?_, ?_⟩
    · by_cases hij : (ldr : Nat) = i₀
      · rw [hij, updHNode_self]
        show N.hist.take _ = _
        rw [← hij, hI.leaderLog]
        exact List.take_of_length_le (Nat.le_max_left ..)
      · rw [updHNode_other _ _ _ hij]
        exact hI.leaderLog
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self, updHNode_hist]
        exact ⟨max (N.node i).log.length k, rfl⟩
      · rw [updHNode_other _ _ _ hij, updHNode_hist]
        exact hI.logsPrefix i
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self]
        show c' ≤ (N.hist.take _).length
        rw [List.length_take]
        have h1 := hok.1
        have h2 := hok.2
        have h3 := hI.commitWindow i
        have hmax : max (N.node i).committed (min lc k) ≤
            min (max (N.node i).log.length k) N.hist.length := by
          omega
        omega
      · rw [updHNode_other _ _ _ hij]
        exact hI.commitWindow i
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self]
        exact Nat.le_trans (hI.applyWindow i) hok.1
      · rw [updHNode_other _ _ _ hij]
        exact hI.applyWindow i
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self, updHNode_hist]
        exact hI.appliedTake i
      · rw [updHNode_other _ _ _ hij, updHNode_hist]
        exact hI.appliedTake i
  | applyStep i₀ k hwin =>
    obtain ⟨m₀, hm₀⟩ := hI.logsPrefix i₀
    refine ⟨hI.histIdx, hI.histTermMono, hI.histTermsLe, ?_, ?_,
      ?_, ?_, ?_⟩
    · by_cases hij : (ldr : Nat) = i₀
      · rw [hij, updHNode_self]
        show (N.node i₀).log = _
        rw [← hij]; exact hI.leaderLog
      · rw [updHNode_other _ _ _ hij]
        exact hI.leaderLog
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self, updHNode_hist]
        exact hI.logsPrefix i
      · rw [updHNode_other _ _ _ hij, updHNode_hist]
        exact hI.logsPrefix i
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self]
        exact hI.commitWindow i
      · rw [updHNode_other _ _ _ hij]
        exact hI.commitWindow i
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self]
        exact hwin.2
      · rw [updHNode_other _ _ _ hij]
        exact hI.applyWindow i
    · intro i
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self, updHNode_hist]
        show (N.node i).appliedLog ++ _ = _
        rw [hI.appliedTake i, hm₀]
        -- window bounds: applied ≤ k ≤ committed ≤ |log| = min m₀ |H|
        have hlen : (N.node i).log.length = min m₀ N.hist.length := by
          rw [hm₀, List.length_take]
        have h1 := hwin.1
        have h2 := hwin.2
        have h3 := hI.commitWindow i
        exact take_append_window N.hist h1 (by omega)
      · rw [updHNode_other _ _ _ hij, updHNode_hist]
        exact hI.appliedTake i

/-- The chain over the reachable set (the induction principle
applied once — C3's pattern on the extended carrier). -/
theorem histInv_reachable {ldr tm : Nat} {certified : Nat → Prop}
    {N₀ N : HNet} (h0 : HistInv ldr tm N₀)
    (hr : Star (HStep ldr tm certified) N₀ N) : HistInv ldr tm N :=
  star_invariance (fun hP hs => hP.step hs) h0 hr

/-! ## H1 — the along-one-trace single-writer facts (starred) -/

/-- H1, corrected form: along ONE trace the history only grows —
`propose` appends, every other step keeps it. (SC1's
`Skel_singleWriterHistory` quantified two independently-reachable
nets; that form is falsified by traces diverging on different
proposals — the finding is logged.) -/
theorem hist_prefix_star {ldr tm : Nat} {certified : Nat → Prop}
    {N N' : HNet} (hr : Star (HStep ldr tm certified) N N') :
    ∃ rest : Hist, N'.hist = N.hist ++ rest := by
  induction hr with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | tail _ hs ih =>
    obtain ⟨rest, hrest⟩ := ih
    cases hs with
    | propose d =>
      exact ⟨rest ++ [_], by rw [updHNode_hist, hrest,
        List.append_assoc]⟩
    | leaderCommit c' hwin hok => exact ⟨rest, hrest⟩
    | deliverAppend i k lc c' hk hok => exact ⟨rest, hrest⟩
    | applyStep i k hwin => exact ⟨rest, hrest⟩

/-- The applied record only grows along a trace (the I2-side
support for the final-net checker interface: the final net's
applied logs contain every apply the checker ever saw). -/
theorem appliedLog_prefix_star {ldr tm : Nat} {certified : Nat → Prop}
    {N N' : HNet} (hr : Star (HStep ldr tm certified) N N') :
    ∀ i, ∃ rest : Hist,
      (N'.node i).appliedLog = (N.node i).appliedLog ++ rest := by
  induction hr with
  | refl => exact fun i => ⟨[], (List.append_nil _).symm⟩
  | tail _ hs ih =>
    intro i
    obtain ⟨rest, hrest⟩ := ih i
    cases hs with
    | propose d =>
      by_cases hij : i = ldr
      · subst hij
        rw [updHNode_self]
        exact ⟨rest, hrest⟩
      · rw [updHNode_other _ _ _ hij]
        exact ⟨rest, hrest⟩
    | leaderCommit c' hwin hok =>
      by_cases hij : i = ldr
      · subst hij; rw [updHNode_self]; exact ⟨rest, hrest⟩
      · rw [updHNode_other _ _ _ hij]; exact ⟨rest, hrest⟩
    | deliverAppend i₀ k lc c' hk hok =>
      by_cases hij : i = i₀
      · subst hij; rw [updHNode_self]; exact ⟨rest, hrest⟩
      · rw [updHNode_other _ _ _ hij]; exact ⟨rest, hrest⟩
    | applyStep i₀ k hwin =>
      by_cases hij : i = i₀
      · subst hij
        rw [updHNode_self]
        exact ⟨rest ++ _,
          (congrArg (· ++ _) hrest).trans (List.append_assoc ..)⟩
      · rw [updHNode_other _ _ _ hij]; exact ⟨rest, hrest⟩

/-! ## The S2/S3 leaves (over the invariant bundle) -/

/-- Membership in the history pins the `histAt` lookup — the bridge
into SC1's proved assemblies. -/
theorem mem_hist_histAt {ldr tm : Nat} {N : HNet}
    (hI : HistInv ldr tm N) {e : Nat × Nat × Nat} (he : e ∈ N.hist) :
    histAt N.hist e.1 = some e := by
  obtain ⟨k, hk⟩ := List.getElem?_of_mem he
  have hidx := hI.histIdx k e hk
  unfold histAt
  rw [if_neg (by omega)]
  rw [show e.1 - 1 = k by omega]
  exact hk

/-- **THE S2 LEAF** — two applied records at one index agree,
across ANY two nodes (H4 take-form → history membership → SC1's
`s2_agree_of_hist`). -/
theorem s2_of_histInv {ldr tm : Nat} {N : HNet}
    (hI : HistInv ldr tm N) {i j : Nat} {e e' : Nat × Nat × Nat}
    (he : e ∈ (N.node i).appliedLog) (he' : e' ∈ (N.node j).appliedLog)
    (hidx : e.1 = e'.1) : e = e' := by
  rw [hI.appliedTake i] at he
  rw [hI.appliedTake j] at he'
  have hm : e ∈ N.hist := (List.take_sublist _ _).mem he
  have hm' : e' ∈ N.hist := (List.take_sublist _ _).mem he'
  exact s2_agree_of_hist (mem_hist_histAt hI hm)
    (mem_hist_histAt hI hm') hidx

/-- **THE S3 LEAF** — a node's applied sequence is strictly
index-increasing and term-monotone, positionally (H4 take-form +
H2; the term half routes through SC1's `s3_term_of_hist` shape via
`histTermMono` directly). -/
theorem s3_of_histInv {ldr tm : Nat} {N : HNet}
    (hI : HistInv ldr tm N) {i : Nat} {p q : Nat}
    {ep eq : Nat × Nat × Nat} (hpq : p < q)
    (hp : (N.node i).appliedLog[p]? = some ep)
    (hq : (N.node i).appliedLog[q]? = some eq) :
    ep.1 < eq.1 ∧ ep.2.1 ≤ eq.2.1 := by
  rw [hI.appliedTake i, List.getElem?_take] at hp hq
  have hp' : N.hist[p]? = some ep := by
    by_cases hlt : p < (N.node i).applied
    · rw [if_pos hlt] at hp; exact hp
    · rw [if_neg hlt] at hp; cases hp
  have hq' : N.hist[q]? = some eq := by
    by_cases hlt : q < (N.node i).applied
    · rw [if_pos hlt] at hq; exact hq
    · rw [if_neg hlt] at hq; cases hq
  constructor
  · rw [hI.histIdx p ep hp', hI.histIdx q eq hq']
    omega
  · exact hI.histTermMono p q ep eq (Nat.le_of_lt hpq) hp' hq'

/-! ## The I4 checker interface (S2/S3-scoped) and the leaf
theorems

Final-net form: unlike S1's claims (leaders appear and vanish — the
trace matters), applied records are CUMULATIVE
(`appliedLog_prefix_star`), so the final net carries every apply
the checker processed; the interface premise ties the checker's
violation branches to final-net deltas, and its proof against the
real checker span (through absTwinRead, including the
apply-order/byIndex mechanics and the EntryNormal typing — the
anomaly scope note above) is the arc-4 lane's I2 work. -/

structure S23CheckerInterface (Nf : HNet)
    (violS2 violS3 : Prop) : Prop where
  s2Sound : violS2 → ∃ i j e e', e ∈ (Nf.node i).appliedLog ∧
    e' ∈ (Nf.node j).appliedLog ∧ e.1 = e'.1 ∧ e ≠ e'
  s3Sound : violS3 → ∃ i p q : Nat, ∃ ep eq : Nat × Nat × Nat, p < q ∧
    (Nf.node i).appliedLog[p]? = some ep ∧
    (Nf.node i).appliedLog[q]? = some eq ∧
    (eq.1 ≤ ep.1 ∨ eq.2.1 < ep.2.1)

/-- **THE S2/S3 CHECKER LEAF** — chain invariants at the start ⇒
both checks' false-delta on every reachable final net, through the
interface premise. -/
theorem s23_leaf {ldr tm : Nat} {certified : Nat → Prop}
    {N₀ Nf : HNet} (h0 : HistInv ldr tm N₀)
    (hr : Star (HStep ldr tm certified) N₀ Nf)
    {violS2 violS3 : Prop}
    (hIface : S23CheckerInterface Nf violS2 violS3) :
    ¬ violS2 ∧ ¬ violS3 := by
  have hI := histInv_reachable h0 hr
  constructor
  · intro hv
    obtain ⟨i, j, e, e', he, he', hidx, hne⟩ := hIface.s2Sound hv
    exact hne (s2_of_histInv hI he he' hidx)
  · intro hv
    obtain ⟨i, p, q, ep, eq, hpq, hp, hq, hbad⟩ := hIface.s3Sound hv
    obtain ⟨h1, h2⟩ := s3_of_histInv hI hpq hp hq
    omega

end GoLean.RaftSeam.NativeSpec
