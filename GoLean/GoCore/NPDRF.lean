import GoLean.GoCore.Multi
import GoLean.GoCore.MachineSound
import GoLean.GoCore.MultiSound

/-!
# The NPDRF reduction obligation — statement, mover kit, and plan
(channels arc slice 3, D2+D3's recorded soundness obligation)

The design of record schedules goroutine interleaving ONLY at registry
ops (D2(a)); its soundness rests on the NPDRF-style reduction (Xiao,
Jiang, Liang, Feng, ICTAC 2018; Lipton 1975 movers; the CHESS
architecture): **data-race-free programs behave identically under
registry-point scheduling and full per-step interleaving**, with the
self-enforcing coupling that programs outside DRF are exactly those
the machine refuses (`raceDetected`). This file delivers the recorded
proof debt's STATEMENT layer and its first mover lemmas:

* `StepMFine` — the FULL-interleaving pool relation: `StepM` with the
  scheduler constraint relaxed from "switch only at registry
  boundaries" to "any runnable goroutine may take the next machine
  step". (Both relations interleave at OUR machine-step granularity;
  the machine-step ↔ Go-atomicity correspondence is the granularity
  ledger's separate, standing obligation.)
* `stepM_le_stepMFine` — PROVED: every registry-point step is a fine
  step, so coarse reachability ⊆ fine reachability unconditionally
  (the easy inclusion of the reduction).
* `RacyFine` — the fine-semantics race: some fine-reachable pool holds
  two distinct goroutines whose next private steps carry conflicting
  footprints (`stepAccesses`, Race.lean — the same footprint the
  executable detector records; what that sharing does and does not buy
  is obstruction 5).
* `NPDRFReduction` — the reduction statement in DRAFT form (a
  `Prop`-valued definition, deliberately not a theorem — and REFUTED,
  machine-checked, at slice channel-logic S4: `NPDRFReduction_refuted`
  below formalizes obstruction 4's counterexample class; the corrected
  statement is `NPDRFClassReduction` per the binding design note
  `docs/2026-08-11_npdrf-reduction.md`).
* the representative BOTH-MOVER lemmas (`storeLoc_root_frame`,
  `loadLoc_after_disjoint_store`) — the CROSS-ROOT half of the
  commutation core (obstruction 6 records the unproved same-root
  path-level half): a store is invisible to every access rooted at a
  different heap cell.

## SCAFFOLD STATUS (non-vacuity gate, recorded honestly)

`NPDRFReduction` is the ORIGINAL DRAFT STATEMENT, kept as the record
of what was refuted — `NPDRFReduction_refuted` (channel-logic S4) is
the machine-checked counterexample, so nothing may cite the draft
except that refutation. The reviewed weakening decision it waited for
is taken: `docs/2026-08-11_npdrf-reduction.md` §4 fixes the corrected
class-level statement (`NPDRFClassReduction`). It is a `def`, not an
axiom and not a `sorry`. The mover lemmas below ARE proved and non-vacuous on their
own terms (they instantiate on any two disjoint cells). Known
obstructions the eventual proof must clear, found by probing while
building this slice and sharpened by the S3 pre-merge audit (each
recorded so the proof effort
starts honest):

1. **Allocator interleaving.** Steps that ALLOCATE (`ExecState.alloc`)
   do not commute up to literal state equality: swapping two threads'
   allocation order permutes the addresses handed out (`nextAddr` is a
   shared counter). The reduction must be stated up to an address
   renaming (a heap isomorphism), or the machine must be refined with
   per-goroutine allocation arenas. This is why the mover lemmas below
   cover the NON-allocating store class first — `appendSlice`'s SPILL
   path (fresh backing) is exactly the allocating class.
2. **Fresh-cell insertion order.** Even without `nextAddr`, two stores
   that CREATE their cells (`Heap.set` on a missing key appends)
   produce permuted heap LISTS under swapped order — commutation is up
   to assoc-list extensional equality, not structural equality. The
   mover statements below therefore carry existing-cell/frame
   premises; the eventual proof should work over an extensional heap
   equivalence.
3. **BUG-040 (the post-spawn decision point) — DISCHARGED at slice 4.**
   The coupling "programs outside DRF are exactly those the machine
   refuses" used to FAIL for races reachable only by preempting a
   sync-free post-spawn parent segment (the exit-no-sync class); the
   `.spawned` marker (a registry op at spawn completion) put the
   child-first interleavings inside the coarse path set, and the class
   is detectable (the flipped eval pins + the pool enumerator's
   both-leaves pin). The detector-completeness half no longer waits on
   it; the remaining obstructions stand on their own.
4. **Main-exit discard (D6) — REFUTATION, now MACHINE-CHECKED
   (`NPDRFReduction_refuted`, channel-logic S4; originally recorded at
   the S3 audit as refutable-as-written).** Main's
   terminal ends the program and discards other goroutines mid-flight,
   so the joined final state can differ across schedules even
   race-free (a leaked goroutine's private effects), and
   `PoolResult.done` carries the WHOLE `ExecState`. Concretely: a main
   that spawns two sync-free goroutines and returns reaches, under
   fine interleaving, `.done` states with both children mid-segment —
   while the coarse relation keeps at most ONE thread mid-segment in a
   sync-free pool — so `ReachesMFine → ReachesM` FAILS on race-free
   programs and the `↔` below is false as stated. The statement must
   be WEAKENED before any proof attempt (post-state scoped to
   main-reachable locations, or main's readout only) — kept in its
   present form deliberately so the weakening is its own reviewed
   decision rather than a silent edit; nothing may cite the current
   form even as a target.
5. **Footprint completeness bears on `RacyFine`'s EXTERNAL adequacy
   (S3 audit).** Sharing `stepAccesses` between the detector and
   `RacyFine` makes plan step (iv)'s coupling cancel any shared
   under-approximation — that axis is real. What sharing does NOT buy:
   `¬ RacyFine` does not imply go_mem/`-race` data-race-freedom while
   the table under-approximates Go's access set (the recorded U1–U2
   in Race.lean's inventory), and an access a step performs but the
   table omits is invisible to the mover route too (a step reading a
   shared cell with an empty recorded footprint would be treated as a
   both-mover it is not). The reduction's honesty therefore rides on
   the inventory's completeness discipline, not on sharing alone.
6. **The proved movers are CROSS-ROOT only; same-root disjoint PATHS
   are unproved (S3 audit).** Both lemmas below are gated on
   `Loc.rootBase m ≠ Loc.rootBase l` — whole-cell disjointness — while
   `RacyFine`/the detector call distinct `.index`/`.field` paths under
   ONE root disjoint (`locOverlap`). So for exactly the multi-cell
   constructs named below (appendSlice in-place, copySlice,
   clearSlice, sortSlice: element writes sharing the backing root),
   the peer pairs the race semantics calls independent need a
   DIFFERENT lemma class — path-level frame lemmas through
   `StructFields.set`/array update — and store/store commutation is
   unproved in any form. The proved pair covers the cross-root half
   (different variables/cells) only.

## The decomposition plan (the mover route, ICTAC 2018's shape)

(i) **Private-step frame lemmas** (this file's `storeLoc_root_frame` /
`loadLoc_after_disjoint_store` + an alloc-renaming story per
obstruction 1): two private steps of different threads with disjoint
footprints commute as state transformers.
(ii) **Per-construct coarse-step movers** (the granularity ledger's
formal successor): each multi-cell apply step (`appendSlice`,
`copySlice`, `clearSlice`, `sortSlice`) is a
fold of the frame lemmas — its whole footprint is what commutes, which
is exactly why `stepAccesses` records apply steps whole.
(iii) **Normalization induction**: any fine execution of a race-free
program reorders — swapping adjacent independent steps, finitely often
— into a registry-point execution with the same result (Mazurkiewicz
trace normal form; segments become contiguous because only registry
ops fail to commute, and their ORDER is preserved).
(iv) **NPDRF equivalence**: race-freedom checked at registry
granularity (the executable detector's judgment) coincides with
`RacyFine` — the half that needs BUG-040 fixed, and the half that
makes the executable refusal the statement's gatekeeper.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-! ## The fine-grained pool relation -/

/-- Fine scheduler latitude: ANY runnable goroutine may take the next
machine step — no registry-boundary condition. The full-interleaving
envelope the reduction compares against. -/
def schedPickFine (m : MultiConfig) (i : Nat) : Prop :=
  i ∈ runnableIdxs m.shared m.threads

/-- The FULL-interleaving pool relation: `StepM`'s six rule classes
verbatim with `schedPickFine` in place of `schedPick`. Proof
infrastructure for the reduction statement only — the executable
machine and every statement carrier stay on registry-point
`StepM`/`stepMulti`. -/
inductive StepMFine : MultiConfig → MultiConfig → Prop where
  | thread {m : MultiConfig} {i : Nat} {c : Config} {c' : Config} {σ' : ExecState}
      {efs : List Config} :
      schedPickFine m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      arrivalCases m.shared m.threads i c = .ok .cellPath →
      StepE c m.shared c' σ' efs →
      StepMFine m ⟨(m.threads.setIfInBounds i c') ++ efs.toArray, σ', i⟩
  | pair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : ExecState}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Config} :
      schedPickFine m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases m.shared m.threads i c = .ok (.single bc cs) →
      (hidx : idx < cs.length) →
      applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'') →
      StepMFine m ⟨ts', σ'', i⟩
  | pickPair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : ExecState}
      {os : List ArrivalOutcome} {sel : Nat}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Config} :
      schedPickFine m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.pair bc cs) →
      (hidx : idx < cs.length) →
      applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'') →
      StepMFine m ⟨ts', σ'', i⟩
  | pickCommit {m : MultiConfig} {i : Nat} {c : Config} {cl : EvClause}
      {env : LocalEnv} {k : Cont} {os : List ArrivalOutcome} {sel : Nat}
      {c' : Config} {σ' : ExecState} :
      schedPickFine m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.commit cl env k) →
      commitClause m.shared env k cl = .ok (c', σ') →
      StepMFine m ⟨m.threads.setIfInBounds i c', σ', i⟩
  | wake {m : MultiConfig} {i : Nat} {c c' : Config} {σ' : ExecState} :
      schedPickFine m i →
      m.threads[i]? = some c →
      isBlockedConfig c = true →
      resumeThread m.shared c = .ok (c', σ') →
      StepMFine m ⟨m.threads.setIfInBounds i c', σ', i⟩
  | spawned {m : MultiConfig} {i : Nat} {k : Cont} :
      schedPickFine m i →
      m.threads[i]? = some (.spawned k) →
      StepMFine m ⟨m.threads.setIfInBounds i (.next k), m.shared, i⟩

/-- A finished goroutine's configuration is a registry boundary
(goroutine exit is a registry op). -/
theorem threadDone_atBoundary {c : Config} (h : threadDone c = true) :
    c.atBoundary = true := by
  match c, h with
  | .next .stop, _ => rfl
  | .returning .stop, _ => rfl
  | .breaking .stop, _ => rfl
  | .continuing .stop, _ => rfl
  | .panicked _, _ => rfl

/-- A parked goroutine's configuration is a registry boundary. -/
theorem isBlockedConfig_atBoundary {c : Config} (h : isBlockedConfig c = true) :
    c.atBoundary = true := by
  match c, h with
  | .blockedSend _ _ _, _ => rfl
  | .blockedRecv _ _ _ _ _, _ => rfl
  | .blockedSelect _ _ _, _ => rfl
  | .blockedSync _ _ _ _, _ => rfl

/-- A legal registry-point pick is a legal fine pick: at a boundary it
is already a runnable-set member; between boundaries the running
goroutine is running — not done, not blocked (both would be at a
boundary) — hence runnable. -/
theorem schedPick_le_fine {m : MultiConfig} {i : Nat}
    (h : schedPick m i) : schedPickFine m i := by
  unfold schedPick at h
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at h; exact absurd h (by simp)
  | some c =>
    rw [hcur] at h
    dsimp only at h
    by_cases hb : c.atBoundary = true
    · rwa [if_pos hb] at h
    · simp only [Bool.not_eq_true] at hb
      rw [if_neg (by simp [hb])] at h
      subst h
      have hdone : threadDone c = false := by
        cases hd : threadDone c
        · rfl
        · exact absurd (threadDone_atBoundary hd) (by simp [hb])
      have hbl : isBlockedConfig c = false := by
        cases hd : isBlockedConfig c
        · rfl
        · exact absurd (isBlockedConfig_atBoundary hd) (by simp [hb])
      unfold schedPickFine runnableIdxs
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · exact List.mem_range.mpr (by
          rcases Array.getElem?_eq_some_iff.mp hcur with ⟨hlt, _⟩
          exact hlt)
      · rw [hcur]
        simp [threadRunnable, hdone, hbl]

/-- **The easy inclusion of the reduction, proved**: every
registry-point pool step is a fine pool step. -/
theorem stepM_le_stepMFine {m m' : MultiConfig} (h : StepM m m') :
    StepMFine m m' := by
  cases h with
  | thread hs hti hbl hplan hstep =>
      exact StepMFine.thread (schedPick_le_fine hs) hti hbl hplan hstep
  | pair hs hti hbl hsp hplan hidx hap =>
      exact StepMFine.pair (schedPick_le_fine hs) hti hbl hsp hplan hidx hap
  | pickPair hs hti hbl hsp hplan hget hidx hap =>
      exact StepMFine.pickPair (schedPick_le_fine hs) hti hbl hsp hplan hget
        hidx hap
  | pickCommit hs hti hbl hsp hplan hget hcom =>
      exact StepMFine.pickCommit (schedPick_le_fine hs) hti hbl hsp hplan hget
        hcom
  | wake hs hti hbl hres =>
      exact StepMFine.wake (schedPick_le_fine hs) hti hbl hres
  | spawned hs hti =>
      exact StepMFine.spawned (schedPick_le_fine hs) hti

/-! ## Reachability and program results -/

/-- Reflexive-transitive closure of the registry-point pool relation. -/
inductive StepsM : MultiConfig → MultiConfig → Prop where
  | refl (m : MultiConfig) : StepsM m m
  | tail {a b c} : StepsM a b → StepM b c → StepsM a c

/-- Reflexive-transitive closure of the fine pool relation. -/
inductive StepsMFine : MultiConfig → MultiConfig → Prop where
  | refl (m : MultiConfig) : StepsMFine m m
  | tail {a b c} : StepsMFine a b → StepMFine b c → StepsMFine a c

theorem stepsM_le_stepsMFine {m m' : MultiConfig} (h : StepsM m m') :
    StepsMFine m m' := by
  induction h with
  | refl => exact .refl _
  | tail _ hstep ih => exact .tail ih (stepM_le_stepMFine hstep)

/-- A pool's terminal program result, mirroring `execProgLoop`'s
classification order (panic abort, main's terminal, the all-asleep
deadlock). Since BUG-044's main-exit window the mirror is of the
CLASSIFICATIONS, not of a unique run outcome: at a `.done`-classifiable
pool with runnable goroutines left, the driver may also CONTINUE (the
L5 window pick), so several results can be reachable from one pool —
which is what `ReachesM`'s existential already expresses (the relation
side admitted post-main-terminal steps all along; the window brought
the driver into line). See scaffold obstruction 4 on the `.done` state
comparison. -/
inductive PoolResult where
  | panicked (msg : String)
  | done (out : ExecOutcome)
  | deadlocked
  deriving Repr, BEq

/-- The result a pool CONFIGURATION classifies as, if any. -/
def poolResult? (m : MultiConfig) : Option PoolResult :=
  match m.panicMsg? with
  | some msg => some (.panicked msg)
  | none =>
      match m.mainOutcome? with
      | some out => some (.done out)
      | none =>
          if (runnableIdxs m.shared m.threads).isEmpty then
            some .deadlocked
          else none

/-- `res` is reachable from `m₀` under registry-point scheduling. -/
def ReachesM (m₀ : MultiConfig) (res : PoolResult) : Prop :=
  ∃ m, StepsM m₀ m ∧ poolResult? m = some res

/-- `res` is reachable from `m₀` under full interleaving. -/
def ReachesMFine (m₀ : MultiConfig) (res : PoolResult) : Prop :=
  ∃ m, StepsMFine m₀ m ∧ poolResult? m = some res

/-! ## The fine-semantics race -/

/-- Two footprints conflict: some overlapping access pair with at
least one write. -/
def footprintsConflict (as bs : List RaceAccess) : Prop :=
  ∃ a ∈ as, ∃ b ∈ bs, locOverlap a.2 b.2 = true ∧ (a.1 = true ∨ b.1 = true)

/-- The fine-semantics data race: some fine-reachable pool holds two
DISTINCT runnable goroutines whose next steps carry conflicting
footprints (the classic co-enabled-conflict formulation, at our step
granularity, over the SAME footprint table the executable detector
records — one access semantics for the statement and the tool).
Registry ops themselves have empty footprints (they are
synchronization, race-free by spec), so a conflict here is always a
data access. -/
def RacyFine (m₀ : MultiConfig) : Prop :=
  ∃ m, StepsMFine m₀ m ∧
    ∃ (i j : Nat) (ci cj : Config), i ≠ j ∧
      m.threads[i]? = some ci ∧ m.threads[j]? = some cj ∧
      threadRunnable m.shared ci = true ∧ threadRunnable m.shared cj = true ∧
      footprintsConflict (stepAccesses m.shared ci) (stepAccesses m.shared cj)

/-- **THE NPDRF REDUCTION STATEMENT — DRAFT FORM, REFUTED**
(`NPDRFReduction_refuted` below is the machine-checked counterexample,
channel-logic S4 — obstruction 4's class made concrete: `.done`
compares whole joined states, and sync-free leaked goroutines make
those schedule-sensitive even race-free, so the `↔`'s ⊆ direction is
false as stated). Kept as the record of what was refuted; nothing may
cite this except the refutation. The corrected citable target is
`NPDRFClassReduction` (design note §4); the ⊇ direction is
unconditional (`stepsM_le_stepsMFine`); the detector coupling is plan
step iv. -/
def NPDRFReduction : Prop :=
  ∀ m₀ : MultiConfig, ¬ RacyFine m₀ →
    ∀ res, ReachesMFine m₀ res ↔ ReachesM m₀ res

/-- The unconditional half of the reduction, proved: every
registry-point-reachable result is fine-reachable. -/
theorem reachesM_le_fine {m₀ : MultiConfig} {res : PoolResult}
    (h : ReachesM m₀ res) : ReachesMFine m₀ res := by
  obtain ⟨m, hsteps, hres⟩ := h
  exact ⟨m, stepsM_le_stepsMFine hsteps, hres⟩

/-! ## The representative both-mover lemmas (plan step i, CROSS-ROOT
half — see obstruction 6)

The store class: `storeLoc` writes exactly its ROOT heap cell, so any
access rooted at a DIFFERENT cell commutes with it. For the
non-allocating multi-cell apply steps (`appendSlice`'s in-place path,
`copySlice`, `clearSlice`, `sortSlice`, `storeMany`) this covers their
commutation against peers rooted in OTHER cells; peers at disjoint
paths under the SAME root (distinct elements/fields of one cell —
which the detector's `locOverlap` rightly calls independent) need the
unproved path-level frame lemmas of obstruction 6. -/

/-- `storeLoc` touches only its ROOT cell: every access path rooted at
a different cell looks up the same cell before and after the store.
(The allocator/type/function context is untouched by `storeLoc_shape`,
StateWf.lean.) -/
theorem storeLoc_root_frame :
    ∀ {l : Loc} {s s' : ExecState} {v : GoValue},
      storeLoc s l v = .ok s' →
      ∀ {m : Loc}, Loc.rootBase m ≠ Loc.rootBase l →
        Heap.lookup s'.heap (Loc.rootLoc m) = Heap.lookup s.heap (Loc.rootLoc m) := by
  intro l
  induction l with
  | base a =>
      intro s s' v h m hne
      have hkey : Loc.base a ≠ Loc.rootLoc m := by
        intro heq
        exact hne (by
          have := congrArg Loc.rootBase heq.symm
          simpa [Loc.rootLoc, Loc.rootBase] using this)
      unfold storeLoc at h
      split at h
      · split at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
          obtain ⟨v', _, hσ⟩ := h
          subst hσ
          exact Heap.lookup_set_ne hkey
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
          obtain ⟨v', _, hσ⟩ := h
          subst hσ
          exact Heap.lookup_set_ne hkey
      · simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        exact Heap.lookup_set_ne hkey
  | field b tid fname ih =>
      intro s s' v h m hne
      unfold storeLoc at h
      simp only [bind_eq_ok] at h
      obtain ⟨bv, hbv, h⟩ := h
      split at h
      · rename_i actual fields
        split at h
        · simp [Bind.bind, Except.bind] at h
        · simp only [Bind.bind, Except.bind] at h
          cases hset : StructFields.set fields fname v with
          | error e => rw [hset] at h; simp at h
          | ok updated =>
              rw [hset] at h
              exact ih h hne
      · simp at h
  | index b i ih =>
      intro s s' v h m hne
      unfold storeLoc at h
      simp only [bind_eq_ok] at h
      obtain ⟨bv, hbv, h⟩ := h
      split at h
      · simp only [bind_eq_ok] at h
        obtain ⟨arr, _, h⟩ := h
        exact ih h hne
      · simp at h

/-- **The read mover**: a load rooted at a different cell than a store
reads the same value before and after it — a store is a both-mover
against every disjoint-rooted read. -/
theorem loadLoc_after_disjoint_store {l m : Loc} {s s' : ExecState}
    {v : GoValue} (h : storeLoc s l v = .ok s')
    (hne : Loc.rootBase m ≠ Loc.rootBase l) :
    loadLoc s' m = loadLoc s m :=
  loadLoc_root_congr (storeLoc_root_frame h hne)

/-! ## THE REFUTATION, MACHINE-CHECKED (channel-logic S4; design note
`docs/2026-08-11_npdrf-reduction.md` §1)

Obstruction 4's counterexample class, formalized: main (goroutine 0)
already terminal beside two leaked goroutines A and B, each two
private stores to its own pre-existing cell (A: x:=1;x:=2 on cell 1,
B: y:=10;y:=20 on cell 2), no synchronization anywhere. All
cross-goroutine footprints are disjoint, so `¬ RacyFine` holds — the
premise of the draft statement is satisfied.

* FINE: step A once (x=1), then B once (y=10); main is terminal, so
  the pool classifies `.done (.normal σ)` at x=1 ∧ y=10 — BOTH leaked
  goroutines strictly mid-segment (`reachesMFine_bad`).
* COARSE: `schedPick` forces `i = cur` off boundaries, so in any
  `StepsM` run at most ONE goroutine is ever strictly mid-segment
  (`CoarseInv`: A untouched-or-complete or B untouched-or-complete,
  with the forced-continuation `cur` coupling that makes the exclusion
  inductive) — the x=1 ∧ y=10 shared state is coarse-unreachable
  (`not_reachesM_bad`).

The proof is finite-state model checking against the EXECUTABLE
machine: the fine run is built from `stepFn_sound`, and coarse
inversion routes through `stepM_complete` (every relation step is a
`stepMulti` step, which computes on the concrete pools). Every
computational ingredient was `#eval`-probed before proving (the
`#eval`-before-you-prove rule). NOTE the subtlety the derivation makes
exact (design note §1): because `StepM` admits post-main-terminal
steps and `poolResult?` classifies at every intermediate pool,
SINGLE-mid-segment `.done` states ARE coarse-reachable — the
counterexample needs TWO leaked writers; one is not enough. -/

namespace NPDRFRefutation


/-! ### The counterexample data -/

def xLoc : Loc := .base ⟨1⟩
def yLoc : Loc := .base ⟨2⟩
def refX : TargetRef := .chain (.addr xLoc) [] []
def refY : TargetRef := .chain (.addr yLoc) [] []
def cellI (n : Int) : HeapCell := ⟨some .int, .int n⟩

def sh (a b : Int) : ExecState :=
  { heap := [(xLoc, cellI a), (yLoc, cellI b)], nextAddr := 3 }

def mainDone : Config := .next .stop

def aC : Nat → Config
  | 0 => .next (.storeK [refX, refX] [.int 1, .int 2] (.seqn #[]) [] .stop)
  | 1 => .next (.storeK [refX] [.int 2] (.seqn #[]) [] .stop)
  | 2 => .next (.storeK [] [] (.seqn #[]) [] .stop)
  | 3 => .exec (.seqn #[]) [] .stop
  | 4 => .next (.seq [] [] .stop)
  | _ => .next .stop

def bC : Nat → Config
  | 0 => .next (.storeK [refY, refY] [.int 10, .int 20] (.seqn #[]) [] .stop)
  | 1 => .next (.storeK [refY] [.int 20] (.seqn #[]) [] .stop)
  | 2 => .next (.storeK [] [] (.seqn #[]) [] .stop)
  | 3 => .exec (.seqn #[]) [] .stop
  | 4 => .next (.seq [] [] .stop)
  | _ => .next .stop

/-- x's value at A-phase `k`. -/
def xv : Nat → Int
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- y's value at B-phase `l`. -/
def yv : Nat → Int
  | 0 => 0
  | 1 => 10
  | _ => 20

def pool (k l cur : Nat) : MultiConfig :=
  ⟨#[mainDone, aC k, bC l], sh (xv k) (yv l), cur⟩

def m0 : MultiConfig := pool 0 0 0
def resBad : PoolResult := .done (.normal (sh 1 10))

/-! ### Per-phase computation lemmas -/

theorem storeX1 (u w : Int) : storeLoc (sh u w) xLoc (.int 1) = .ok (sh 1 w) := by
  unfold storeLoc normalizeValueForTy typeResolutionFuel; rfl
theorem storeX2 (u w : Int) : storeLoc (sh u w) xLoc (.int 2) = .ok (sh 2 w) := by
  unfold storeLoc normalizeValueForTy typeResolutionFuel; rfl
theorem storeY10 (u w : Int) : storeLoc (sh u w) yLoc (.int 10) = .ok (sh u 10) := by
  unfold storeLoc normalizeValueForTy typeResolutionFuel; rfl
theorem storeY20 (u w : Int) : storeLoc (sh u w) yLoc (.int 20) = .ok (sh u 20) := by
  unfold storeLoc normalizeValueForTy typeResolutionFuel; rfl

/-- The value x holds after A's phase-`k` step from old value `u`. -/
def xUpd : Nat → Int → Int
  | 0, _ => 1
  | 1, _ => 2
  | _, u => u

def yUpd : Nat → Int → Int
  | 0, _ => 10
  | 1, _ => 20
  | _, w => w

theorem stepA {k : Nat} (hk : k ≤ 4) (u w : Int) (ch : Choices) :
    stepFn (sh u w) (aC k) ch = .ok (aC (k + 1), sh (xUpd k u) w, ch) := by
  match k, hk with
  | 0, _ =>
      unfold stepFn aC
      simp [storeTarget, resolveChain, valueAsLoc, refX, Bind.bind, Except.bind,
        storeX1, xUpd]
  | 1, _ =>
      unfold stepFn aC
      simp [storeTarget, resolveChain, valueAsLoc, refX, Bind.bind, Except.bind,
        storeX2, xUpd]
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem stepB {l : Nat} (hl : l ≤ 4) (u w : Int) (ch : Choices) :
    stepFn (sh u w) (bC l) ch = .ok (bC (l + 1), sh u (yUpd l w), ch) := by
  match l, hl with
  | 0, _ =>
      unfold stepFn bC
      simp [storeTarget, resolveChain, valueAsLoc, refY, Bind.bind, Except.bind,
        storeY10, yUpd]
  | 1, _ =>
      unfold stepFn bC
      simp [storeTarget, resolveChain, valueAsLoc, refY, Bind.bind, Except.bind,
        storeY20, yUpd]
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem stepDone (u w : Int) (ch : Choices) (r : Config × ExecState × Choices) :
    stepFn (sh u w) (.next .stop) ch ≠ .ok r := by
  intro h; simp [stepFn] at h

/-! ### Per-phase shape lemmas -/

theorem aC_hi {k : Nat} (hk : 5 ≤ k) : aC k = .next .stop := by
  match k, hk with
  | k + 5, _ => rfl

theorem bC_hi {l : Nat} (hl : 5 ≤ l) : bC l = .next .stop := by
  match l, hl with
  | l + 5, _ => rfl

theorem spawnPlan_aC (k : Nat) : spawnPlan (aC k) = none := by
  match k with | 0 | 1 | 2 | 3 | 4 => rfl | k + 5 => rfl
theorem spawnPlan_bC (l : Nat) : spawnPlan (bC l) = none := by
  match l with | 0 | 1 | 2 | 3 | 4 => rfl | l + 5 => rfl

theorem notBlocked_aC (k : Nat) : isBlockedConfig (aC k) = false := by
  match k with | 0 | 1 | 2 | 3 | 4 => rfl | k + 5 => rfl
theorem notBlocked_bC (l : Nat) : isBlockedConfig (bC l) = false := by
  match l with | 0 | 1 | 2 | 3 | 4 => rfl | l + 5 => rfl

theorem notSpawned_aC (k : Nat) (kk : Cont) : aC k ≠ .spawned kk := by
  match k with | 0 | 1 | 2 | 3 | 4 => simp [aC] | k + 5 => simp [aC]
theorem notSpawned_bC (l : Nat) (kk : Cont) : bC l ≠ .spawned kk := by
  match l with | 0 | 1 | 2 | 3 | 4 => simp [bC] | l + 5 => simp [bC]

theorem arrival_cellPath (s : ExecState) (ts : Array Config) (i : Nat) :
    ∀ (c : Config), (∀ v k, c ≠ .retV v k) →
      arrivalCases s ts i c = .ok .cellPath := by
  intro c hc
  unfold arrivalCases
  match c, hc with
  | .next k, _ => rfl
  | .exec st env k, _ => rfl
  | .evalE e env k, _ => rfl
  | .returning k, _ => rfl
  | .breaking k, _ => rfl
  | .continuing k, _ => rfl
  | .panicking ps k, _ => rfl
  | .panicked m, _ => rfl
  | .blockedSend a b c, _ => rfl
  | .blockedRecv a b c d e, _ => rfl
  | .blockedSelect a b c, _ => rfl
  | .blockedSync a b c d, _ => rfl
  | .spawned k, _ => rfl
  | .breakingTo lbl k, _ => rfl
  | .continuingTo lbl k, _ => rfl
  | .retV v k, h => exact absurd rfl (h v k)

theorem notRetV_aC (k : Nat) : ∀ v kk, aC k ≠ .retV v kk := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => intro v kk; simp [aC]
  | k + 5 => intro v kk; simp [aC]
theorem notRetV_bC (l : Nat) : ∀ v kk, bC l ≠ .retV v kk := by
  match l with
  | 0 | 1 | 2 | 3 | 4 => intro v kk; simp [bC]
  | l + 5 => intro v kk; simp [bC]

theorem arrival_aC (s : ExecState) (ts : Array Config) (i k : Nat) :
    arrivalCases s ts i (aC k) = .ok .cellPath :=
  arrival_cellPath s ts i _ (notRetV_aC k)
theorem arrival_bC (s : ExecState) (ts : Array Config) (i l : Nat) :
    arrivalCases s ts i (bC l) = .ok .cellPath :=
  arrival_cellPath s ts i _ (notRetV_bC l)

theorem done_aC (k : Nat) : threadDone (aC k) = decide (5 ≤ k) := by
  match k with | 0 | 1 | 2 | 3 | 4 => rfl | k + 5 => simp [aC_hi, threadDone]
theorem done_bC (l : Nat) : threadDone (bC l) = decide (5 ≤ l) := by
  match l with | 0 | 1 | 2 | 3 | 4 => rfl | l + 5 => simp [bC_hi, threadDone]

theorem boundary_aC (k : Nat) : (aC k).atBoundary = decide (5 ≤ k) := by
  match k with | 0 | 1 | 2 | 3 | 4 => rfl | k + 5 => simp [aC_hi, Config.atBoundary]
theorem boundary_bC (l : Nat) : (bC l).atBoundary = decide (5 ≤ l) := by
  match l with | 0 | 1 | 2 | 3 | 4 => rfl | l + 5 => simp [bC_hi, Config.atBoundary]

theorem runnable_aC (s : ExecState) (k : Nat) :
    threadRunnable s (aC k) = decide (k ≤ 4) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | k + 5 => simp [aC_hi, threadRunnable, threadDone, isBlockedConfig]
theorem runnable_bC (s : ExecState) (l : Nat) :
    threadRunnable s (bC l) = decide (l ≤ 4) := by
  match l with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | l + 5 => simp [bC_hi, threadRunnable, threadDone, isBlockedConfig]

theorem runnable_main (s : ExecState) : threadRunnable s mainDone = false := rfl

/-- The runnable set of any counterexample pool, computed. -/
theorem runnableIdxs_pool (k l : Nat) (s : ExecState) :
    runnableIdxs s #[mainDone, aC k, bC l]
      = (if k ≤ 4 then [1] else []) ++ (if l ≤ 4 then [2] else []) := by
  unfold runnableIdxs
  show List.filter _ [0, 1, 2] = _
  simp only [List.filter]
  rw [show (#[mainDone, aC k, bC l][0]? : Option Config) = some mainDone from rfl,
      show (#[mainDone, aC k, bC l][1]? : Option Config) = some (aC k) from rfl,
      show (#[mainDone, aC k, bC l][2]? : Option Config) = some (bC l) from rfl]
  simp [runnable_main, runnable_aC, runnable_bC]
  by_cases hk : k ≤ 4 <;> by_cases hl : l ≤ 4 <;> simp [hk, hl]

/-! ### The fine run to the bad result -/

theorem fineStep1 : StepMFine m0 (pool 1 0 1) := by
  have hstep : Step (aC 0) (sh 0 0) (aC 1) (sh 1 0) :=
    stepFn_sound (c := aC 0) (ch := []) (by
      have := stepA (k := 0) (by omega) 0 0 []
      simpa [xUpd, xv] using this)
  have h := StepMFine.thread (m := m0) (i := 1) (c := aC 0) (c' := aC 1)
    (σ' := sh 1 0) (efs := [])
    (by unfold schedPickFine m0 pool
        rw [runnableIdxs_pool]
        simp)
    rfl rfl (arrival_aC _ _ _ _) (.lift hstep)
  exact h

theorem fineStep2 : StepMFine (pool 1 0 1) (pool 1 1 2) := by
  have hstep : Step (bC 0) (sh 1 0) (bC 1) (sh 1 10) :=
    stepFn_sound (c := bC 0) (ch := []) (by
      have := stepB (l := 0) (by omega) 1 0 []
      simpa [yUpd, yv] using this)
  have h := StepMFine.thread (m := pool 1 0 1) (i := 2) (c := bC 0) (c' := bC 1)
    (σ' := sh 1 10) (efs := [])
    (by unfold schedPickFine pool
        rw [runnableIdxs_pool]
        simp)
    rfl rfl (arrival_bC _ _ _ _) (.lift hstep)
  exact h

theorem reachesMFine_bad : ReachesMFine m0 resBad :=
  ⟨pool 1 1 2, .tail (.tail (.refl m0) fineStep1) fineStep2, rfl⟩

/-! ### The fine invariant (thread shapes + sh-shaped state) and ¬RacyFine -/

/-- Every fine-reachable pool: main's tombstone beside one A-trace and
one B-trace config over an `sh`-shaped state. -/
def FineInv (m : MultiConfig) : Prop :=
  ∃ k l u w, m.threads = #[mainDone, aC k, bC l] ∧ m.shared = sh u w

theorem shape_of_mem {k l i : Nat} {c : Config}
    (hti : (#[mainDone, aC k, bC l] : Array Config)[i]? = some c) :
    (i = 0 ∧ c = mainDone) ∨ (i = 1 ∧ c = aC k) ∨ (i = 2 ∧ c = bC l) := by
  match i with
  | 0 => exact .inl ⟨rfl, by injection hti with h; exact h.symm⟩
  | 1 => exact .inr (.inl ⟨rfl, by injection hti with h; exact h.symm⟩)
  | 2 => exact .inr (.inr ⟨rfl, by injection hti with h; exact h.symm⟩)
  | i + 3 =>
      have hnone : (#[mainDone, aC k, bC l] : Array Config)[i + 3]? = none :=
        Array.getElem?_eq_none (by simp)
      rw [hnone] at hti
      cases hti

theorem arrival_main (s : ExecState) (ts : Array Config) (i : Nat) :
    arrivalCases s ts i mainDone = .ok .cellPath := rfl

theorem fineInv_step {m m' : MultiConfig} (hJ : FineInv m)
    (h : StepMFine m m') : FineInv m' := by
  obtain ⟨k, l, u, w, hts, hsh⟩ := hJ
  cases h with
  | thread hs hti hbl harr hse =>
      rename_i i c c' σ' efs
      unfold schedPickFine at hs
      rw [hts, hsh, runnableIdxs_pool] at hs
      have hi : (i = 1 ∧ k ≤ 4) ∨ (i = 2 ∧ l ≤ 4) := by
        by_cases hk : k ≤ 4 <;> by_cases hl : l ≤ 4 <;> simp [hk, hl] at hs
        · rcases hs with rfl | rfl
          · exact .inl ⟨rfl, hk⟩
          · exact .inr ⟨rfl, hl⟩
        · exact .inl ⟨hs, hk⟩
        · exact .inr ⟨hs, hl⟩
      rw [hts] at hti
      rcases hi with ⟨rfl, hk⟩ | ⟨rfl, hl⟩
      · have hc : c = aC k := by
          rw [show (#[mainDone, aC k, bC l] : Array Config)[1]? = some (aC k)
            from rfl] at hti
          injection hti with h1; exact h1.symm
        subst hc
        cases hse with
        | spawn hplan _ => rw [spawnPlan_aC] at hplan; cases hplan
        | lift hstep =>
            obtain ⟨ch, ch', hexec⟩ := step_complete hstep
            rw [hsh, stepA hk u w ch] at hexec
            have hcs : aC (k + 1) = c' ∧ sh (xUpd k u) w = σ' ∧ ch = ch' := by
              injection hexec with h1
              injection h1 with h2 h3
              injection h3 with h4 h5
              exact ⟨h2, h4, h5⟩
            obtain ⟨rfl, rfl, -⟩ := hcs
            exact ⟨k + 1, l, xUpd k u, w, by rw [hts]; rfl, rfl⟩
      · have hc : c = bC l := by
          rw [show (#[mainDone, aC k, bC l] : Array Config)[2]? = some (bC l)
            from rfl] at hti
          injection hti with h1; exact h1.symm
        subst hc
        cases hse with
        | spawn hplan _ => rw [spawnPlan_bC] at hplan; cases hplan
        | lift hstep =>
            obtain ⟨ch, ch', hexec⟩ := step_complete hstep
            rw [hsh, stepB hl u w ch] at hexec
            have hcs : bC (l + 1) = c' ∧ sh u (yUpd l w) = σ' ∧ ch = ch' := by
              injection hexec with h1
              injection h1 with h2 h3
              injection h3 with h4 h5
              exact ⟨h2, h4, h5⟩
            obtain ⟨rfl, rfl, -⟩ := hcs
            exact ⟨k, l + 1, u, yUpd l w, by rw [hts]; rfl, rfl⟩
  | pair hs hti hbl hsp harr hidx hap =>
      rw [hts] at hti
      rcases shape_of_mem hti with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [arrival_main] at harr; simp at harr
      · rw [arrival_aC] at harr; simp at harr
      · rw [arrival_bC] at harr; simp at harr
  | pickPair hs hti hbl hsp harr hget hidx hap =>
      rw [hts] at hti
      rcases shape_of_mem hti with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [arrival_main] at harr; simp at harr
      · rw [arrival_aC] at harr; simp at harr
      · rw [arrival_bC] at harr; simp at harr
  | pickCommit hs hti hbl hsp harr hget hcom =>
      rw [hts] at hti
      rcases shape_of_mem hti with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [arrival_main] at harr; simp at harr
      · rw [arrival_aC] at harr; simp at harr
      · rw [arrival_bC] at harr; simp at harr
  | wake hs hti hbl hres =>
      rw [hts] at hti
      rcases shape_of_mem hti with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [show isBlockedConfig mainDone = false from rfl] at hbl; cases hbl
      · rw [notBlocked_aC] at hbl; cases hbl
      · rw [notBlocked_bC] at hbl; cases hbl
  | spawned hs hti =>
      rename_i i kk
      rw [hts] at hti
      rcases shape_of_mem hti with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc⟩
      · exact absurd hc.symm (by simp [mainDone])
      · exact absurd hc.symm (notSpawned_aC k kk)
      · exact absurd hc.symm (notSpawned_bC l kk)

theorem fineInv_reach {m : MultiConfig} (h : StepsMFine m0 m) : FineInv m := by
  induction h with
  | refl => exact ⟨0, 0, 0, 0, rfl, rfl⟩
  | tail _ hstep ih => exact fineInv_step ih hstep

/-- Footprints of the trace configs, per phase. -/
theorem acc_aC (s : ExecState) (k : Nat) :
    stepAccesses s (aC k) = [] ∨ stepAccesses s (aC k) = [(true, xLoc)] := by
  match k with
  | 0 => right; rfl
  | 1 => right; rfl
  | 2 | 3 | 4 => left; rfl
  | k + 5 => left; rfl

theorem acc_bC (s : ExecState) (l : Nat) :
    stepAccesses s (bC l) = [] ∨ stepAccesses s (bC l) = [(true, yLoc)] := by
  match l with
  | 0 => right; rfl
  | 1 => right; rfl
  | 2 | 3 | 4 => left; rfl
  | l + 5 => left; rfl

theorem conflict_nil_l {bs : List RaceAccess} : ¬ footprintsConflict [] bs := by
  rintro ⟨a, ha, -⟩; simp at ha

theorem conflict_nil_r {as : List RaceAccess} : ¬ footprintsConflict as [] := by
  rintro ⟨a, -, b, hb, -⟩; simp at hb

theorem conflict_xy : ¬ footprintsConflict [(true, xLoc)] [(true, yLoc)] := by
  rintro ⟨a, ha, b, hb, hov, -⟩
  rw [List.mem_singleton] at ha hb
  subst ha; subst hb
  exact absurd hov (by decide)

theorem conflict_yx : ¬ footprintsConflict [(true, yLoc)] [(true, xLoc)] := by
  rintro ⟨a, ha, b, hb, hov, -⟩
  rw [List.mem_singleton] at ha hb
  subst ha; subst hb
  exact absurd hov (by decide)

theorem not_racyFine_m0 : ¬ RacyFine m0 := by
  rintro ⟨m, hsteps, i, j, ci, cj, hne, hi, hj, hri, hrj, hconf⟩
  obtain ⟨k, l, u, w, hts, hsh⟩ := fineInv_reach hsteps
  rw [hts] at hi hj
  have hM : stepAccesses m.shared mainDone = [] := rfl
  rcases shape_of_mem hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases shape_of_mem hj with ⟨hj0, rfl⟩ | ⟨hj0, rfl⟩ | ⟨hj0, rfl⟩
  · exact hne hj0.symm
  · rw [hM] at hconf; exact conflict_nil_l hconf
  · rw [hM] at hconf; exact conflict_nil_l hconf
  · rw [hM] at hconf; exact conflict_nil_r hconf
  · exact hne hj0.symm
  · rcases acc_aC m.shared k with h1 | h1 <;> rcases acc_bC m.shared l with h2 | h2 <;>
      rw [h1, h2] at hconf
    · exact conflict_nil_l hconf
    · exact conflict_nil_l hconf
    · exact conflict_nil_r hconf
    · exact conflict_xy hconf
  · rw [hM] at hconf; exact conflict_nil_r hconf
  · rcases acc_bC m.shared l with h1 | h1 <;> rcases acc_aC m.shared k with h2 | h2 <;>
      rw [h1, h2] at hconf
    · exact conflict_nil_l hconf
    · exact conflict_nil_l hconf
    · exact conflict_nil_r hconf
    · exact conflict_yx hconf
  · exact hne hj0.symm

/-! ### The coarse invariant: at most one strictly-mid-segment goroutine -/

theorem spawnedCont_aC (k : Nat) : spawnedCont (aC k) = none := by
  match k with | 0 | 1 | 2 | 3 | 4 => rfl | k + 5 => rfl
theorem spawnedCont_bC (l : Nat) : spawnedCont (bC l) = none := by
  match l with | 0 | 1 | 2 | 3 | 4 => rfl | l + 5 => rfl

theorem xv_upd {k : Nat} (hk : k ≤ 4) : xUpd k (xv k) = xv (k + 1) := by
  match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
theorem yv_upd {l : Nat} (hl : l ≤ 4) : yUpd l (yv l) = yv (l + 1) := by
  match l, hl with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl

theorem stepThread_A {k l : Nat} (hk : k ≤ 4) (ch : Choices) :
    stepThread (sh (xv k) (yv l)) #[mainDone, aC k, bC l] 1 ch
      = .ok (#[mainDone, aC (k + 1), bC l], sh (xv (k + 1)) (yv l), ch) := by
  have hstep := stepA (k := k) hk (xv k) (yv l) ch
  rw [xv_upd hk] at hstep
  unfold stepThread
  rw [show (#[mainDone, aC k, bC l][1]? : Option Config) = some (aC k) from rfl]
  simp only [notBlocked_aC, spawnedCont_aC, spawnPlan_aC, Bool.false_eq_true,
    if_false]
  unfold arrivalPlan
  rw [arrival_aC]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [hstep]
  rfl

theorem stepThread_B {k l : Nat} (hl : l ≤ 4) (ch : Choices) :
    stepThread (sh (xv k) (yv l)) #[mainDone, aC k, bC l] 2 ch
      = .ok (#[mainDone, aC k, bC (l + 1)], sh (xv k) (yv (l + 1)), ch) := by
  have hstep := stepB (l := l) hl (xv k) (yv l) ch
  rw [yv_upd hl] at hstep
  unfold stepThread
  rw [show (#[mainDone, aC k, bC l][2]? : Option Config) = some (bC l) from rfl]
  simp only [notBlocked_bC, spawnedCont_bC, spawnPlan_bC, Bool.false_eq_true,
    if_false]
  unfold arrivalPlan
  rw [arrival_bC]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [hstep]
  rfl

theorem stepThreadInto_A {k l cur : Nat} (hk : k ≤ 4) (ch : Choices) :
    stepThreadInto (pool k l cur) 1 ch = .ok (pool (k + 1) l 1, ch) := by
  unfold stepThreadInto pool
  simp only [Bind.bind, Except.bind]
  rw [stepThread_A hk]
  rfl

theorem stepThreadInto_B {k l cur : Nat} (hl : l ≤ 4) (ch : Choices) :
    stepThreadInto (pool k l cur) 2 ch = .ok (pool k (l + 1) 2, ch) := by
  unfold stepThreadInto pool
  simp only [Bind.bind, Except.bind]
  rw [stepThread_B hl]
  rfl

/-- `stepMulti` at a boundary with both A and B runnable, per the
stream head. -/
theorem stepMulti_both_nil {k l cur : Nat} (hb :
      ((#[mainDone, aC k, bC l] : Array Config)[cur]?).map Config.atBoundary
        = some true)
    (hk : k ≤ 4) (hl : l ≤ 4) :
    stepMulti (pool k l cur) [] = .ok (pool (k + 1) l 1, []) := by
  unfold stepMulti
  match hcur : (#[mainDone, aC k, bC l] : Array Config)[cur]? with
  | none => rw [hcur] at hb; cases hb
  | some c =>
      rw [hcur] at hb
      simp only [Option.map, Option.some.injEq] at hb
      show (if c.atBoundary then _ else _) = _
      rw [hb, if_pos rfl]
      rw [show (pool k l cur).shared = sh (xv k) (yv l) from rfl,
          show (pool k l cur).threads = #[mainDone, aC k, bC l] from rfl,
          runnableIdxs_pool, if_pos hk, if_pos hl]
      show (let (pick, ch1) := Choices.consume [] 2
            match [1, 2][pick]? with
            | some i => stepThreadInto (pool k l cur) i ch1
            | none => throw (GoError.internal "scheduler pick out of range")) = _
      simp only [Choices.consume]
      exact stepThreadInto_A hk []

theorem stepMulti_both_cons {k l cur : Nat} (hb :
      ((#[mainDone, aC k, bC l] : Array Config)[cur]?).map Config.atBoundary
        = some true)
    (hk : k ≤ 4) (hl : l ≤ 4) (c : Nat) (r : Choices) :
    stepMulti (pool k l cur) (c :: r)
      = .ok (if c % 2 = 0 then (pool (k + 1) l 1, r) else (pool k (l + 1) 2, r)) := by
  unfold stepMulti
  match hcur : (#[mainDone, aC k, bC l] : Array Config)[cur]? with
  | none => rw [hcur] at hb; cases hb
  | some cc =>
      rw [hcur] at hb
      simp only [Option.map, Option.some.injEq] at hb
      show (if cc.atBoundary then _ else _) = _
      rw [hb, if_pos rfl]
      rw [show (pool k l cur).shared = sh (xv k) (yv l) from rfl,
          show (pool k l cur).threads = #[mainDone, aC k, bC l] from rfl,
          runnableIdxs_pool, if_pos hk, if_pos hl]
      show (let (pick, ch1) := Choices.consume (c :: r) 2
            match [1, 2][pick]? with
            | some i => stepThreadInto (pool k l cur) i ch1
            | none => throw (GoError.internal "scheduler pick out of range")) = _
      simp only [Choices.consume]
      rcases Nat.mod_two_eq_zero_or_one c with hc | hc
      · rw [show c % max 1 2 = 0 from hc]
        rw [if_pos hc]
        exact stepThreadInto_A hk r
      · rw [show c % max 1 2 = 1 from hc]
        rw [if_neg (by omega)]
        exact stepThreadInto_B hl r

theorem stepMulti_Aonly {k l cur : Nat} (hb :
      ((#[mainDone, aC k, bC l] : Array Config)[cur]?).map Config.atBoundary
        = some true)
    (hk : k ≤ 4) (hl : 5 ≤ l) (ch : Choices) :
    stepMulti (pool k l cur) ch = .ok (pool (k + 1) l 1, ch) := by
  unfold stepMulti
  match hcur : (#[mainDone, aC k, bC l] : Array Config)[cur]? with
  | none => rw [hcur] at hb; cases hb
  | some cc =>
      rw [hcur] at hb
      simp only [Option.map, Option.some.injEq] at hb
      show (if cc.atBoundary then _ else _) = _
      rw [hb, if_pos rfl]
      rw [show (pool k l cur).shared = sh (xv k) (yv l) from rfl,
          show (pool k l cur).threads = #[mainDone, aC k, bC l] from rfl,
          runnableIdxs_pool, if_pos hk, if_neg (by omega)]
      exact stepThreadInto_A hk ch

theorem stepMulti_Bonly {k l cur : Nat} (hb :
      ((#[mainDone, aC k, bC l] : Array Config)[cur]?).map Config.atBoundary
        = some true)
    (hk : 5 ≤ k) (hl : l ≤ 4) (ch : Choices) :
    stepMulti (pool k l cur) ch = .ok (pool k (l + 1) 2, ch) := by
  unfold stepMulti
  match hcur : (#[mainDone, aC k, bC l] : Array Config)[cur]? with
  | none => rw [hcur] at hb; cases hb
  | some cc =>
      rw [hcur] at hb
      simp only [Option.map, Option.some.injEq] at hb
      show (if cc.atBoundary then _ else _) = _
      rw [hb, if_pos rfl]
      rw [show (pool k l cur).shared = sh (xv k) (yv l) from rfl,
          show (pool k l cur).threads = #[mainDone, aC k, bC l] from rfl,
          runnableIdxs_pool, if_neg (by omega), if_pos hl]
      exact stepThreadInto_B hl ch

theorem stepMulti_dead {k l cur : Nat} (hb :
      ((#[mainDone, aC k, bC l] : Array Config)[cur]?).map Config.atBoundary
        = some true)
    (hk : 5 ≤ k) (hl : 5 ≤ l) (ch : Choices) :
    stepMulti (pool k l cur) ch = .error .deadlock := by
  unfold stepMulti
  match hcur : (#[mainDone, aC k, bC l] : Array Config)[cur]? with
  | none => rw [hcur] at hb; cases hb
  | some cc =>
      rw [hcur] at hb
      simp only [Option.map, Option.some.injEq] at hb
      show (if cc.atBoundary then _ else _) = _
      rw [hb, if_pos rfl]
      rw [show (pool k l cur).shared = sh (xv k) (yv l) from rfl,
          show (pool k l cur).threads = #[mainDone, aC k, bC l] from rfl,
          runnableIdxs_pool, if_neg (by omega), if_neg (by omega)]
      rfl

theorem stepMulti_midA {k l : Nat} (hk : k ≤ 4) (h1 : 1 ≤ k) (ch : Choices) :
    stepMulti (pool k l 1) ch = .ok (pool (k + 1) l 1, ch) := by
  unfold stepMulti
  rw [show ((pool k l 1).threads[(pool k l 1).cur]? : Option Config)
      = some (aC k) from rfl]
  show (if (aC k).atBoundary then _ else _) = _
  rw [boundary_aC, if_neg (by simp; omega)]
  exact stepThreadInto_A hk ch

theorem stepMulti_midB {k l : Nat} (hl : l ≤ 4) (h1 : 1 ≤ l) (ch : Choices) :
    stepMulti (pool k l 2) ch = .ok (pool k (l + 1) 2, ch) := by
  unfold stepMulti
  rw [show ((pool k l 2).threads[(pool k l 2).cur]? : Option Config)
      = some (bC l) from rfl]
  show (if (bC l).atBoundary then _ else _) = _
  rw [boundary_bC, if_neg (by simp; omega)]
  exact stepThreadInto_B hl ch

theorem stepMulti_curHi {k l cur : Nat} (hcur : 3 ≤ cur) (ch : Choices) :
    stepMulti (pool k l cur) ch
      = .error (.internal "running goroutine out of range") := by
  unfold stepMulti
  rw [show ((pool k l cur).threads[(pool k l cur).cur]? : Option Config)
      = ((#[mainDone, aC k, bC l] : Array Config)[cur]? : Option Config) from rfl,
    Array.getElem?_eq_none (by simp; omega)]
  rfl

/-- The coarse reachability invariant: pools reachable under
registry-point scheduling keep at least one of A, B untouched or
complete (never BOTH strictly mid-trace), with the forced-continuation
`cur` coupling that makes the exclusion inductive. -/
def CoarseInv (m : MultiConfig) : Prop :=
  ∃ k l cur, m = pool k l cur ∧ k ≤ 5 ∧ l ≤ 5 ∧
    (k = 0 ∨ k = 5 ∨ l = 0 ∨ l = 5) ∧
    (1 ≤ k → k ≤ 4 → cur = 1) ∧ (1 ≤ l → l ≤ 4 → cur = 2) ∧
    (cur = 1 → 1 ≤ k) ∧ (cur = 2 → 1 ≤ l)

/-- CoarseInv is closed under `StepM`, via `stepM_complete` (every
relation step is an executable `stepMulti` step) and the concrete
`stepMulti` computations above. -/
theorem coarseInv_step {m m' : MultiConfig} (hR : CoarseInv m)
    (h : StepM m m') : CoarseInv m' := by
  obtain ⟨k, l, cur, rfl, hk, hl, hdisj, hmidA, hmidB, hcur1, hcur2⟩ := hR
  obtain ⟨ch, ch', hexec⟩ := stepM_complete h
  have extract : ∀ {p : MultiConfig} {r : Choices},
      (Except.ok (p, r) : Except GoError (MultiConfig × Choices))
        = .ok (m', ch') → m' = p := by
    intro p r hpr
    injection hpr with h1
    exact (congrArg Prod.fst h1).symm
  -- helper: package a successor into the invariant
  have mkA : ∀ (kk ll : Nat), kk ≤ 4 → ll ≤ 5 → (ll = 0 ∨ ll = 5) →
      CoarseInv (pool (kk + 1) ll 1) := by
    intro kk ll hkk hll hd
    exact ⟨kk + 1, ll, 1, rfl, by omega, hll, by omega,
      fun _ _ => rfl, fun h1 h4 => by omega, fun _ => by omega,
      fun h2 => by omega⟩
  have mkB : ∀ (kk ll : Nat), kk ≤ 5 → ll ≤ 4 → (kk = 0 ∨ kk = 5) →
      CoarseInv (pool kk (ll + 1) 2) := by
    intro kk ll hkk hll hd
    exact ⟨kk, ll + 1, 2, rfl, hkk, by omega, by omega,
      fun h1 h4 => by omega, fun _ _ => rfl, fun h1 => by omega,
      fun _ => by omega⟩
  match hc : cur with
  | 0 =>
      -- neither thread is strictly mid (the forced-continuation
      -- implications put cur at 1/2 there), so k, l ∈ {0, 5}
      have hk05 : k = 0 ∨ k = 5 := by
        by_cases h1 : 1 ≤ k
        · by_cases h4 : k ≤ 4
          · have := hmidA h1 h4; omega
          · omega
        · omega
      have hl05 : l = 0 ∨ l = 5 := by
        by_cases h1 : 1 ≤ l
        · by_cases h4 : l ≤ 4
          · have := hmidB h1 h4; omega
          · omega
        · omega
      have hb : ((#[mainDone, aC k, bC l] : Array Config)[0]?).map
          Config.atBoundary = some true := rfl
      rcases hk05 with rfl | rfl <;> rcases hl05 with rfl | rfl
      · -- (0,0): both runnable — stream case analysis
        match ch with
        | [] =>
            rw [stepMulti_both_nil hb (by omega) (by omega)] at hexec
            obtain rfl := extract hexec
            exact mkA 0 0 (by omega) (by omega) (.inl rfl)
        | c :: r =>
            rw [stepMulti_both_cons hb (by omega) (by omega) c r] at hexec
            rcases Nat.mod_two_eq_zero_or_one c with hc2 | hc2
            · rw [if_pos hc2] at hexec
              obtain rfl := extract hexec
              exact mkA 0 0 (by omega) (by omega) (.inl rfl)
            · rw [if_neg (by omega)] at hexec
              obtain rfl := extract hexec
              exact mkB 0 0 (by omega) (by omega) (.inl rfl)
      · -- (0,5): only A runnable
        rw [stepMulti_Aonly hb (by omega) (by omega) ch] at hexec
        obtain rfl := extract hexec
        exact mkA 0 5 (by omega) (by omega) (.inr rfl)
      · -- (5,0): only B runnable
        rw [stepMulti_Bonly hb (by omega) (by omega) ch] at hexec
        obtain rfl := extract hexec
        exact mkB 5 0 (by omega) (by omega) (.inr rfl)
      · -- (5,5): deadlocked — no step exists
        rw [stepMulti_dead hb (by omega) (by omega) ch] at hexec
        cases hexec
  | 1 =>
      have h1k : 1 ≤ k := hcur1 rfl
      by_cases h4 : k ≤ 4
      · -- A strictly mid: forced continuation
        have hlz : l = 0 ∨ l = 5 := by
          by_cases hl1 : 1 ≤ l
          · by_cases hl4 : l ≤ 4
            · have := hmidB hl1 hl4; omega
            · omega
          · omega
        rw [stepMulti_midA h4 h1k ch] at hexec
        obtain rfl := extract hexec
        exact mkA k l h4 hl hlz
      · -- k = 5: A's tombstone is a boundary — reschedule
        have hk5 : k = 5 := by omega
        subst hk5
        have hb : ((#[mainDone, aC 5, bC l] : Array Config)[1]?).map
            Config.atBoundary = some true := rfl
        by_cases hl4 : l ≤ 4
        · rw [stepMulti_Bonly hb (by omega) hl4 ch] at hexec
          obtain rfl := extract hexec
          exact mkB 5 l (by omega) hl4 (.inr rfl)
        · rw [stepMulti_dead hb (by omega) (by omega) ch] at hexec
          cases hexec
  | 2 =>
      have h1l : 1 ≤ l := hcur2 rfl
      by_cases h4 : l ≤ 4
      · have hkz : k = 0 ∨ k = 5 := by
          by_cases hk1 : 1 ≤ k
          · by_cases hk4 : k ≤ 4
            · have := hmidA hk1 hk4; omega
            · omega
          · omega
        rw [stepMulti_midB h4 h1l ch] at hexec
        obtain rfl := extract hexec
        exact mkB k l hk h4 hkz
      · have hl5 : l = 5 := by omega
        subst hl5
        have hb : ((#[mainDone, aC k, bC 5] : Array Config)[2]?).map
            Config.atBoundary = some true := rfl
        by_cases hk4 : k ≤ 4
        · rw [stepMulti_Aonly hb hk4 (by omega) ch] at hexec
          obtain rfl := extract hexec
          exact mkA k 5 hk4 (by omega) (.inr rfl)
        · rw [stepMulti_dead hb (by omega) (by omega) ch] at hexec
          cases hexec
  | cur + 3 =>
      rw [stepMulti_curHi (by omega) ch] at hexec
      cases hexec

theorem coarseInv_reach {m : MultiConfig} (h : StepsM m0 m) : CoarseInv m := by
  induction h with
  | refl =>
      exact ⟨0, 0, 0, rfl, by omega, by omega, .inl rfl,
        fun h _ => by omega, fun h _ => by omega,
        fun h => by omega, fun h => by omega⟩
  | tail _ hstep ih => exact coarseInv_step ih hstep

/-- Every counterexample pool classifies as main's `.done` over its
phase-determined shared state. -/
theorem poolResult?_pool (k l cur : Nat) :
    poolResult? (pool k l cur) = some (.done (.normal (sh (xv k) (yv l)))) := by
  rcases k with _|_|_|_|_|k <;> rcases l with _|_|_|_|_|l <;> rfl

theorem xv_eq_one {k : Nat} (h : xv k = 1) : k = 1 := by
  rcases k with _|_|k <;> simp [xv] at h ⊢
theorem yv_eq_ten {l : Nat} (h : yv l = 10) : l = 1 := by
  rcases l with _|_|l <;> simp [yv] at h ⊢

theorem not_reachesM_bad : ¬ ReachesM m0 resBad := by
  rintro ⟨m, hsteps, hres⟩
  obtain ⟨k, l, cur, rfl, hk, hl, hdisj, hmidA, hmidB, -, -⟩ :=
    coarseInv_reach hsteps
  rw [poolResult?_pool] at hres
  injection hres with h1
  injection h1 with h2
  injection h2 with h3
  -- the shared states agree, so both phase values are the bad ones
  have hxy : xv k = 1 ∧ yv l = 10 := by
    have hheap := congrArg ExecState.heap h3
    simp only [sh, cellI, List.cons.injEq, Prod.mk.injEq, HeapCell.mk.injEq,
      GoValue.int.injEq, and_true, true_and] at hheap
    exact hheap
  have hk1 : k = 1 := xv_eq_one hxy.1
  have hl1 : l = 1 := yv_eq_ten hxy.2
  subst hk1; subst hl1
  rcases hdisj with h | h | h | h <;> omega

/-- **THE REFUTATION, MACHINE-CHECKED**: the draft reduction statement
is false. -/
theorem NPDRFReduction_refuted : ¬ NPDRFReduction := fun h =>
  not_reachesM_bad ((h m0 not_racyFine_m0 resBad).mp reachesMFine_bad)

end NPDRFRefutation

export NPDRFRefutation (NPDRFReduction_refuted)

/-! ## The settled statement layer (channel-logic S4; design note §§3-5)

`BoundarySwitch`/`stepM_iff_fine_bs` characterize the gap the
refutation demonstrated; `NPDRFClassReduction` is the corrected
citable target; the never-spawning fragment is its proved instance
class. All proof infrastructure (statement-TCB: these relations and
`Prop`s never enter designated statement closures). -/

/-- The scheduling discipline that separates the coarse (registry-point)
relation from full interleaving: a pick is boundary-switched when the
RUNNING goroutine sits at a registry boundary (a reschedule is legal)
or the pick continues the running goroutine. -/
def BoundarySwitch (m : MultiConfig) (i : Nat) : Prop :=
  match m.threads[m.cur]? with
  | some c => c.atBoundary = true ∨ i = m.cur
  | none => False

theorem schedPick_iff_fine_bs {m : MultiConfig} {i : Nat} :
    schedPick m i ↔ schedPickFine m i ∧ BoundarySwitch m i := by
  constructor
  · intro h
    refine ⟨schedPick_le_fine h, ?_⟩
    unfold schedPick at h
    unfold BoundarySwitch
    cases hcur : m.threads[m.cur]? with
    | none => rw [hcur] at h; exact h
    | some c =>
        rw [hcur] at h
        dsimp only at h ⊢
        by_cases hb : c.atBoundary = true
        · exact .inl hb
        · rw [if_neg (by simp [hb])] at h; exact .inr h
  · rintro ⟨hf, hbs⟩
    unfold BoundarySwitch at hbs
    unfold schedPick
    cases hcur : m.threads[m.cur]? with
    | none => rw [hcur] at hbs; exact hbs
    | some c =>
        rw [hcur] at hbs
        dsimp only at hbs ⊢
        unfold schedPickFine at hf
        rcases hbs with hb | rfl
        · rw [if_pos hb]; exact hf
        · by_cases hb : c.atBoundary = true
          · rw [if_pos hb]; exact hf
          · rw [if_neg (by simp [hb])]

/-- The stepped goroutine of a fine step is its result's `cur`, and it
is a legal fine pick. -/
theorem stepMFine_pick {b c : MultiConfig} (h : StepMFine b c) :
    schedPickFine b c.cur := by
  cases h with
  | thread hs hti hbl harr hse => exact hs
  | pair hs hti hbl hsp harr hidx hap => exact hs
  | pickPair hs hti hbl hsp harr hget hidx hap => exact hs
  | pickCommit hs hti hbl hsp harr hget hcom => exact hs
  | wake hs hti hbl hres => exact hs
  | spawned hs hti => exact hs

/-- **The exact characterization**: the registry-point relation IS full
interleaving restricted to boundary switches. -/
theorem stepM_iff_fine_bs {m m' : MultiConfig} :
    StepM m m' ↔ StepMFine m m' ∧ BoundarySwitch m m'.cur := by
  constructor
  · intro h
    refine ⟨stepM_le_stepMFine h, ?_⟩
    cases h with
    | thread hs hti hbl harr hse => exact (schedPick_iff_fine_bs.mp hs).2
    | pair hs hti hbl hsp harr hidx hap => exact (schedPick_iff_fine_bs.mp hs).2
    | pickPair hs hti hbl hsp harr hget hidx hap =>
        exact (schedPick_iff_fine_bs.mp hs).2
    | pickCommit hs hti hbl hsp harr hget hcom =>
        exact (schedPick_iff_fine_bs.mp hs).2
    | wake hs hti hbl hres => exact (schedPick_iff_fine_bs.mp hs).2
    | spawned hs hti => exact (schedPick_iff_fine_bs.mp hs).2
  · rintro ⟨hf, hbs⟩
    cases hf with
    | thread hs hti hbl harr hse =>
        exact StepM.thread (schedPick_iff_fine_bs.mpr ⟨hs, hbs⟩) hti hbl harr hse
    | pair hs hti hbl hsp harr hidx hap =>
        exact StepM.pair (schedPick_iff_fine_bs.mpr ⟨hs, hbs⟩) hti hbl hsp harr
          hidx hap
    | pickPair hs hti hbl hsp harr hget hidx hap =>
        exact StepM.pickPair (schedPick_iff_fine_bs.mpr ⟨hs, hbs⟩) hti hbl hsp
          harr hget hidx hap
    | pickCommit hs hti hbl hsp harr hget hcom =>
        exact StepM.pickCommit (schedPick_iff_fine_bs.mpr ⟨hs, hbs⟩) hti hbl hsp
          harr hget hcom
    | wake hs hti hbl hres =>
        exact StepM.wake (schedPick_iff_fine_bs.mpr ⟨hs, hbs⟩) hti hbl hres
    | spawned hs hti =>
        exact StepM.spawned (schedPick_iff_fine_bs.mpr ⟨hs, hbs⟩) hti

/-- The boundary-switched fine closure. -/
inductive StepsMFineBS : MultiConfig → MultiConfig → Prop where
  | refl (m : MultiConfig) : StepsMFineBS m m
  | tail {a b c} : StepsMFineBS a b → StepMFine b c → BoundarySwitch b c.cur →
      StepsMFineBS a c

/-- Run-level characterization: coarse runs are exactly the
boundary-switched fine runs. -/
theorem stepsM_iff_fine_bs {m m' : MultiConfig} :
    StepsM m m' ↔ StepsMFineBS m m' := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ hstep ih =>
        obtain ⟨hf, hbs⟩ := stepM_iff_fine_bs.mp hstep
        exact .tail ih hf hbs
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ hf hbs ih => exact .tail ih (stepM_iff_fine_bs.mpr ⟨hf, hbs⟩)

/-! ### The corrected reduction statement (class level) -/

/-- Constructor-level result correspondence: the observation the
corrected reduction preserves. States and messages are deliberately
NOT compared — the design note's §2 shows allocation order makes both
schedule-sensitive even race-free (addresses embed in `.done` states,
in pointer-carrying values, and in formatted panic payloads), so any
literal comparison stays refutable; anything stronger needs the heap-
iso quotient (recorded successor machinery, note §5). -/
def PoolResult.sameClass : PoolResult → PoolResult → Bool
  | .panicked _, .panicked _ => true
  | .deadlocked, .deadlocked => true
  | .done o, .done o' =>
      match o, o' with
      | .normal _, .normal _ => true
      | .returned _, .returned _ => true
      | .broke _, .broke _ => true
      | .continued _, .continued _ => true
      | _, _ => false
  | _, _ => false

theorem PoolResult.sameClass_refl (r : PoolResult) : r.sameClass r = true := by
  cases r with
  | panicked msg => rfl
  | deadlocked => rfl
  | done o => cases o <;> rfl

/-- **THE CORRECTED NPDRF REDUCTION — the citable open target**
(design note §4; replaces the refuted draft above): a race-free pool's
fine-reachable results are coarse-reachable UP TO RESULT CLASS. Unlike
the draft, no known counterexample class applies (class-level
observation is blind to both refutation mechanisms — the mid-segment
state gap and allocation order); the truth argument and the mover-
route proof plan are the note's §4-5. SCAFFOLD DISCIPLINE: this is a
`def`, claimed by no theorem; the proved instances are the
never-spawning fragment below (`npdrfClassReduction_single_fragment`)
— nothing may cite it AS PROVED, and no ∀-schedule caption may claim
it (the caption formula's guard, note §6). The ⊇ direction is
`reachesM_le_fine` (literal, hence class-level, unconditionally). -/
def NPDRFClassReduction : Prop :=
  ∀ m₀ : MultiConfig, ¬ RacyFine m₀ →
    ∀ res, ReachesMFine m₀ res →
      ∃ res', ReachesM m₀ res' ∧ res.sameClass res' = true

/-! ### P3: the never-spawning fragment -/

theorem runnableIdxs_lt {s : ExecState} {ts : Array Config} {i : Nat}
    (h : i ∈ runnableIdxs s ts) : i < ts.size := by
  unfold runnableIdxs at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

theorem stepsMFine_to_stepsM_single {m₀ : MultiConfig}
    (hc : m₀.cur = 0)
    (hns : ∀ m, StepsMFine m₀ m → m.threads.size = 1) :
    ∀ {m}, StepsMFine m₀ m → StepsM m₀ m ∧ m.cur = 0 := by
  intro m h
  induction h with
  | refl => exact ⟨.refl _, hc⟩
  | @tail a b hab hbc ih =>
      obtain ⟨hsM, hcur⟩ := ih
      have hasize : a.threads.size = 1 := hns _ hab
      have hpick := stepMFine_pick hbc
      have hlt : b.cur < a.threads.size := runnableIdxs_lt hpick
      have hcc : b.cur = 0 := by omega
      have hbs : BoundarySwitch a b.cur := by
        unfold BoundarySwitch
        cases hcur0 : a.threads[a.cur]? with
        | none =>
            rw [Array.getElem?_eq_none_iff] at hcur0
            omega
        | some c₀ => exact .inr (by omega)
      exact ⟨.tail hsM (stepM_iff_fine_bs.mpr ⟨hbc, hbs⟩), hcc⟩

/-- **The proved fragment of the corrected reduction** (P3, design
note §5): on never-spawning pools (every fine-reachable pool still
single-threaded), fine and coarse reachability coincide LITERALLY —
strictly stronger than `NPDRFClassReduction`'s conclusion on this
class, and without the race-freedom premise (a lone thread's fine pick
is always boundary-switched: it IS the running goroutine). Honesty
rider: this is the sequential-degenerate class at relation level — the
corrected statement's genuinely CONCURRENT content (spawning programs)
remains open, gated on the note §5's blocking machinery (footprint-
frame theorem, heap iso, permutation engine). -/
theorem reachesMFine_iff_reachesM_single {m₀ : MultiConfig}
    (hc : m₀.cur = 0)
    (hns : ∀ m, StepsMFine m₀ m → m.threads.size = 1) :
    ∀ res, ReachesMFine m₀ res ↔ ReachesM m₀ res := by
  intro res
  constructor
  · rintro ⟨m, hs, hr⟩
    exact ⟨m, (stepsMFine_to_stepsM_single hc hns hs).1, hr⟩
  · exact reachesM_le_fine

/-- The corrected statement's conclusion, discharged on the fragment. -/
theorem npdrfClassReduction_single_fragment {m₀ : MultiConfig}
    (hc : m₀.cur = 0)
    (hns : ∀ m, StepsMFine m₀ m → m.threads.size = 1) :
    ∀ res, ReachesMFine m₀ res →
      ∃ res', ReachesM m₀ res' ∧ PoolResult.sameClass res res' = true :=
  fun res hr =>
    ⟨res, (reachesMFine_iff_reachesM_single hc hns res).mp hr,
      PoolResult.sameClass_refl res⟩

/-! ### Non-vacuity witness for the fragment: a concrete pool
satisfying the fragment's premises, with an inhabited result on both
sides of the proved `iff` (degenerate BY DESIGN — the fragment's value
is that the corrected statement's shape is inhabitable, not that this
pool is interesting; the honest scope note is on the fragment theorem
above). -/

def singletonTerminalPool : MultiConfig := ⟨#[.next .stop], {}, 0⟩

theorem singletonTerminal_no_step :
    ∀ m, StepsMFine singletonTerminalPool m → m = singletonTerminalPool := by
  intro m h
  induction h with
  | refl => rfl
  | @tail a b hab hbc ih =>
      subst ih
      have hpick := stepMFine_pick hbc
      have : b.cur ∈ ([] : List Nat) := hpick
      cases this

theorem fragment_witness_iff :
    ∀ res, ReachesMFine singletonTerminalPool res
      ↔ ReachesM singletonTerminalPool res :=
  reachesMFine_iff_reachesM_single rfl
    (fun m h => by rw [singletonTerminal_no_step m h]; rfl)

theorem fragment_witness_inhabited :
    ReachesM singletonTerminalPool (.done (.normal {})) :=
  ⟨singletonTerminalPool, .refl _, rfl⟩

end GoLean.GoCore.Machine
