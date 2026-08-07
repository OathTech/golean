import GoLean.GoCore.Multi
import GoLean.GoCore.MachineSound

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
  `Prop`-valued definition, deliberately not a theorem — and REFUTABLE
  as written: obstruction 4 exhibits the counterexample class; the
  statement must be weakened before any proof attempt).
* the representative BOTH-MOVER lemmas (`storeLoc_root_frame`,
  `loadLoc_after_disjoint_store`) — the CROSS-ROOT half of the
  commutation core (obstruction 6 records the unproved same-root
  path-level half): a store is invisible to every access rooted at a
  different heap cell.

## SCAFFOLD STATUS (non-vacuity gate, recorded honestly)

`NPDRFReduction` is a DRAFT STATEMENT — no theorem in the repo claims
it, nothing may cite it (not even as a proof target: it is refutable
as written, obstruction 4), and the recorded weakening decision comes
before any proof effort. It is a `def`, not an axiom and not a
`sorry`. The mover lemmas below ARE proved and non-vacuous on their
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
3. **BUG-040 (the post-spawn decision point).** The coupling "programs
   outside DRF are exactly those the machine refuses" currently FAILS
   for races reachable only by preempting a sync-free post-spawn
   parent segment (the exit-no-sync class): the coarse relation has no
   child-first path there, so no coarse run executes — or detects —
   the conflicting access. `NPDRFReduction` as stated below is about
   OUTCOME equality for race-free programs; the detector-completeness
   half (fine-racy ⇒ some coarse path refuses) must additionally wait
   on BUG-040's fix.
4. **Main-exit discard (D6) — and it makes the statement below
   REFUTABLE AS WRITTEN, not merely unproven (S3 audit).** Main's
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
   the table under-approximates Go's access set (the recorded U1–U3
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
`copySlice`, `clearSlice`, `sortSlice`, frame exit's `storeMany`) is a
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

/-- The FULL-interleaving pool relation: `StepM`'s four rule classes
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
      arrivalPlan m.shared m.threads i c = .ok none →
      StepE c m.shared c' σ' efs →
      StepMFine m ⟨(m.threads.setIfInBounds i c') ++ efs.toArray, σ', i⟩
  | pair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : ExecState}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Config} :
      schedPickFine m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalPlan m.shared m.threads i c = .ok (some (bc, cs)) →
      (hidx : idx < cs.length) →
      applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'') →
      StepMFine m ⟨ts', σ'', i⟩
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
deadlock). See scaffold obstruction 4 on the `.done` state
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

/-- **THE NPDRF REDUCTION STATEMENT — DRAFT FORM, REFUTABLE AS
WRITTEN** (scaffold; see the module docstring's marking and
OBSTRUCTION 4, which exhibits the counterexample class: `.done`
compares whole joined states, and sync-free leaked goroutines make
those schedule-sensitive even race-free — so the `↔`'s ⊆ direction is
false as stated and MUST be weakened, per obstruction 4, before any
proof attempt; the mover plan (steps i–iii) is the route for the
WEAKENED form, not this one). Nothing may cite this — not even as a
proof target. The ⊇ direction is unconditional
(`stepsM_le_stepsMFine`); the detector coupling is plan step iv. -/
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

end GoLean.GoCore.Machine
