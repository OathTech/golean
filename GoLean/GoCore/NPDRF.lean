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
  two distinct goroutines whose next steps carry conflicting LABELS
  (`StepE`'s `AccessTrace` — the same emitted trace the executable
  detector folds; what that sharing does and does not buy is
  obstruction 5).
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

1. **Allocator interleaving.** Steps that ALLOCATE (`Store.alloc`)
   do not commute up to literal state equality: swapping two threads'
   allocation order permutes the addresses handed out (`nextAddr` is a
   shared counter). The reduction must be stated up to an address
   renaming (a heap isomorphism), or the machine must be refined with
   per-goroutine allocation arenas. This is why the mover lemmas below
   cover the NON-allocating store class first — `appendSlice`'s SPILL
   path (fresh backing) is exactly the allocating class.
2. **Fresh-cell insertion order — DISCHARGED BY CONSTRUCTION (dense
   heap, design-hygiene A2, 2026-09-04).** The obstruction was that two
   stores CREATING their cells (`Heap.set` on a missing key appended)
   produced permuted heap LISTS under swapped order, so commutation held
   only up to assoc-list extensional equality. On the dense heap
   (`Heap := Array HeapCell`) a store can only OVERWRITE an existing
   index (`Array.set` under the lookup's bounds proof) and only
   `Store.alloc` creates cells (`push`, obstruction 1's class), so
   two non-allocating stores to distinct roots commute up to structural
   heap equality (`Array.set` commutes at distinct indices). The mover
   statements below still carry their existing-cell/frame premises (they
   were stated before A2); the text is kept as the record.
3. **BUG-040 (the post-spawn decision point) — DISCHARGED at slice 4,
   then GENERALIZED at W3.2 slice 1 (stages C/D, 2026-08-20/21).**
   The coupling "programs outside DRF are exactly those the machine
   refuses" used to FAIL for races reachable only by preempting a
   sync-free post-spawn parent segment (the exit-no-sync class); the
   completion marker (now `.opDone`, a registry op at EVERY op
   completion — B1) and the back-edge boundaries (B2) put those
   interleavings inside the coarse path set, and the class is
   detectable (the flipped eval pins + the pool enumerator's
   both-leaves pin). The detector-completeness half no longer waits on
   it; the remaining obstructions stand on their own. NOTE (stage E):
   `StepM`/`StepMFine` and this file's statements now range over the
   WIDENED boundary set automatically — `StepMFine` already relaxed
   ALL boundaries, so the coarse-vs-fine RESIDUAL this draft measures
   SHRANK with the widening (more coarse points = closer to fine
   granularity); the weakening ruling and any proof effort remain
   slice 5's, over the new point set (the doctrine's "the reduction
   line resumes AFTER the machine widens").
4. **Main-exit discard (D6) — and it makes the statement below
   REFUTABLE AS WRITTEN, not merely unproven (S3 audit).** Main's
   terminal ends the program and discards other goroutines mid-flight,
   so the joined final state can differ across schedules even
   race-free (a leaked goroutine's private effects), and
   `PoolResult.done` carries the WHOLE `Store`. Concretely: a main
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
   (S3 audit).** Sharing the emitted trace between the detector and
   `RacyFine` makes plan step (iv)'s coupling cancel any shared
   under-approximation — that axis is real. What sharing does NOT buy:
   `¬ RacyFine` does not imply go_mem/`-race` data-race-freedom while
   the emitted trace under-approximates Go's access set (the recorded
   U2 in the module's access-discipline docstring, Ops.lean), and an
   access a step performs but the module does not emit is invisible to
   the mover route too (a step reading a
   shared cell with an empty recorded footprint would be treated as a
   both-mover it is not). The reduction's honesty therefore rides on
   the module's emission discipline (every access through an emitting
   operation), not on sharing alone.
6. **The proved movers are CROSS-ROOT only; same-root disjoint PATHS
   are unproved (S3 audit).** Both lemmas below are gated on
   `Loc.rootBase m ≠ Loc.rootBase l` — whole-cell disjointness — while
   `RacyFine`/the detector call distinct `.index`/`.field` paths under
   ONE root disjoint (`locOverlap`). So for exactly the multi-cell
   constructs named below (appendSlice in-place, copySlice,
   clearSlice, sortSlice: element writes sharing the backing root),
   the peer pairs the race semantics calls independent need a
   DIFFERENT lemma class — path-level frame lemmas through
   the leaf writes (`writeAt`) — and store/store commutation is
   unproved in any form. The proved pair covers the cross-root half
   (different variables/cells) only.
7. **The `thread` rule IS thread-local — DISCHARGED BY CONSTRUCTION
   (design-hygiene arc slice 1, B1 entry-identity stamps, 2026-09-03;
   recorded OPEN 2026-09-02 at the E9 closure's audit fix round, F4).**
   Between those dates a `mapDelete`/`clearMap` apply that proceeded
   rewrote EVERY other goroutine's continuation (`pruneForeign`,
   Multi.lean — the `produced`/`start` KEY sets of its in-flight
   `mapIterK` frames over the deleted map), a modification that
   appeared in NO `stepAccesses` footprint (the footprint table of the
   time; since C1 S2b the emitted trace), so plan step (i)'s
   "disjoint footprints commute" would have swapped a pruning step past
   a foreign ranger's pick and changed that pick's candidate set; the
   saving argument (the observing pick loads the cell the delete
   writes, so the two conflict and are HB-ordered or racy) had to ride
   as a side condition on every commutation lemma. With stamps the
   frame's sets are entry IDS, a delete is a heap write and nothing
   else, and a foreign frame learns of it at its next pick THROUGH the
   cell load already in its footprint: `StepM.thread`/`StepMFine.thread`
   again conclude `⟨(m.threads.setIfInBounds i c') ++ efs.toArray, σ', i⟩`
   with no pool rewrite, and there is no continuation-level
   pseudo-access to record. Nothing remains of this obstruction; it is
   kept in the list as the record of a thread-locality regression the
   mover route would have had to carry, and of how it was closed.

## The decomposition plan (the mover route, ICTAC 2018's shape)

(i) **Private-step frame lemmas** (this file's `storeLoc_root_frame` /
`loadLoc_after_disjoint_store` + an alloc-renaming story per
obstruction 1): two private steps of different threads with disjoint
footprints commute as state transformers.
(ii) **Per-construct coarse-step movers** (the granularity ledger's
formal successor): each multi-cell apply step (`appendSlice`,
`copySlice`, `clearSlice`, `sortSlice`) is a
fold of the frame lemmas — its whole footprint is what commutes, which
is exactly why an apply step's label is one step's trace, whole.
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

-- B7 (2026-09-17): the program context is the first explicit parameter of
-- every definition below that reads it; theorems take it implicitly
-- (`variable {ctx}` toggles).
variable (ctx : ProgramCtx)

open GoLean

/-! ## The fine-grained pool relation -/

/-- Fine scheduler latitude: ANY runnable goroutine may take the next
machine step — no registry-boundary condition. The full-interleaving
envelope the reduction compares against. -/
def schedPickFine (m : MultiConfig) (i : Nat) : Prop :=
  i ∈ runnableIdxs ctx m.shared m.threads

/-- The FULL-interleaving pool relation: `StepM`'s seven rule classes
verbatim with `schedPickFine` in place of `schedPick`. Proof
infrastructure for the reduction statement only — the executable
machine and every statement carrier stay on registry-point
`StepM`/`stepMulti`. -/
inductive StepMFine : MultiConfig → MultiConfig → AccessTrace → Prop where
  | thread {m : MultiConfig} {i : Nat} {c : Config} {c' : Config} {σ' : Store}
      {efs : List Config} {l : StepLabel} :
      schedPickFine ctx m i →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      arrivalCases ctx m.shared m.threads i c = .ok .cellPath →
      StepE ctx m.threads.size c m.shared c' σ' efs l →
      StepMFine m ⟨(m.threads.setIfInBounds i (Thread.afterStep m.shared c c'))
        ++ (efs.map (Thread.running · none)).toArray, σ', i⟩ l.trace
  | strip {m : MultiConfig} {i : Nat} {c : Config} {site : ChoiceSite} :
      schedPickFine ctx m i →
      m.threads[i]? = some (.running c (some site)) →
      StepMFine m ⟨m.threads.setIfInBounds i (.running c none), m.shared, i⟩ []
  | abort {m : MultiConfig} {i : Nat} {c : Config} {first : PanicEntry}
      {rest : List PanicEntry} {pick : Nat} {msg : String} :
      schedPickFine ctx m i →
      m.threads[i]? = some (.running c none) →
      c.abort? = some (first, rest) →
      pick < repanicCollapseWidth first rest →
      abortMsg ctx first rest pick = .ok msg →
      StepMFine m ⟨m.threads.setIfInBounds i (.aborted msg), m.shared, i⟩ []
  | pair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : Store}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Thread} {tr : AccessTrace} :
      schedPickFine ctx m i →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases ctx m.shared m.threads i c = .ok (.single bc cs) →
      (hidx : idx < cs.length) →
      applyPairing ctx m.shared m.threads i bc cs[idx] = .ok (ts', σ'', tr) →
      StepMFine m ⟨ts', σ'', i⟩ tr
  | pickPair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : Store}
      {os : List ArrivalOutcome} {sel : Nat}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Thread} {tr : AccessTrace} :
      schedPickFine ctx m i →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases ctx m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.pair bc cs) →
      (hidx : idx < cs.length) →
      applyPairing ctx m.shared m.threads i bc cs[idx] = .ok (ts', σ'', tr) →
      StepMFine m ⟨ts', σ'', i⟩ tr
  | pickCommit {m : MultiConfig} {i : Nat} {c : Config} {evs : List EvClause} {cl : EvClause}
      {env : LocalEnv} {k : Cont} {os : List ArrivalOutcome} {sel : Nat}
      {c' : Config} {σ' : Store} {trc : AccessTrace} :
      schedPickFine ctx m i →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases ctx m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.commit evs cl env k) →
      commitClause ctx m.shared env k cl = .ok (c', σ', trc) →
      StepMFine m ⟨m.threads.setIfInBounds i (Thread.afterStep m.shared c c'), σ', i⟩
        (selectPoll evs ++ trc)
  | wake {m : MultiConfig} {i : Nat} {c c' : Config} {σ' : Store} {tr : AccessTrace} :
      schedPickFine ctx m i →
      m.threads[i]? = some (.running c none) →
      isBlockedConfig c = true →
      resumeThread ctx m.shared c = .ok (c', σ', tr) →
      StepMFine m ⟨m.threads.setIfInBounds i (Thread.completed c'), σ', i⟩ tr

variable {ctx}
/-- A finished goroutine is at a registry boundary (goroutine exit is a
registry op; the abort tombstone likewise). -/
theorem threadDone_atBoundary {t : Thread} (h : threadDone t = true) :
    t.atBoundary = true := by
  cases t with
  | aborted msg => rfl
  | running c b =>
    cases b with
    | some site => simp [threadDone] at h
    | none =>
      -- B3: both are `Config.isTerminal` (the terminal shape, named once).
      simp only [threadDone] at h
      simp only [Thread.atBoundary]
      unfold Config.atBoundary
      rw [h]
      rfl

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
    (h : schedPick ctx m i) : schedPickFine ctx m i := by
  unfold schedPick at h
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at h; exact absurd h (by simp)
  | some t =>
    rw [hcur] at h
    dsimp only at h
    by_cases hb : t.atBoundary = true
    · rwa [if_pos hb] at h
    · simp only [Bool.not_eq_true] at hb
      rw [if_neg (by simp [hb])] at h
      subst h
      -- Not at a boundary: a live, unflagged goroutine whose configuration
      -- is neither done nor blocked (both would be at a boundary) —
      -- hence runnable.
      obtain ⟨c, rfl⟩ : ∃ c, t = .running c none := by
        cases t with
        | aborted msg => simp [Thread.atBoundary] at hb
        | running c b =>
          cases b with
          | some site => simp [Thread.atBoundary] at hb
          | none => exact ⟨c, rfl⟩
      simp only [Thread.atBoundary] at hb
      have hdone : c.isTerminal = false := by
        cases hd : c.isTerminal
        · rfl
        · exact absurd (threadDone_atBoundary (t := .running c none) (by simpa [threadDone] using hd))
            (by simp [Thread.atBoundary, hb])
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
theorem stepM_le_stepMFine {m m' : MultiConfig} {tr : AccessTrace} (h : StepM ctx m m' tr) :
    StepMFine ctx m m' tr := by
  cases h with
  | thread hs hti hbl hplan hstep =>
      exact StepMFine.thread (schedPick_le_fine hs) hti hbl hplan hstep
  | strip hs hti =>
      exact StepMFine.strip (schedPick_le_fine hs) hti
  | abort hs hti hab hpick hmsg =>
      exact StepMFine.abort (schedPick_le_fine hs) hti hab hpick hmsg
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

/-! ## Reachability and program results -/

variable (ctx)
/-- Reflexive-transitive closure of the registry-point pool relation. -/
inductive StepsM : MultiConfig → MultiConfig → Prop where
  | refl (m : MultiConfig) : StepsM m m
  | tail {a b c tr} : StepsM a b → StepM ctx b c tr → StepsM a c

/-- Reflexive-transitive closure of the fine pool relation. -/
inductive StepsMFine : MultiConfig → MultiConfig → Prop where
  | refl (m : MultiConfig) : StepsMFine m m
  | tail {a b c tr} : StepsMFine a b → StepMFine ctx b c tr → StepsMFine a c

variable {ctx}
theorem stepsM_le_stepsMFine {m m' : MultiConfig} (h : StepsM ctx m m') :
    StepsMFine ctx m m' := by
  induction h with
  | refl => exact .refl _
  | tail _ hstep ih => exact .tail ih (stepM_le_stepMFine hstep)

variable (ctx)
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
  | done (σ : Store)
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
          if (runnableIdxs ctx m.shared m.threads).isEmpty then
            some .deadlocked
          else none

/-- `res` is reachable from `m₀` under registry-point scheduling. -/
def ReachesM (m₀ : MultiConfig) (res : PoolResult) : Prop :=
  ∃ m, StepsM ctx m₀ m ∧ poolResult? ctx m = some res

/-- `res` is reachable from `m₀` under full interleaving. -/
def ReachesMFine (m₀ : MultiConfig) (res : PoolResult) : Prop :=
  ∃ m, StepsMFine ctx m₀ m ∧ poolResult? ctx m = some res

/-! ## The fine-semantics race -/

/-- Two LABELS conflict: some pair of ACCESSES (`traceAccesses` — the
happens-before actions are not accesses; attribution is looked through) at
overlapping keys (`ShadowKey.overlap` — path overlap under the `.data` key,
identity for the synchronization keys) whose kinds conflict
(`AccessKind.conflicts` — at least one write, not both atomic). C1 S2b:
stated over the steps' LABELS (the module's emitted `AccessTrace`), formerly
over the footprint table's `List RaceAccess`; C1 S2c: the labels carry
memory-model events, of which the accesses are compared. -/
def footprintsConflict (as bs : AccessTrace) : Prop :=
  ∃ a ∈ traceAccesses as, ∃ b ∈ traceAccesses bs,
    a.2.overlap b.2 = true ∧ a.1.conflicts b.1 = true

/-- The fine-semantics data race: some fine-reachable pool holds two
DISTINCT runnable goroutines whose next steps carry conflicting LABELS
(the classic co-enabled-conflict formulation, at our step granularity,
over the SAME emitted trace the executable detector folds
(`raceUpdate` reads `StepEvent.trace`) — one access semantics for the
statement and the tool). The next step is the goroutine's own `StepE`
from the pool's shared state: an ordinary `Step` (its label) or a spawn
(the child's frame-entry read — the label the fold attributes to the
child). Since C1 S2c a registry-op step's label carries its channel-object
/ sync-word accesses and its happens-before actions too, so a conflict here
may be a synchronization-word conflict exactly as the detector would record
it (the actions themselves never conflict). C1 S2b restatement; formerly over
the footprint table `stepAccesses`, which recorded a panicking step's
would-be accesses and ignored the spawn's read — the labels record what
the machine performed. -/
def RacyFine (m₀ : MultiConfig) : Prop :=
  ∃ m, StepsMFine ctx m₀ m ∧
    ∃ (i j : Nat) (ci cj : Config), i ≠ j ∧
      -- (C5: an unflagged live goroutine — a flagged one's next step is
      -- its boundary clear, footprint-free.)
      m.threads[i]? = some (.running ci none) ∧ m.threads[j]? = some (.running cj none) ∧
      threadRunnable ctx m.shared (.running ci none) = true
        ∧ threadRunnable ctx m.shared (.running cj none) = true ∧
      ∃ (ci' cj' : Config) (σi σj : Store) (efsi efsj : List Config) (tri trj : StepLabel),
        StepE ctx m.threads.size ci m.shared ci' σi efsi tri
          ∧ StepE ctx m.threads.size cj m.shared cj' σj efsj trj ∧
        footprintsConflict tri.trace trj.trace

/-- **DEPRECATED — UNSOUND AS STATED (RULED [USER] Mike 2026-09-18,
verbatim, relayed by the [AGENT] coordinator — cite as relayed: «We
shouldn't delete, hard to revive that way. Can we just deprecate/ mark
unsound for now?»; record `docs/2026-08-31_qrow-rulings.md`, «The
on-deck decisions ruling record (2026-09-18)», ruling (4); C1 charter
§7 D8).** The statement below is FALSE: `main` can exit with other
goroutines mid-computation and `.done` compares the WHOLE joined store,
so `ReachesMFine → ReachesM` fails on race-free programs (obstruction
4). It is kept as a `def` — not deleted, so its wording and history stay
revivable — carrying the `deprecated` attribute so that ANY use warns at
the use site; it is not to be used as a hypothesis, a proof target, or a
citation. It is RESTATED after C1's access trace exists (the fine-race
proposition `RacyFine` and `footprintsConflict` move onto the trace at
C1 S2; the weakening per obstruction 4 is its own reviewed decision).
Zero use sites at the marking (`git grep NPDRFReduction` at main
`68b261e6` = this definition and its docstrings only).

THE NPDRF REDUCTION STATEMENT — DRAFT FORM, REFUTABLE AS
WRITTEN (scaffold; see the module docstring's marking and
OBSTRUCTION 4, which exhibits the counterexample class: `.done`
compares whole joined states, and sync-free leaked goroutines make
those schedule-sensitive even race-free — so the `↔`'s ⊆ direction is
false as stated and MUST be weakened, per obstruction 4, before any
proof attempt; the mover plan (steps i–iii) is the route for the
WEAKENED form, not this one). Nothing may cite this — not even as a
proof target. The ⊇ direction is unconditional
(`stepsM_le_stepsMFine`); the detector coupling is plan step iv. -/
@[deprecated "NPDRFReduction is FALSE as stated (main can exit with other goroutines mid-computation; the whole-state comparison fails) — not to be used as a hypothesis; restated after C1's access trace" (since := "2026-09-18")]
def NPDRFReduction : Prop :=
  ∀ m₀ : MultiConfig, ¬ RacyFine ctx m₀ →
    ∀ res, ReachesMFine ctx m₀ res ↔ ReachesM ctx m₀ res

variable {ctx}
/-- The unconditional half of the reduction, proved: every
registry-point-reachable result is fine-reachable. -/
theorem reachesM_le_fine {m₀ : MultiConfig} {res : PoolResult}
    (h : ReachesM ctx m₀ res) : ReachesMFine ctx m₀ res := by
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
    ∀ {l : Loc} {s s' : Store} {v : GoValue},
      storeLoc ctx s l v = .ok s' →
      ∀ {m : Loc}, Loc.rootBase m ≠ Loc.rootBase l →
        Heap.lookup s'.heap (Loc.rootLoc m) = Heap.lookup s.heap (Loc.rootLoc m) := by
  intro l s s' v h m hne
  -- C1 S1: the store is ONE root-cell update at `l`'s root (the root-first
  -- write); every other root cell is untouched.
  have hkey : (Loc.base (Loc.rootPath l).1 : Loc) ≠ Loc.rootLoc m := by
    intro heq
    apply hne
    have h1 := congrArg Loc.rootBase heq
    simp only [Loc.rootBase, Loc.rootLoc, Loc.rootPath_fst] at h1
    exact h1.symm
  unfold storeLoc at h
  exact Store.updateCell_lookup_ne h hkey

/-- **The read mover**: a load rooted at a different cell than a store
reads the same value before and after it — a store is a both-mover
against every disjoint-rooted read. -/
theorem loadLoc_after_disjoint_store {l m : Loc} {s s' : Store}
    {v : GoValue} (h : storeLoc ctx s l v = .ok s')
    (hne : Loc.rootBase m ≠ Loc.rootBase l) :
    loadLoc ctx s' m = loadLoc ctx s m :=
  loadLoc_root_congr (storeLoc_root_frame h hne)

end GoLean.GoCore.Machine
