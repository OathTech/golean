import GoLeanProofs.LangD

/-!
# `ProgressExecC` at ∀-heap strength for the spawning witness (P-S4-1)

The safety half of the recorded S4 debt
(`docs/2026-08-10_gospecc-decomposition.md` §9 first bullet, parking
ledger P-S4-1; proof route `docs/2026-08-11_channel-protocol-layer.md`
§5): the spawn-noop program's pool run is HEAP-BLIND — every step either
thread takes (goStmt entry, the nullary callee eval, `spawnStep` on a
no-arg/no-decl/no-result worker, the `.spawned` strip, the empty-seqn
walk, the empty `frameFall`) neither reads nor writes the heap and
preserves the shared state verbatim. So from ANY admissible
`InitialSplit` state — the heap and allocator fully symbolic — the
reachable pool set is a FINITE family of thread-shape stages over the
CONSTANT shared seed, and safety is an invariant induction over
`execProgLoop`:

- `Stage` enumerates main's chain (5 configs) × the child's
  (absent ∪ 4 configs), with `cur ∈ {0, 1}`;
- per stage: `stepMulti` computes (both L1 picks at the one
  two-runnable boundary stay in the family), `raceUpdate` is
  conflict-free (every footprint is empty — `stepAccesses` returns `[]`
  on every stage config, `dispatchAccesses` is empty on a method-free
  table, and the spawn edge is the pure clock op `RaceState.spawn`),
  no stage is blocked (`runnableIdxs` nonempty while main is
  non-terminal), and no stage panics;
- fuel induction through `execProgLoop_unfold` closes the run set to
  exactly `.ok (.normal …)` and `.error .fuelOut`.

This is the pool-reachability kit's FIRST instance, deliberately built
CONCRETE (per-program stage enumeration) rather than as a generic kit —
the S4 note's §5 generic form grows from instances, not ahead of them.
`spawnNoopSpecC` below assembles the owed `GoSpecC`.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface

namespace GoLean.Iris

/-! ## The stage family

Main's chain: spawn-statement entry → callee eval → the completed spawn
position → the post-spawn marker → the terminal. The child's chain:
frame-entry body → the spliced empty sequence → the frame fall → the
terminal. The shared state is the CONSTANT seed throughout — every
transition below is proved as a definitional equation with `heap` and
`nextAddr` symbolic. -/

/-- Main stage 0: `.exec (go noopWorker()) [] .stop` — the initial pool. -/
private def mainExec : Config := .exec spawnNoopProg [] .stop
/-- Main stage 1: the callee literal under evaluation (goStmt entry). -/
private def mainEval : Config :=
  .evalE (.funcVal ⟨"noopWorker"⟩ #[]) [] (.goCalleeK [] [] .stop)
/-- Main stage 2: the completed spawn position (a registry boundary). -/
private def mainSpawnPos : Config :=
  .retV (.funcVal ⟨"noopWorker"⟩ []) (.goCalleeK [] [] .stop)
/-- Main stage 3: the post-spawn marker (BUG-040's own boundary). -/
private def mainMarker : Config := .spawned .stop
/-- Main stage 4: the `.normal` terminal. -/
private def mainDone : Config := .next .stop

/-- Child stage 0: the worker body under its barrier frame (`spawnStep`'s
child for a no-arg, no-result, non-wrapper worker). -/
private def childEntry : Config :=
  .exec (.seqn #[]) [] (.frame [] [] [] [] .stop false)
/-- Child stage 1: the spliced (empty) sequence. -/
private def childSeq : Config :=
  .next (.seq [] [] (.frame [] [] [] [] .stop false))
/-- Child stage 2: the empty frame fall. -/
private def childFall : Config := .next (.frame [] [] [] [] .stop false)
/-- Child stage 3: the child's terminal (a tombstone — not runnable). -/
private def childDone : Config := .next .stop

/-- The ∀-heap seed: exactly `ProgressExecC`'s state record, `heap` and
`nextAddr` symbolic. Everything below reduces definitionally over it —
no stage transition inspects either field. -/
private def seedState (hp : Heap) (na : Nat) : ExecState :=
  { types := [], functions := #[noopWorker], methods := #[],
    heap := hp, nextAddr := na }

/-- The reachable-stage invariant: before the fork, main alone in one of
its first three stages; after, main ∈ {marker, terminal} × child in its
four-stage chain, the running goroutine one of the two. Deliberately a
little GENEROUS (a few stage combinations are unreachable — e.g. the
marker beside a finished child at `cur = 0`) — harmless, since every
member steps back into the family. -/
private inductive Stage (hp : Heap) (na : Nat) : MultiConfig → Prop where
  | pre {c : Config} (h : c = mainExec ∨ c = mainEval ∨ c = mainSpawnPos) :
      Stage hp na ⟨#[c], seedState hp na, 0⟩
  | post {mc cc : Config} {cur : Nat}
      (hmc : mc = mainMarker ∨ mc = mainDone)
      (hcc : cc = childEntry ∨ cc = childSeq ∨ cc = childFall ∨ cc = childDone)
      (hcur : cur = 0 ∨ cur = 1) :
      Stage hp na ⟨#[mc, cc], seedState hp na, cur⟩

/-! ## One-unfold equations for `execProgLoop`, hypothesis-driven

Generic single-layer reductions of the detecting loop, each taking the
classification scrutinees as EQUATIONS (discharged by `rfl` at every
concrete stage). This keeps every stage case a rewrite chain — no
reliance on deep definitional unfolding inside the induction. -/

/-- The L1/L5 pick is 2-bounded: `Choices.consume _ 2` yields 0 or 1. -/
private theorem consume_two (ch : Choices) {pick : Nat} {ch₁ : Choices}
    (h : ch.consume 2 = (pick, ch₁)) : pick = 0 ∨ pick = 1 := by
  cases ch with
  | nil => simp [Choices.consume] at h; omega
  | cons c rest => simp [Choices.consume] at h; omega

/-- Zero fuel at a live (main-non-terminal, runnable) pool: `.fuelOut`. -/
private theorem loop_zero_eq {m : MultiConfig} (r : RaceState) (ch : Choices)
    (hne : m.threads.isEmpty = false)
    (hpanic : m.panicMsg? = none)
    (hmain : m.mainOutcome? = none)
    (hrun : (runnableIdxs m.shared m.threads).isEmpty = false) :
    execProgLoop 0 m r ch = .error .fuelOut := by
  rw [execProgLoop_unfold]
  simp only [hne, Bool.false_eq_true, reduceIte, hpanic, hmain, hrun]
  rfl

/-- Main terminal, nothing else runnable: the run returns. -/
private theorem loop_exit_eq {m : MultiConfig} {out : ExecOutcome}
    (fuel : Nat) (r : RaceState) (ch : Choices)
    (hne : m.threads.isEmpty = false)
    (hpanic : m.panicMsg? = none)
    (hout : m.mainOutcome? = some out)
    (hrun : runnableIdxs m.shared m.threads = []) :
    execProgLoop fuel m r ch = .ok (out, ch) := by
  rw [execProgLoop_unfold]
  simp only [hne, Bool.false_eq_true, reduceIte, hpanic, hout, hrun]
  rfl

/-- The step case: a live pool at `fuel + 1` steps (`stepMulti`), the
detector rides along (`raceUpdate`), and the loop recurses — with both
outcomes supplied as equations. -/
private theorem run_step {m m' : MultiConfig} {r' : RaceState} {ch' : Choices}
    (fuel : Nat) (r : RaceState) (ch : Choices)
    (hne : m.threads.isEmpty = false)
    (hpanic : m.panicMsg? = none)
    (hmain : m.mainOutcome? = none)
    (hrun : (runnableIdxs m.shared m.threads).isEmpty = false)
    (hsm : stepMulti m ch = .ok (m', ch'))
    (hru : raceUpdate m.shared m.threads ch m' r = .ok r') :
    execProgLoop (fuel + 1) m r ch = execProgLoop fuel m' r' ch' := by
  rw [execProgLoop_unfold]
  simp only [hne, Bool.false_eq_true, reduceIte, hpanic, hmain, hrun, hsm]
  simp only [Bind.bind, Except.bind]
  rw [hru]

/-- The L5 main-exit window, exit pick (0): the run returns with the
consumed stream. Any fuel — the window classifies BEFORE the fuel check. -/
private theorem window_exit {m : MultiConfig} {out : ExecOutcome}
    {pick : Nat} {ch₁ : Choices} {i : Nat} {is : List Nat}
    (fuel : Nat) (r : RaceState) (ch : Choices)
    (hne : m.threads.isEmpty = false)
    (hpanic : m.panicMsg? = none)
    (hout : m.mainOutcome? = some out)
    (hrun : runnableIdxs m.shared m.threads = i :: is)
    (hcs : ch.consume 2 = (pick, ch₁))
    (hpk : (pick == 0) = true) :
    execProgLoop fuel m r ch = .ok (out, ch₁) := by
  rw [execProgLoop_unfold]
  simp only [hne, Bool.false_eq_true, reduceIte, hpanic, hout, hrun,
    hcs, hpk]
  rfl

/-- The L5 window, continue pick (≠ 0), zero fuel: `.fuelOut` — the one
allowed exhaustion class at main's terminal (child still running). -/
private theorem window_zero {m : MultiConfig} {out : ExecOutcome}
    {pick : Nat} {ch₁ : Choices} {i : Nat} {is : List Nat}
    (r : RaceState) (ch : Choices)
    (hne : m.threads.isEmpty = false)
    (hpanic : m.panicMsg? = none)
    (hout : m.mainOutcome? = some out)
    (hrun : runnableIdxs m.shared m.threads = i :: is)
    (hcs : ch.consume 2 = (pick, ch₁))
    (hpk : (pick == 0) = false) :
    execProgLoop 0 m r ch = .error .fuelOut := by
  rw [execProgLoop_unfold]
  simp only [hne, Bool.false_eq_true, reduceIte, hpanic, hout, hrun,
    hcs, hpk]
  rfl

/-- The L5 window, continue pick (≠ 0), positive fuel: one ordinary pool
step on the CONSUMED stream, then recurse. -/
private theorem window_continue {m m' : MultiConfig} {out : ExecOutcome}
    {pick : Nat} {ch₁ ch' : Choices} {r' : RaceState} {i : Nat} {is : List Nat}
    (fuel : Nat) (r : RaceState) (ch : Choices)
    (hne : m.threads.isEmpty = false)
    (hpanic : m.panicMsg? = none)
    (hout : m.mainOutcome? = some out)
    (hrun : runnableIdxs m.shared m.threads = i :: is)
    (hcs : ch.consume 2 = (pick, ch₁))
    (hpk : (pick == 0) = false)
    (hsm : stepMulti m ch₁ = .ok (m', ch'))
    (hru : raceUpdate m.shared m.threads ch₁ m' r = .ok r') :
    execProgLoop (fuel + 1) m r ch = execProgLoop fuel m' r' ch' := by
  rw [execProgLoop_unfold]
  simp only [hne, Bool.false_eq_true, reduceIte, hpanic, hout, hrun,
    hcs, hpk, hsm]
  simp only [Bind.bind, Except.bind]
  rw [hru]

/-! ## One-step equations for `stepMulti`, hypothesis-driven -/

/-- A non-boundary running goroutine steps privately. -/
private theorem stepMulti_private {m : MultiConfig} {c₀ : Config}
    (ch : Choices)
    (hc : m.threads[m.cur]? = some c₀)
    (hb : c₀.atBoundary = false) :
    stepMulti m ch = stepThreadInto m m.cur ch := by
  unfold stepMulti
  simp only [hc, hb, Bool.false_eq_true, reduceIte]

/-- A boundary with exactly one runnable goroutine: it steps, the L1
site consumes nothing. -/
private theorem stepMulti_single {m : MultiConfig} {c₀ : Config} {i : Nat}
    (ch : Choices)
    (hc : m.threads[m.cur]? = some c₀)
    (hb : c₀.atBoundary = true)
    (hrs : runnableIdxs m.shared m.threads = [i]) :
    stepMulti m ch = stepThreadInto m i ch := by
  unfold stepMulti
  simp only [hc, hb, hrs, reduceIte]

/-- A boundary with exactly two runnable goroutines: the L1 pick is
consumed (bound 2) and selects between them. -/
private theorem stepMulti_pair {m : MultiConfig} {c₀ : Config} {a b : Nat}
    {pick : Nat} {ch₁ : Choices} (ch : Choices)
    (hc : m.threads[m.cur]? = some c₀)
    (hb : c₀.atBoundary = true)
    (hrs : runnableIdxs m.shared m.threads = [a, b])
    (hcs : ch.consume 2 = (pick, ch₁))
    (hpk : pick < 2) :
    stepMulti m ch = stepThreadInto m (if pick = 0 then a else b) ch₁ := by
  unfold stepMulti
  simp only [hc, hb, hrs, reduceIte, List.length_cons, List.length_nil]
  rw [hcs]
  have h2 : pick = 0 ∨ pick = 1 := by omega
  rcases h2 with rfl | rfl <;> simp

/-! ## The invariant induction -/

set_option maxHeartbeats 1600000 in
/-- Every `Stage` pool, under every fuel, race state, and choice stream,
runs to `.ok (.normal …)` or `.error .fuelOut` — the invariant induction
over the detecting loop. Quantifying the `RaceState` is what lets the
induction recurse through the spawn edge's clock op; every detector arm
taken returns `.ok` because every stage footprint is empty. -/
private theorem stage_progress (hp : Heap) (na : Nat) :
    ∀ (fuel : Nat) (m : MultiConfig), Stage hp na m →
      ∀ (r : RaceState) (ch : Choices),
        (∃ (σf : ExecState) (ch' : Choices),
            execProgLoop fuel m r ch = .ok (.normal σf, ch'))
          ∨ execProgLoop fuel m r ch = .error .fuelOut := by
  intro fuel
  induction fuel with
  | zero =>
    intro m hm r ch
    cases hm with
    | pre h =>
      rcases h with rfl | rfl | rfl <;>
        exact .inr (loop_zero_eq r ch rfl rfl rfl rfl)
    | post hmc hcc hcur =>
      rcases hmc with rfl | rfl
      · -- main non-terminal (the marker): fuel out
        rcases hcc with rfl | rfl | rfl | rfl <;>
          exact .inr (loop_zero_eq r ch rfl rfl rfl rfl)
      · -- main terminal: exit, or the L5 window at zero fuel
        rcases hcc with rfl | rfl | rfl | rfl
        · -- childEntry: window
          obtain ⟨pick, ch₁, hcs⟩ :
              ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
          rcases consume_two ch hcs with rfl | rfl
          · exact .inl ⟨seedState hp na, ch₁,
              window_exit 0 r ch rfl rfl rfl rfl hcs rfl⟩
          · exact .inr (window_zero r ch rfl rfl rfl rfl hcs rfl)
        · -- childSeq: window
          obtain ⟨pick, ch₁, hcs⟩ :
              ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
          rcases consume_two ch hcs with rfl | rfl
          · exact .inl ⟨seedState hp na, ch₁,
              window_exit 0 r ch rfl rfl rfl rfl hcs rfl⟩
          · exact .inr (window_zero r ch rfl rfl rfl rfl hcs rfl)
        · -- childFall: window
          obtain ⟨pick, ch₁, hcs⟩ :
              ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
          rcases consume_two ch hcs with rfl | rfl
          · exact .inl ⟨seedState hp na, ch₁,
              window_exit 0 r ch rfl rfl rfl rfl hcs rfl⟩
          · exact .inr (window_zero r ch rfl rfl rfl rfl hcs rfl)
        · -- childDone: clean exit
          exact .inl ⟨seedState hp na, ch,
            loop_exit_eq 0 r ch rfl rfl rfl rfl⟩
  | succ fuel ih =>
    intro m hm r ch
    cases hm with
    | pre h =>
      rcases h with rfl | rfl | rfl
      · -- goStmt entry (private step)
        rw [run_step fuel r ch rfl rfl rfl rfl
          (show stepMulti ⟨#[mainExec], seedState hp na, 0⟩ ch
              = .ok (⟨#[mainEval], seedState hp na, 0⟩, ch) from rfl) rfl]
        exact ih _ (.pre (.inr (.inl rfl))) r ch
      · -- nullary callee eval (private step)
        rw [run_step fuel r ch rfl rfl rfl rfl
          (show stepMulti ⟨#[mainEval], seedState hp na, 0⟩ ch
              = .ok (⟨#[mainSpawnPos], seedState hp na, 0⟩, ch) from rfl) rfl]
        exact ih _ (.pre (.inr (.inr rfl))) r ch
      · -- THE FORK: single-runnable boundary; state unchanged; the
        -- detector takes the spawn clock edge (empty dispatch footprint)
        rw [run_step fuel r ch rfl rfl rfl rfl
          (show stepMulti ⟨#[mainSpawnPos], seedState hp na, 0⟩ ch
              = .ok (⟨#[mainMarker, childEntry], seedState hp na, 0⟩, ch)
            from rfl)
          (show raceUpdate (seedState hp na) #[mainSpawnPos] ch
              ⟨#[mainMarker, childEntry], seedState hp na, 0⟩ r
              = .ok (r.spawn 0 1) from rfl)]
        exact ih _ (.post (.inl rfl) (.inl rfl) (.inl rfl)) (r.spawn 0 1) ch
    | post hmc hcc hcur =>
      rcases hmc with rfl | rfl
      · -- main at the marker (non-terminal)
        rcases hcur with rfl | rfl
        · -- cur = 0: the marker is a boundary
          rcases hcc with rfl | rfl | rfl | rfl
          · -- childEntry: the ONE two-runnable boundary — the L1 pick
            obtain ⟨pick, ch₁, hcs⟩ :
                ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
            rcases consume_two ch hcs with rfl | rfl
            · -- pick 0: strip the marker
              rw [run_step fuel r ch rfl rfl rfl rfl
                ((stepMulti_pair ch rfl rfl rfl hcs (by omega)).trans
                  (show stepThreadInto
                      ⟨#[mainMarker, childEntry], seedState hp na, 0⟩ 0 ch₁
                      = .ok (⟨#[mainDone, childEntry], seedState hp na, 0⟩,
                          ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inl rfl) (.inl rfl)) r ch₁
            · -- pick 1: the child steps
              rw [run_step fuel r ch rfl rfl rfl rfl
                ((stepMulti_pair ch rfl rfl rfl hcs (by omega)).trans
                  (show stepThreadInto
                      ⟨#[mainMarker, childEntry], seedState hp na, 0⟩ 1 ch₁
                      = .ok (⟨#[mainMarker, childSeq], seedState hp na, 1⟩,
                          ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inl rfl) (.inr (.inl rfl)) (.inr rfl)) r ch₁
          · -- childSeq: the L1 pick
            obtain ⟨pick, ch₁, hcs⟩ :
                ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
            rcases consume_two ch hcs with rfl | rfl
            · rw [run_step fuel r ch rfl rfl rfl rfl
                ((stepMulti_pair ch rfl rfl rfl hcs (by omega)).trans
                  (show stepThreadInto
                      ⟨#[mainMarker, childSeq], seedState hp na, 0⟩ 0 ch₁
                      = .ok (⟨#[mainDone, childSeq], seedState hp na, 0⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inl rfl)) (.inl rfl)) r ch₁
            · rw [run_step fuel r ch rfl rfl rfl rfl
                ((stepMulti_pair ch rfl rfl rfl hcs (by omega)).trans
                  (show stepThreadInto
                      ⟨#[mainMarker, childSeq], seedState hp na, 0⟩ 1 ch₁
                      = .ok (⟨#[mainMarker, childFall], seedState hp na, 1⟩,
                          ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inl rfl) (.inr (.inr (.inl rfl))) (.inr rfl))
                r ch₁
          · -- childFall: the L1 pick
            obtain ⟨pick, ch₁, hcs⟩ :
                ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
            rcases consume_two ch hcs with rfl | rfl
            · rw [run_step fuel r ch rfl rfl rfl rfl
                ((stepMulti_pair ch rfl rfl rfl hcs (by omega)).trans
                  (show stepThreadInto
                      ⟨#[mainMarker, childFall], seedState hp na, 0⟩ 0 ch₁
                      = .ok (⟨#[mainDone, childFall], seedState hp na, 0⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inr (.inl rfl))) (.inl rfl))
                r ch₁
            · rw [run_step fuel r ch rfl rfl rfl rfl
                ((stepMulti_pair ch rfl rfl rfl hcs (by omega)).trans
                  (show stepThreadInto
                      ⟨#[mainMarker, childFall], seedState hp na, 0⟩ 1 ch₁
                      = .ok (⟨#[mainMarker, childDone], seedState hp na, 1⟩,
                          ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inl rfl) (.inr (.inr (.inr rfl))) (.inr rfl))
                r ch₁
          · -- childDone: single-runnable, the marker strips
            rw [run_step fuel r ch rfl rfl rfl rfl
              ((stepMulti_single ch rfl rfl rfl).trans
                (show stepThreadInto
                    ⟨#[mainMarker, childDone], seedState hp na, 0⟩ 0 ch
                    = .ok (⟨#[mainDone, childDone], seedState hp na, 0⟩, ch)
                  from rfl)) rfl]
            exact ih _ (.post (.inr rfl) (.inr (.inr (.inr rfl))) (.inl rfl))
              r ch
        · -- cur = 1: the child runs
          rcases hcc with rfl | rfl | rfl | rfl
          · -- childEntry: private seqn step
            rw [run_step fuel r ch rfl rfl rfl rfl
              ((stepMulti_private ch rfl rfl).trans
                (show stepThreadInto
                    ⟨#[mainMarker, childEntry], seedState hp na, 1⟩ 1 ch
                    = .ok (⟨#[mainMarker, childSeq], seedState hp na, 1⟩, ch)
                  from rfl)) rfl]
            exact ih _ (.post (.inl rfl) (.inr (.inl rfl)) (.inr rfl)) r ch
          · -- childSeq: private seqDone step
            rw [run_step fuel r ch rfl rfl rfl rfl
              ((stepMulti_private ch rfl rfl).trans
                (show stepThreadInto
                    ⟨#[mainMarker, childSeq], seedState hp na, 1⟩ 1 ch
                    = .ok (⟨#[mainMarker, childFall], seedState hp na, 1⟩, ch)
                  from rfl)) rfl]
            exact ih _ (.post (.inl rfl) (.inr (.inr (.inl rfl))) (.inr rfl))
              r ch
          · -- childFall: private frameFall step
            rw [run_step fuel r ch rfl rfl rfl rfl
              ((stepMulti_private ch rfl rfl).trans
                (show stepThreadInto
                    ⟨#[mainMarker, childFall], seedState hp na, 1⟩ 1 ch
                    = .ok (⟨#[mainMarker, childDone], seedState hp na, 1⟩, ch)
                  from rfl)) rfl]
            exact ih _ (.post (.inl rfl) (.inr (.inr (.inr rfl))) (.inr rfl))
              r ch
          · -- childDone at cur = 1: its terminal is a boundary; only the
            -- marker is runnable — it strips
            rw [run_step fuel r ch rfl rfl rfl rfl
              ((stepMulti_single ch rfl rfl rfl).trans
                (show stepThreadInto
                    ⟨#[mainMarker, childDone], seedState hp na, 1⟩ 0 ch
                    = .ok (⟨#[mainDone, childDone], seedState hp na, 0⟩, ch)
                  from rfl)) rfl]
            exact ih _ (.post (.inr rfl) (.inr (.inr (.inr rfl))) (.inl rfl))
              r ch
      · -- main terminal
        rcases hcc with rfl | rfl | rfl | rfl
        · -- childEntry: the L5 window
          obtain ⟨pick, ch₁, hcs⟩ :
              ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
          rcases consume_two ch hcs with rfl | rfl
          · exact .inl ⟨seedState hp na, ch₁,
              window_exit (fuel + 1) r ch rfl rfl rfl rfl hcs rfl⟩
          · -- continue pick: the child steps (boundary route at cur = 0,
            -- private route at cur = 1 — same successor)
            rcases hcur with rfl | rfl
            · rw [window_continue fuel r ch rfl rfl rfl rfl hcs rfl
                ((stepMulti_single ch₁ rfl rfl rfl).trans
                  (show stepThreadInto
                      ⟨#[mainDone, childEntry], seedState hp na, 0⟩ 1 ch₁
                      = .ok (⟨#[mainDone, childSeq], seedState hp na, 1⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inl rfl)) (.inr rfl)) r ch₁
            · rw [window_continue fuel r ch rfl rfl rfl rfl hcs rfl
                ((stepMulti_private ch₁ rfl rfl).trans
                  (show stepThreadInto
                      ⟨#[mainDone, childEntry], seedState hp na, 1⟩ 1 ch₁
                      = .ok (⟨#[mainDone, childSeq], seedState hp na, 1⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inl rfl)) (.inr rfl)) r ch₁
        · -- childSeq: the L5 window
          obtain ⟨pick, ch₁, hcs⟩ :
              ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
          rcases consume_two ch hcs with rfl | rfl
          · exact .inl ⟨seedState hp na, ch₁,
              window_exit (fuel + 1) r ch rfl rfl rfl rfl hcs rfl⟩
          · rcases hcur with rfl | rfl
            · rw [window_continue fuel r ch rfl rfl rfl rfl hcs rfl
                ((stepMulti_single ch₁ rfl rfl rfl).trans
                  (show stepThreadInto
                      ⟨#[mainDone, childSeq], seedState hp na, 0⟩ 1 ch₁
                      = .ok (⟨#[mainDone, childFall], seedState hp na, 1⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inr (.inl rfl))) (.inr rfl))
                r ch₁
            · rw [window_continue fuel r ch rfl rfl rfl rfl hcs rfl
                ((stepMulti_private ch₁ rfl rfl).trans
                  (show stepThreadInto
                      ⟨#[mainDone, childSeq], seedState hp na, 1⟩ 1 ch₁
                      = .ok (⟨#[mainDone, childFall], seedState hp na, 1⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inr (.inl rfl))) (.inr rfl))
                r ch₁
        · -- childFall: the L5 window
          obtain ⟨pick, ch₁, hcs⟩ :
              ∃ pick ch₁, ch.consume 2 = (pick, ch₁) := ⟨_, _, rfl⟩
          rcases consume_two ch hcs with rfl | rfl
          · exact .inl ⟨seedState hp na, ch₁,
              window_exit (fuel + 1) r ch rfl rfl rfl rfl hcs rfl⟩
          · rcases hcur with rfl | rfl
            · rw [window_continue fuel r ch rfl rfl rfl rfl hcs rfl
                ((stepMulti_single ch₁ rfl rfl rfl).trans
                  (show stepThreadInto
                      ⟨#[mainDone, childFall], seedState hp na, 0⟩ 1 ch₁
                      = .ok (⟨#[mainDone, childDone], seedState hp na, 1⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inr (.inr rfl))) (.inr rfl))
                r ch₁
            · rw [window_continue fuel r ch rfl rfl rfl rfl hcs rfl
                ((stepMulti_private ch₁ rfl rfl).trans
                  (show stepThreadInto
                      ⟨#[mainDone, childFall], seedState hp na, 1⟩ 1 ch₁
                      = .ok (⟨#[mainDone, childDone], seedState hp na, 1⟩, ch₁)
                    from rfl)) rfl]
              exact ih _ (.post (.inr rfl) (.inr (.inr (.inr rfl))) (.inr rfl))
                r ch₁
        · -- childDone: clean exit
          exact .inl ⟨seedState hp na, ch,
            loop_exit_eq (fuel + 1) r ch rfl rfl rfl rfl⟩

/-! ## The exports -/

/-- **The ∀-heap safety fact in interpreter vocabulary alone** — the
whole mathematical content of `spawnNoopProgressC` below, stated
without the surface layer's split vocabulary so its axiom set is the
CONSTRUCTIVE lane's (`[propext, Quot.sound]` — checkable here; the
`ProgressExecC` form below unavoidably adds `Classical.choice` through
its STATEMENT constants, `InitialSplit`/`sat`/`heapletOf`, which are
built over `Iris.Std.PartialMap` — a pre-existing property of the
surface vocabulary, not of this proof). Over EVERY heap and allocator
bound — nothing about them is assumed, not even well-formedness; the
run is heap-blind — every fuel and every choice stream: the pool run of
`go noopWorker()` completes at main's `.normal` terminal or reports
`.fuelOut`, and nothing else. -/
theorem spawnNoopPoolProgress (hp : Heap) (na : Nat)
    (fuel : Nat) (ch : Choices) :
    (∃ (σf : ExecState) (ch' : Choices),
        execProg fuel []
          { types := [], functions := #[noopWorker], methods := #[],
            heap := hp, nextAddr := na }
          ch spawnNoopProg = .ok (.normal σf, ch'))
      ∨ execProg fuel []
          { types := [], functions := #[noopWorker], methods := #[],
            heap := hp, nextAddr := na }
          ch spawnNoopProg = .error .fuelOut :=
  stage_progress hp na fuel
    ⟨#[mainExec], seedState hp na, 0⟩ (.pre (.inl rfl)) {} ch

/-- **`ProgressExecC` at full `InitialSplit` strength for the spawning
witness** — parking item P-S4-1 paid (S4 note §9 first bullet; route:
channel-protocol note §5). For EVERY admissible initial state — the
frame heap and allocator bound fully symbolic; the `InitialSplit`
premise is not otherwise consulted, which is exactly the ∀-heap
strength — every fuel and every choice stream, the pool run of
`go noopWorker()` is `.ok (.normal …)` or `.error .fuelOut`, and
NOTHING else: no deadlock, no race refusal, no abort, on every modeled
schedule. The `.fuelOut` class includes exhaustion inside the L5
main-exit window (main terminal, the spawned child still running, a
continue pick at zero fuel) — the allowed class, per `ProgressExecC`'s
docstring. Proof: interpreter-side invariant induction over the
reachable stage family (heap-blind, state-constant) — no Iris, no
kernel enumeration; the proof layer is constructive
(`spawnNoopPoolProgress` above carries it at `[propext, Quot.sound]`;
this instantiation inherits `Classical.choice` from the `ProgressExecC`
statement vocabulary itself). -/
theorem spawnNoopProgressC :
    ProgressExecC [] #[noopWorker] #[] [] spawnNoopCell spawnNoopProg := by
  intro hp na hP F _hsplit fuel ch
  exact spawnNoopPoolProgress hp na fuel ch

/-- **The assembled `GoSpecC` on a genuinely SPAWNING program at full
`InitialSplit` strength** — the S4 note's owed debt (`GoSpecC =
GoTripleC ∧ ProgressExecC`, §9) CLOSED: `spawnNoopTripleC` (the triple
half, paid through the decomposition pipe) beside `spawnNoopProgressC`
(the safety half, the pool-reachability kit's first instance). Every
completing run delivers the harness cell with the frame intact, and
every bounded run on every schedule is safe ("every schedule" = every REGISTRY-POINT schedule — the settled S4 NPDRF caption, docs/2026-08-11_npdrf-reduction.md §6; sub-registry transfer is unproved). Axioms: the triple half
went through the Iris pipe, so this bundle sits at
`[propext, Classical.choice, Quot.sound]` — the safety half's proof
layer is constructive (`spawnNoopPoolProgress`). -/
theorem spawnNoopSpecC :
    GoSpecC [] #[noopWorker] #[] [] spawnNoopCell spawnNoopProg
      spawnNoopCell :=
  ⟨spawnNoopTripleC, spawnNoopProgressC⟩

end GoLean.Iris
