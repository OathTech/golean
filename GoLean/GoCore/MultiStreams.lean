import GoLean.GoCore.MultiWfSound

/-!
# The pool ∀-streams kernel checker (channels arc slice 5)

The `allStreamsOk` analogue over the ThreadPool driver — the second of
the two discharge routes the slice-2 build log recorded for `GoSpecC`'s
`∀ ch` quantifier ("the concurrent WP or a pool-level ∀-streams kernel
checker"). One kernel evaluation certifies that EVERY choice stream —
schedules (L1) and data latitude together, D8's single-stream design —
runs a seeded pool to main's `.normal` terminal with a caller-chosen
Bool readout of the joined final state.

Design (mirroring the sequential checker's discipline,
`MachineSound.lean`):

* The branched sites are the L1 scheduler pick — at a boundary with
  `|runnable| > 1` the checker explores every runnable index, probing
  the REAL `stepMulti` at the singleton stream `[j]` (the consume pops
  `j`, leaving the remainder empty) — and (BUG-044) the MAIN-EXIT
  WINDOW: at main's terminal with runnable goroutines left, BOTH window
  picks must certify (exit = `post` of the readout state; continue =
  the same stepping core, recursively).
* Every OTHER consumption shape FAILS CLOSED (`false`, never unsound):
  CONSUMING select apply positions (L2 — a `consumesSelect` shape is
  accepted only when its arrival analysis is partnerless `.cellPath`
  AND its `applySelectCore` is `.done`, i.e. default/park/singleton
  commit — the spec-parity slice-4 refinement, `selectApplyDone`; a
  multi-ready or partnered select still refuses), `appendSlice`
  applies, `mapIterK` picks, and multi-candidate waiter pairings (L4
  width > 1). A program that needs a refused shape turns the checker
  false, visibly. The slice-4 CLI enumerator remains the full-width
  engine — this checker is deliberately the KERNEL-REDUCIBLE core.
* `stepThread_oblivious` is the soundness hinge: under the fail-closed
  flags (`poolThreadOblivious`), a goroutine-step that succeeds under
  one stream succeeds under EVERY stream with the same successor and
  the stream returned untouched — `stepFn_oblivious` lifted through
  the pool dispatch (wake / marker strip / spawn / singleton pairing
  are stream-free by construction).
* `raceUpdate_oblivious`: the detector's dispatcher replicates stream
  consumption only at select applies (slice 4), so under the same
  fail-closed flag its verdict is stream-independent.

`execProgLoop_ok_of_allStreamsOkPool` is the soundness theorem: checker
true at fuel `N` ⇒ every stream's pool run completes `.ok (.normal σf)`
within `N` with `post σf = true` — in particular no run deadlocks, no
run trips the race detector, on ANY modeled schedule.
-/

namespace GoLean.GoCore.Machine

-- The unused-simp-arg linter misfires on the shared multi-branch simp
-- sets (the `MultiSound.lean`/`MachineSound.lean` precedent).
set_option linter.unusedSimpArgs false

/-- Is this configuration a nonempty-branching `mapIterK` position?
(Conservative: flags every `mapIterK` `.next`, including the empty
snapshot the sequential checker probes obliviously — the pool checker
fails closed on both rather than reasoning about emptiness.) -/
def isMapIterNext : Config → Bool
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ _) => true
  | _ => false

/-- Is this select-apply configuration's apply NON-consuming — i.e.
does `applySelectCore` return `.done` (default taken, park, or a
singleton-ready commit)? Kernel-computable on the spot; `false` on
every other shape and on the `.picks` (≥ 2 ready, L2-consuming) arm.
The spec-parity slice-4 refinement (design note
`docs/2026-08-10_gospecc-decomposition.md` §6(b)): the select-tricky
class's selects are all `.done`-shaped, and the blanket
`consumesSelect` refusal was the only thing keeping them out of the
checker. -/
def selectApplyDone (s : ExecState) : Config → Bool
  | .retV v (.selectOpsK clauses default? done [] env k) =>
      match applySelectCore s clauses default? ((v :: done).reverse) env k with
      | .ok (.done _ _) => true
      | _ => false
  | _ => false

/-- The fail-closed per-thread obliviousness check: `true` only on
shapes whose `stepThread` provably ignores the choice stream
(`stepThread_oblivious`). Select applies (spec-parity slice 4): no
longer a blanket refusal — accepted exactly when the arrival analysis
is partnerless (`.cellPath`) AND the apply is non-consuming
(`selectApplyDone`, the `.done` shape); a multi-ready (L2-consuming)
or partnered select still fails closed. -/
def poolThreadOblivious (s : ExecState) (ts : Array Config) (i : Nat) : Bool :=
  match ts[i]? with
  | none => false
  | some c =>
    if isBlockedConfig c then true
    else if (spawnedCont c).isSome then true
    else if (spawnPlan c).isSome then true
    else if consumesSelect c then
      (match arrivalCases s ts i c with
       | .ok .cellPath => selectApplyDone s c
       | _ => false)
    else if consumesAppendSlice c then false
    else if isMapIterNext c then false
    else
      match arrivalCases s ts i c with
      | .ok .cellPath => true
      | .ok (.single _ cs) => cs.length == 1
      | _ => false

/-- The `mapIterK` exclusion in the shape `stepFn_oblivious` consumes. -/
theorem isMapIterNext_false_elim {c : Config} (h : isMapIterNext c = false) :
    ∀ (kv vv : Option String) (kt vt : Ty) (body : Stmt)
      (base : Option Loc) (produced start : Array GoValue)
      (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body base produced start env k) := by
  intro kv vv kt vt body base produced start env k heq
  subst heq
  simp [isMapIterNext] at h

/-- A `consumesSelect` configuration is exactly the select-apply
shape. -/
theorem consumesSelect_shape {c : Config} (h : consumesSelect c = true) :
    ∃ v clauses default? done env k,
      c = .retV v (.selectOpsK clauses default? done [] env k) := by
  match c, h with
  | .retV v (.selectOpsK clauses default? done [] env k), _ =>
    exact ⟨v, clauses, default?, done, env, k, rfl⟩

/-- Inversion of the non-consuming apply shape: `.done` arises only
from a zero-ready analysis (default or park) or a singleton-ready
commit — never from the `.picks` (≥ 2 ready) arm. Feeds the detector's
obliviousness (`raceUpdate` reads the stream only in its multi-ready
branches). -/
theorem applySelectCore_done_inv {s : ExecState}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : ExecState}
    (h : applySelectCore s clauses default? vs env k = .ok (.done c' s')) :
    ∃ evs, evalClauses clauses vs = .ok evs
      ∧ (readyClauses s evs = .ok []
        ∨ ∃ cl, readyClauses s evs = .ok [cl]) := by
  unfold applySelectCore at h
  simp only [bind_eq_ok] at h
  obtain ⟨evs, hevs, h⟩ := h
  refine ⟨evs, hevs, ?_⟩
  obtain ⟨ready, hready, h⟩ := h
  cases ready with
  | nil => exact .inl hready
  | cons cl rest =>
    cases rest with
    | nil => exact .inr ⟨cl, hready⟩
    | cons cl2 rest2 =>
      -- the `.picks` arm: its result is never `.done`
      simp only [bind_eq_ok] at h
      obtain ⟨commits, -, h⟩ := h
      simp only [pure_eq_ok] at h
      cases h

/-- A non-consuming apply returns the stream untouched, whatever the
stream. -/
theorem applySelect_of_done {s : ExecState}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : ExecState}
    (h : applySelectCore s clauses default? vs env k = .ok (.done c' s')) :
    ∀ ch : Choices,
      applySelect s clauses default? vs env k ch = .ok (c', s', ch) := by
  intro ch
  unfold applySelect
  simp only [h, Bind.bind, Except.bind]
  rfl

/-- `stepFn` at a `.done`-shaped select apply is stream-independent:
the apply commits/parks/defaults with the stream returned verbatim. -/
theorem stepFn_select_done {s : ExecState} {v : GoValue}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {done : List GoValue} {env : LocalEnv} {k : Cont}
    {c' : Config} {s' : ExecState}
    (h : applySelectCore s clauses default? ((v :: done).reverse) env k
      = .ok (.done c' s')) :
    ∀ ch : Choices,
      stepFn s (.retV v (.selectOpsK clauses default? done [] env k)) ch
        = .ok (c', s', ch) := by
  intro ch
  unfold stepFn
  simp only [applySelect_of_done h ch]
  rfl

/-- **Stream obliviousness of the certified goroutine-step shapes**:
under the `poolThreadOblivious` flags, a `stepThread` that succeeds
under one stream succeeds under EVERY stream, with the same successor
and the stream returned untouched. -/
theorem stepThread_oblivious {s : ExecState} {ts : Array Config} {i : Nat}
    {ch₀ : Choices} {ts' : Array Config} {s' : ExecState} {ch₀' : Choices}
    (hobl : poolThreadOblivious s ts i = true)
    (h : stepThread s ts i ch₀ = .ok (ts', s', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepThread s ts i ch = .ok (ts', s', ch) := by
  unfold poolThreadOblivious at hobl
  unfold stepThread at h
  cases hti : ts[i]? with
  | none => rw [hti] at hobl; cases hobl
  | some c =>
    rw [hti] at hobl h
    by_cases hblc : isBlockedConfig c = true
    · simp only [hblc, reduceIte, bind_eq_ok] at h
      obtain ⟨⟨c₂, s₂⟩, hres, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      unfold stepThread
      rw [hti]
      simp only [hblc, reduceIte, hres, Bind.bind, Except.bind]
      rfl
    · simp only [Bool.not_eq_true] at hblc
      simp only [hblc, Bool.false_eq_true, reduceIte] at h hobl
      cases hsc : spawnedCont c with
      | some k =>
        rw [hsc] at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨rfl, fun ch => ?_⟩
        unfold stepThread
        rw [hti]
        simp only [hblc, Bool.false_eq_true, reduceIte, hsc]
        rfl
      | none =>
        rw [hsc] at h hobl
        simp only [Option.isSome_none, Bool.false_eq_true, reduceIte] at hobl
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at h
          simp only [bind_eq_ok] at h
          obtain ⟨⟨parent', child, s₂⟩, hspawn, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun ch => ?_⟩
          unfold stepThread
          rw [hti]
          simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, hspawn,
            Bind.bind, Except.bind]
          rfl
        | none =>
          rw [hsp] at h hobl
          simp only [Option.isSome_none, Bool.false_eq_true, reduceIte] at hobl
          -- the fail-closed stream flags
          cases hnsel : consumesSelect c with
          | true =>
            -- the slice-4 refinement: a select apply certified as
            -- partnerless AND non-consuming (`.done`) is oblivious
            rw [hnsel] at hobl
            simp only [reduceIte] at hobl
            obtain ⟨v, clauses, default?, dn, envS, kS, rfl⟩ :=
              consumesSelect_shape hnsel
            cases harr : arrivalCases s ts i
                (.retV v (.selectOpsK clauses default? dn [] envS kS)) with
            | error e => rw [harr] at hobl; cases hobl
            | ok a =>
              cases a with
              | single bc cands => rw [harr] at hobl; cases hobl
              | multi os => rw [harr] at hobl; cases hobl
              | cellPath =>
                rw [harr] at hobl
                dsimp only at hobl
                simp only [selectApplyDone] at hobl
                cases happly : applySelectCore s clauses default?
                    ((v :: dn).reverse) envS kS with
                | error e => rw [happly] at hobl; cases hobl
                | ok o =>
                  cases o with
                  | picks commits => rw [happly] at hobl; cases hobl
                  | done c₂ s₂ =>
                    simp only [bind_eq_ok] at h
                    obtain ⟨⟨plan, ch₁⟩, hplan, h⟩ := h
                    rw [arrivalPlan_of_cellPath (ch := ch₀) harr] at hplan
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
                    obtain ⟨hp1, hp2⟩ := hplan
                    subst hp1
                    subst hp2
                    simp only [bind_eq_ok] at h
                    obtain ⟨⟨c₃, s₃, ch₃⟩, hstep, h⟩ := h
                    simp only [pure_eq_ok, Except.ok.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    rw [stepFn_select_done happly ch₀] at hstep
                    injection hstep with hstep
                    injection hstep with hc hrest
                    injection hrest with hs hch
                    subst hc
                    subst hs
                    subst hch
                    refine ⟨rfl, fun ch => ?_⟩
                    unfold stepThread
                    rw [hti]
                    simp only [hblc, Bool.false_eq_true, reduceIte, hsc,
                      hsp, Bind.bind, Except.bind,
                      arrivalPlan_of_cellPath (ch := ch) harr]
                    rw [stepFn_select_done happly ch]
                    rfl
          | false =>
          rw [hnsel] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnapp : consumesAppendSlice c with
          | true => rw [hnapp] at hobl; simp at hobl
          | false =>
          rw [hnapp] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnmi : isMapIterNext c with
          | true => rw [hnmi] at hobl; simp at hobl
          | false =>
          rw [hnmi] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          simp only [bind_eq_ok] at h
          obtain ⟨⟨plan, ch₁⟩, hplan, h⟩ := h
          cases harr : arrivalCases s ts i c with
          | error e =>
            rw [harr] at hobl
            cases hobl
          | ok r =>
            cases r with
            | cellPath =>
              rw [arrivalPlan_of_cellPath (ch := ch₀) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2⟩ := hplan
              subst hp1
              subst hp2
              simp only [bind_eq_ok] at h
              obtain ⟨⟨c₂, s₂, ch₂⟩, hstep, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              obtain ⟨rfl, hall⟩ := stepFn_oblivious
                (isMapIterNext_false_elim hnmi) hnapp hnsel hstep
              refine ⟨rfl, fun ch => ?_⟩
              unfold stepThread
              rw [hti]
              simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp,
                Bind.bind, Except.bind, arrivalPlan_of_cellPath (ch := ch) harr]
              rw [hall ch]
              rfl
            | single bc cands =>
              rw [harr] at hobl
              rw [arrivalPlan_of_single (ch := ch₀) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2⟩ := hplan
              subst hp1
              subst hp2
              cases cands with
              | nil => simp at hobl
              | cons cand rest =>
                cases rest with
                | nil =>
                  dsimp only at h
                  simp only [bind_eq_ok] at h
                  obtain ⟨⟨ts₂, s₂⟩, hpair, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  refine ⟨rfl, fun ch => ?_⟩
                  unfold stepThread
                  rw [hti]
                  simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp,
                    Bind.bind, Except.bind,
                    arrivalPlan_of_single (ch := ch) harr]
                  rw [hpair]
                  rfl
                | cons cand2 rest2 => simp at hobl
            | multi os =>
              rw [harr] at hobl
              cases hobl

/-- **The detector's dispatcher is stream-independent away from
CONSUMING select applies** (its only replication site, slice 4;
hypothesis generalized at spec-parity slice 4: a select apply
certified partnerless + non-consuming is also covered — the detector's
select arm reads the stream only in its multi-ready branches, which
the `.done` inversion excludes). -/
theorem raceUpdate_oblivious {sPre : ExecState} {tsPre : Array Config}
    {ch ch' : Choices} {m' : MultiConfig} {r : RaceState}
    (hns : ∀ cPre, tsPre[m'.cur]? = some cPre →
      consumesSelect cPre = false
        ∨ (arrivalCases sPre tsPre m'.cur cPre = .ok .cellPath
            ∧ selectApplyDone sPre cPre = true)) :
    raceUpdate sPre tsPre ch m' r = raceUpdate sPre tsPre ch' m' r := by
  unfold raceUpdate
  by_cases hsz : m'.threads.size ≤ 1
  · simp [hsz]
  · simp only [hsz, Bool.false_eq_true, reduceIte]
    cases hti : tsPre[m'.cur]? with
    | none => rfl
    | some cPre =>
      have hsel := hns cPre hti
      by_cases hgrow : tsPre.size < m'.threads.size
      · simp [hgrow]
      · simp only [if_neg hgrow]
        by_cases hblk : isBlockedConfig cPre = true
        · simp [hblk]
        · simp only [hblk, Bool.false_eq_true, reduceIte]
          cases cPre <;> try rfl
          case retV v k =>
            cases k <;> try rfl
            case chanStK op done pending env kk =>
              cases pending <;> rfl
            -- syncStK (spec-parity slice 2): the sync arm never reads
            -- the stream (zero new Choices sites).
            case syncStK op done pending env kk =>
              cases pending <;> rfl
            case selectOpsK clauses d done pending env kk =>
              cases pending with
              | cons e rest => rfl
              | nil =>
                -- the slice-4 case: partnerless + `.done` — the arm's
                -- stream reads are all in branches the inversion of
                -- `.done` excludes
                rcases hsel with hfalse | ⟨harr, hdone⟩
                · simp [consumesSelect] at hfalse
                · have hdone' : ∃ c₂ s₂,
                      applySelectCore sPre clauses d ((v :: done).reverse)
                        env kk = .ok (.done c₂ s₂) := by
                    simp only [selectApplyDone] at hdone
                    cases happ : applySelectCore sPre clauses d
                        ((v :: done).reverse) env kk with
                    | error e => rw [happ] at hdone; cases hdone
                    | ok o =>
                      cases o with
                      | picks commits => rw [happ] at hdone; cases hdone
                      | done c₂ s₂ => exact ⟨c₂, s₂, rfl⟩
                  obtain ⟨c₂, s₂, happly⟩ := hdone'
                  obtain ⟨evs, hevs, hready⟩ :=
                    applySelectCore_done_inv happly
                  simp only [Bind.bind, Except.bind]
                  congr 1
                  funext r₁
                  cases hwp : wokenPartner tsPre m'.threads m'.cur with
                  | some j => rfl
                  | none =>
                    dsimp only
                    cases hpost : m'.threads[m'.cur]? with
                    | none =>
                      simp only [harr, hevs, Bind.bind, Except.bind]
                      rcases hready with hready | ⟨cl, hready⟩ <;>
                        simp only [hready]
                    | some cPost =>
                      cases cPost <;>
                        first
                        | rfl
                        | (simp only [harr, hevs, Bind.bind, Except.bind]
                           rcases hready with hready | ⟨cl, hready⟩ <;>
                             simp only [hready])

/-- One all-runnable-branches STEP probe — the checker's stepping core,
factored out (BUG-044: the main-exit window makes it reachable from TWO
classification arms, so it is shared instead of duplicated). Every
scheduler branch of one pool step from `m` must succeed
stream-obliviously with the detector accepting and `next` certifying
the successor. The recursive knot is passed in (`next` =
`allStreamsOkPool post fuel`), keeping this helper non-recursive and
the checker's recursion structural. -/
def stepAllBranchesOk (next : MultiConfig → RaceState → Bool)
    (m : MultiConfig) (r : RaceState) : Bool :=
  let probe : Nat → Choices → Bool := fun i probeCh =>
    poolThreadOblivious m.shared m.threads i &&
    match stepMulti m probeCh with
    | .ok (m', chRem) =>
        chRem.isEmpty &&
        (match raceUpdate m.shared m.threads probeCh m' r with
         | .ok r' => next m' r'
         | .error _ => false)
    | .error _ => false
  match m.threads[m.cur]? with
  | none => false
  | some c =>
    if c.atBoundary then
      match runnableIdxs m.shared m.threads with
      | [] => false
      | [i] => probe i []
      | rs =>
          (List.range rs.length).all fun j =>
            match rs[j]? with
            | some i => probe i [j]
            | none => false
    else probe m.cur []

/-- **THE POOL ∀-STREAMS CHECKER** (docstring above): kernel-evaluable
certification that every choice stream completes the pool run at main's
`.normal` terminal with `post` true of the joined final state. The
BUG-044 MAIN-EXIT WINDOW (L5) is covered: at main's terminal with other
goroutines still runnable, BOTH window branches must certify — the
exit itself (`post σf`) AND every continuation step
(`stepAllBranchesOk`, recursively), mirroring `execProgLoop`'s bound-2
site over every pick. -/
def allStreamsOkPool (post : ExecState → Bool) :
    Nat → MultiConfig → RaceState → Bool
  | 0, _, _ => false
  | fuel + 1, m, r =>
    if m.threads.isEmpty then false
    else
      match m.panicMsg? with
      | some _ => false
      | none =>
        match m.mainOutcome? with
        | some (.normal σf) =>
          (match runnableIdxs m.shared m.threads with
          | [] => post σf
          | _ :: _ =>
              post σf && stepAllBranchesOk (allStreamsOkPool post fuel) m r)
        | some _ => false
        | none =>
          if (runnableIdxs m.shared m.threads).isEmpty then false
          else stepAllBranchesOk (allStreamsOkPool post fuel) m r


/-- A certified thread shape is either not a select apply at all, or a
select apply certified partnerless AND non-consuming (the slice-4
refinement — the old conclusion was the bare `consumesSelect c =
false`). Feeds `raceUpdate_oblivious`. -/
theorem poolThreadOblivious_sel {s : ExecState} {ts : Array Config}
    {i : Nat} {c : Config}
    (hobl : poolThreadOblivious s ts i = true) (hti : ts[i]? = some c) :
    consumesSelect c = false
      ∨ (arrivalCases s ts i c = .ok .cellPath
          ∧ selectApplyDone s c = true) := by
  unfold poolThreadOblivious at hobl
  rw [hti] at hobl
  dsimp only at hobl
  by_cases hblc : isBlockedConfig c = true
  · cases c <;> simp_all [isBlockedConfig, consumesSelect]
  · simp only [Bool.not_eq_true] at hblc
    simp only [hblc, Bool.false_eq_true, reduceIte] at hobl
    cases hsc : spawnedCont c with
    | some k =>
      obtain rfl := spawnedCont_shape hsc
      exact .inl rfl
    | none =>
      simp only [hsc, Option.isSome_none, Bool.false_eq_true,
        reduceIte] at hobl
      cases hsp : spawnPlan c with
      | some p =>
        match c, hsp with
        | .retV cv (.goCalleeK [] env k), _ => exact .inl rfl
        | .retV v (.goArgsK cv vals [] env k), _ => exact .inl rfl
      | none =>
        simp only [hsp, Option.isSome_none, Bool.false_eq_true,
          reduceIte] at hobl
        cases hnsel : consumesSelect c with
        | true =>
          rw [hnsel] at hobl
          simp only [reduceIte] at hobl
          refine .inr ?_
          cases harr : arrivalCases s ts i c with
          | error e => rw [harr] at hobl; cases hobl
          | ok a =>
            cases a with
            | single bc cands => rw [harr] at hobl; cases hobl
            | multi os => rw [harr] at hobl; cases hobl
            | cellPath =>
              rw [harr] at hobl
              exact ⟨rfl, hobl⟩
        | false => exact .inl rfl

/-- The one-layer unfolding of `execProgLoop`, as an equation
(incl. the BUG-044 main-exit window at `mainOutcome?`-some). -/
theorem execProgLoop_unfold (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) :
    execProgLoop fuel m r ch
      = (if m.threads.isEmpty then
          throw (.internal "thread pool without a main goroutine")
        else
          match m.panicMsg? with
          | some msg => throw (.panic msg)
          | none =>
            match m.mainOutcome? with
            | some out =>
              (match runnableIdxs m.shared m.threads with
              | [] => return (out, ch)
              | _ :: _ =>
                  let (pick, ch₁) := ch.consume 2
                  if pick == 0 then return (out, ch₁)
                  else
                    match fuel with
                    | 0 => throw .fuelOut
                    | fuel + 1 => do
                        let (m', choices') ← stepMulti m ch₁
                        let r' ← raceUpdate m.shared m.threads ch₁ m' r
                        execProgLoop fuel m' r' choices')
            | none =>
              if (runnableIdxs m.shared m.threads).isEmpty then
                throw .deadlock
              else
                match fuel with
                | 0 => throw .fuelOut
                | fuel + 1 => do
                    let (m', choices') ← stepMulti m ch
                    let r' ← raceUpdate m.shared m.threads ch m' r
                    execProgLoop fuel m' r' choices') := by
  rw [execProgLoop.eq_def]
  rfl

set_option maxHeartbeats 1600000 in
/-- **Soundness of the stepping core** (`stepAllBranchesOk`), for the
induction step of the checker's soundness theorem: if every scheduler
branch of one pool step certifies (with `next` = the fuel-`n` checker,
whose soundness is the induction hypothesis `ih`), then under EVERY
stream the step-then-recurse pipeline completes at main's `.normal`
terminal with `post`. Shared verbatim by both classification arms that
step (mid-run, and the BUG-044 main-exit window's continue branch). -/
theorem stepAllBranchesOk_sound {post : ExecState → Bool} {n : Nat}
    {m : MultiConfig} {r : RaceState}
    (ih : ∀ {m' : MultiConfig} {r' : RaceState},
      allStreamsOkPool post n m' r' = true →
      ∀ ch : Choices, ∃ (σf : ExecState) (ch' : Choices),
        execProgLoop n m' r' ch = .ok (.normal σf, ch') ∧ post σf = true)
    (hall : stepAllBranchesOk (allStreamsOkPool post n) m r = true) :
    ∀ ch : Choices, ∃ (σf : ExecState) (ch' : Choices),
      ((do
        let x ← stepMulti m ch
        match x with
        | (m', choices') => do
            let r' ← raceUpdate m.shared m.threads ch m' r
            execProgLoop n m' r' choices')
        : Except GoError (ExecOutcome × Choices))
        = .ok (.normal σf, ch') ∧ post σf = true := by
  intro ch
  unfold stepAllBranchesOk at hall
  dsimp only at hall
  -- the per-branch probe fact, discharged uniformly below
  have hprobe : ∀ {i : Nat} {probeCh : Choices},
      (poolThreadOblivious m.shared m.threads i &&
        match stepMulti m probeCh with
        | .ok (m', chRem) =>
            chRem.isEmpty &&
            (match raceUpdate m.shared m.threads probeCh m' r with
             | .ok r' => allStreamsOkPool post n m' r'
             | .error _ => false)
        | .error _ => false) = true →
      -- what the induction needs: the probe's successor pool,
      -- the empty remainder, the detector verdict, and the
      -- recursive certificate
      ∃ (m' : MultiConfig) (r' : RaceState),
        poolThreadOblivious m.shared m.threads i = true
        ∧ stepMulti m probeCh = .ok (m', [])
        ∧ raceUpdate m.shared m.threads probeCh m' r = .ok r'
        ∧ allStreamsOkPool post n m' r' = true := by
    intro i probeCh hpr
    rw [Bool.and_eq_true] at hpr
    obtain ⟨hobl, hpr⟩ := hpr
    cases hsm : stepMulti m probeCh with
    | error e => rw [hsm] at hpr; cases hpr
    | ok p =>
      obtain ⟨m', chRem⟩ := p
      rw [hsm] at hpr
      dsimp only at hpr
      rw [Bool.and_eq_true] at hpr
      obtain ⟨hemp', hpr⟩ := hpr
      have hchRem : chRem = [] := by
        cases chRem with
        | nil => rfl
        | cons a l => simp [List.isEmpty] at hemp'
      subst hchRem
      cases hru : raceUpdate m.shared m.threads probeCh m' r with
      | error e => rw [hru] at hpr; cases hpr
      | ok r' =>
        rw [hru] at hpr
        exact ⟨m', r', hobl, rfl, hru, hpr⟩
  cases hti : m.threads[m.cur]? with
  | none => rw [hti] at hall; cases hall
  | some c =>
    rw [hti] at hall
    dsimp only at hall
    -- shared finisher: from a certified probe for thread `i`
    -- and the real `stepMulti` landing on the same successor,
    -- chain the detector and the induction hypothesis.
    have hfinish : ∀ {i : Nat} {probeCh chTail : Choices}
        {m' : MultiConfig} {r' : RaceState},
        poolThreadOblivious m.shared m.threads i = true →
        raceUpdate m.shared m.threads probeCh m' r = .ok r' →
        allStreamsOkPool post n m' r' = true →
        stepMulti m ch = .ok (m', chTail) →
        m'.cur = i →
        ∃ (σf : ExecState) (ch' : Choices),
          ((do
            let x ← stepMulti m ch
            match x with
            | (m', choices') => do
                let r' ← raceUpdate m.shared m.threads ch m' r
                execProgLoop n m' r' choices')
            : Except GoError (ExecOutcome × Choices))
            = .ok (.normal σf, ch') ∧ post σf = true := by
      intro i probeCh chTail m' r' hobl hru hnext hreal hcur
      have hruReal : raceUpdate m.shared m.threads ch m' r = .ok r' := by
        rw [raceUpdate_oblivious (ch' := probeCh)
          (fun cPre hcp => by
            rw [hcur]
            exact poolThreadOblivious_sel hobl (hcur ▸ hcp))]
        exact hru
      obtain ⟨σf, ch'', hrec, hpost⟩ := ih hnext chTail
      refine ⟨σf, ch'', ?_, hpost⟩
      dsimp only
      rw [hreal]
      simp only [Bind.bind, Except.bind]
      rw [hruReal]
      exact hrec
    by_cases hb : c.atBoundary = true
    · rw [if_pos hb] at hall
      cases hrs : runnableIdxs m.shared m.threads with
      | nil => rw [hrs] at hall; cases hall
      | cons r0 rest =>
        rw [hrs] at hall
        cases rest with
        | nil =>
          obtain ⟨m', r', hobl, hsm, hru, hnext⟩ := hprobe hall
          have hinto : stepThreadInto m r0 [] = .ok (m', []) := by
            unfold stepMulti at hsm
            rw [hti] at hsm
            dsimp only at hsm
            rw [if_pos hb, hrs] at hsm
            exact hsm
          obtain ⟨ts₂, s₂, hst, hm'⟩ :
              ∃ ts₂ s₂,
                stepThread m.shared m.threads r0 [] = .ok (ts₂, s₂, [])
                ∧ m' = ⟨ts₂, s₂, r0⟩ := by
            unfold stepThreadInto at hinto
            simp only [bind_eq_ok] at hinto
            obtain ⟨⟨ts₂, s₂, chr⟩, hst, hinto⟩ := hinto
            simp only [pure_eq_ok, Except.ok.injEq,
              Prod.mk.injEq] at hinto
            obtain ⟨rfl, rfl⟩ := hinto
            exact ⟨ts₂, s₂, hst, rfl⟩
          obtain ⟨-, hallst⟩ := stepThread_oblivious hobl hst
          have hreal : stepMulti m ch = .ok (m', ch) := by
            unfold stepMulti
            rw [hti]
            dsimp only
            rw [if_pos hb, hrs]
            dsimp only
            unfold stepThreadInto
            rw [hallst ch]
            subst hm'
            rfl
          exact hfinish hobl hru hnext hreal (by rw [hm'])
        | cons r1 rest' =>
          rcases hcons : Choices.consume ch (r0 :: r1 :: rest').length
            with ⟨pick, tail⟩
          have hpicklt : pick < (r0 :: r1 :: rest').length := by
            have hb0 : 0 < (r0 :: r1 :: rest').length := by simp
            have := consume_fst_lt (ch := ch) hb0
            rw [hcons] at this
            exact this
          rw [List.all_eq_true] at hall
          have hj := hall pick (by
            simpa using List.mem_range.mpr hpicklt)
          cases hget : (r0 :: r1 :: rest')[pick]? with
          | none =>
            rw [List.getElem?_eq_none_iff] at hget
            omega
          | some i =>
            rw [hget] at hj
            obtain ⟨m', r', hobl, hsm, hru, hnext⟩ := hprobe hj
            have hconsProbe :
                Choices.consume [pick] (r0 :: r1 :: rest').length
                  = (pick, []) := by
              simp only [Choices.consume, Prod.mk.injEq]
              refine ⟨Nat.mod_eq_of_lt ?_, trivial⟩
              omega
            have hinto : stepThreadInto m i [] = .ok (m', []) := by
              unfold stepMulti at hsm
              rw [hti] at hsm
              dsimp only at hsm
              rw [if_pos hb, hrs] at hsm
              dsimp only at hsm
              simp only [hconsProbe, hget] at hsm
              exact hsm
            obtain ⟨ts₂, s₂, hst, hm'⟩ :
                ∃ ts₂ s₂,
                  stepThread m.shared m.threads i []
                    = .ok (ts₂, s₂, [])
                  ∧ m' = ⟨ts₂, s₂, i⟩ := by
              unfold stepThreadInto at hinto
              simp only [bind_eq_ok] at hinto
              obtain ⟨⟨ts₂, s₂, chr⟩, hst, hinto⟩ := hinto
              simp only [pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at hinto
              obtain ⟨rfl, rfl⟩ := hinto
              exact ⟨ts₂, s₂, hst, rfl⟩
            obtain ⟨-, hallst⟩ := stepThread_oblivious hobl hst
            have hreal : stepMulti m ch = .ok (m', tail) := by
              unfold stepMulti
              rw [hti]
              dsimp only
              rw [if_pos hb, hrs]
              dsimp only
              rw [hcons]
              dsimp only
              rw [hget]
              dsimp only
              unfold stepThreadInto
              rw [hallst tail]
              subst hm'
              rfl
            exact hfinish hobl hru hnext hreal (by rw [hm'])
    · rw [if_neg hb] at hall
      obtain ⟨m', r', hobl, hsm, hru, hnext⟩ := hprobe hall
      have hinto : stepThreadInto m m.cur [] = .ok (m', []) := by
        unfold stepMulti at hsm
        rw [hti] at hsm
        dsimp only at hsm
        rw [if_neg hb] at hsm
        exact hsm
      obtain ⟨ts₂, s₂, hst, hm'⟩ :
          ∃ ts₂ s₂,
            stepThread m.shared m.threads m.cur []
              = .ok (ts₂, s₂, [])
            ∧ m' = ⟨ts₂, s₂, m.cur⟩ := by
        unfold stepThreadInto at hinto
        simp only [bind_eq_ok] at hinto
        obtain ⟨⟨ts₂, s₂, chr⟩, hst, hinto⟩ := hinto
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hinto
        obtain ⟨rfl, rfl⟩ := hinto
        exact ⟨ts₂, s₂, hst, rfl⟩
      obtain ⟨-, hallst⟩ := stepThread_oblivious hobl hst
      have hreal : stepMulti m ch = .ok (m', ch) := by
        unfold stepMulti
        rw [hti]
        dsimp only
        rw [if_neg hb]
        unfold stepThreadInto
        rw [hallst ch]
        subst hm'
        rfl
      exact hfinish hobl hru hnext hreal (by rw [hm'])

set_option maxHeartbeats 1600000 in
/-- **Checker soundness**: `allStreamsOkPool post fuel m r = true`
certifies that EVERY choice stream's pool run from `(m, r)` completes
at main's `.normal` terminal within `fuel`, with `post` true of the
joined final state — schedules and data latitude quantified together
(one stream), deadlock and race refusals excluded on every modeled
schedule, and (BUG-044) the main-exit window's branches both covered:
the exit pick returns main's readout, every continue pick re-enters
the certified stepping core. -/
theorem execProgLoop_ok_of_allStreamsOkPool {post : ExecState → Bool} :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState},
      allStreamsOkPool post fuel m r = true →
      ∀ ch : Choices, ∃ (σf : ExecState) (ch' : Choices),
        execProgLoop fuel m r ch = .ok (.normal σf, ch') ∧ post σf = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r hall ch
    simp [allStreamsOkPool] at hall
  | succ n ih =>
    intro m r hall ch
    unfold allStreamsOkPool at hall
    rw [execProgLoop_unfold]
    by_cases hemp : m.threads.isEmpty
    · rw [if_pos hemp] at hall; cases hall
    · rw [if_neg hemp] at hall
      rw [if_neg hemp]
      cases hp : m.panicMsg? with
      | some msg => rw [hp] at hall; cases hall
      | none =>
        rw [hp] at hall
        cases hm : m.mainOutcome? with
        | some out =>
          rw [hm] at hall
          cases out with
          | normal σf =>
            cases hrs : runnableIdxs m.shared m.threads with
            | nil =>
              rw [hrs] at hall
              exact ⟨σf, ch, rfl, hall⟩
            | cons r0 rest =>
              -- the BUG-044 main-exit window: both picks certified
              rw [hrs] at hall
              rw [Bool.and_eq_true] at hall
              obtain ⟨hpost, hstep⟩ := hall
              dsimp only
              rcases hcons : Choices.consume ch 2 with ⟨pick, ch₁⟩
              dsimp only
              by_cases hpick : (pick == 0) = true
              · rw [if_pos hpick]
                exact ⟨σf, ch₁, rfl, hpost⟩
              · rw [if_neg hpick]
                exact stepAllBranchesOk_sound ih hstep ch₁
          | returned σf => cases hall
          | broke σf => cases hall
          | continued σf => cases hall
        | none =>
          rw [hm] at hall
          by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
          · rw [if_pos hrun] at hall; cases hall
          · rw [if_neg hrun] at hall
            rw [if_neg hrun]
            exact stepAllBranchesOk_sound ih hall ch

/-- Fuel monotonicity of the pool driver: a completed run is stable
under more fuel (the classification arms precede the fuel check —
`execStmt_mono`'s pool twin, what lifts a kernel-checked bound to
every larger fuel in `TerminatesC`-shaped statements). -/
theorem execProgLoop_mono :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState} {ch : Choices}
      {out : ExecOutcome} {ch' : Choices} {fuel' : Nat},
      execProgLoop fuel m r ch = .ok (out, ch') → fuel ≤ fuel' →
      execProgLoop fuel' m r ch = .ok (out, ch') := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r ch out ch' fuel' h hle
    rw [execProgLoop_unfold] at h
    rw [execProgLoop_unfold]
    by_cases hemp : m.threads.isEmpty
    · rw [if_pos hemp] at h; cases h
    · rw [if_neg hemp] at h
      rw [if_neg hemp]
      cases hp : m.panicMsg? with
      | some msg => rw [hp] at h; cases h
      | none =>
        rw [hp] at h
        cases hm : m.mainOutcome? with
        | some o =>
          rw [hm] at h
          cases hrs : runnableIdxs m.shared m.threads with
          | nil =>
            rw [hrs] at h
            exact h
          | cons r0 rest =>
            -- the BUG-044 window at fuel 0: exit pick carries over,
            -- continue pick is a fuel-out contradiction
            rw [hrs] at h
            dsimp only at h ⊢
            rcases hcons : Choices.consume ch 2 with ⟨pick, ch₁⟩
            rw [hcons] at h
            dsimp only at h ⊢
            by_cases hpick : (pick == 0) = true
            · rw [if_pos hpick] at h
              rw [if_pos hpick]
              exact h
            · rw [if_neg hpick] at h
              simp [throw, throwThe, MonadExceptOf.throw] at h
        | none =>
          rw [hm] at h
          by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
          · rw [if_pos hrun] at h; cases h
          · rw [if_neg hrun] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ n ih =>
    intro m r ch out ch' fuel' h hle
    cases fuel' with
    | zero => omega
    | succ n' =>
      rw [execProgLoop_unfold] at h
      rw [execProgLoop_unfold]
      by_cases hemp : m.threads.isEmpty
      · rw [if_pos hemp] at h; cases h
      · rw [if_neg hemp] at h
        rw [if_neg hemp]
        cases hp : m.panicMsg? with
        | some msg => rw [hp] at h; cases h
        | none =>
          rw [hp] at h
          cases hm : m.mainOutcome? with
          | some o =>
            rw [hm] at h
            cases hrs : runnableIdxs m.shared m.threads with
            | nil =>
              rw [hrs] at h
              exact h
            | cons r0 rest =>
              -- the BUG-044 window: exit pick carries over; a continue
              -- pick recurses like the ordinary step case
              rw [hrs] at h
              dsimp only at h ⊢
              rcases hcons : Choices.consume ch 2 with ⟨pick, ch₁⟩
              rw [hcons] at h
              dsimp only at h ⊢
              by_cases hpick : (pick == 0) = true
              · rw [if_pos hpick] at h
                rw [if_pos hpick]
                exact h
              · rw [if_neg hpick] at h
                rw [if_neg hpick]
                cases hsm : stepMulti m ch₁ with
                | error e =>
                  rw [hsm] at h
                  simp [Bind.bind, Except.bind] at h
                | ok p =>
                  obtain ⟨m', ch₂⟩ := p
                  rw [hsm] at h
                  simp only [Bind.bind, Except.bind] at h ⊢
                  cases hru : raceUpdate m.shared m.threads ch₁ m' r with
                  | error e =>
                    rw [hru] at h
                    simp at h
                  | ok r' =>
                    rw [hru] at h
                    exact ih h (by omega)
          | none =>
            rw [hm] at h
            by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
            · rw [if_pos hrun] at h; cases h
            · rw [if_neg hrun] at h
              rw [if_neg hrun]
              dsimp only at h ⊢
              cases hsm : stepMulti m ch with
              | error e =>
                rw [hsm] at h
                simp [Bind.bind, Except.bind] at h
              | ok p =>
                obtain ⟨m', ch₁⟩ := p
                rw [hsm] at h
                simp only [Bind.bind, Except.bind] at h ⊢
                cases hru : raceUpdate m.shared m.threads ch m' r with
                | error e =>
                  rw [hru] at h
                  simp at h
                | ok r' =>
                  rw [hru] at h
                  exact ih h (by omega)

/-- **Sub-bound classification** (the fuel truth-equivalence hinge —
matrix §7.2's recorded argument, machine-checked): truncating a
completed pool run's fuel either completes the SAME run or classifies
`.fuelOut` — never any OTHER outcome. In particular a sub-bound
truncation can never surface `.deadlock` or `.raceDetected`: the
classification arms precede the fuel check, and the truncated run
follows the identical (choice-determined) path until the fuel gate
throws. With `execProgLoop_mono` this makes the certificate-derived
`NoDeadlock`/`NoRace` corollaries quantify ALL fuels (slice 6's
fuel-independence lift). -/
theorem execProgLoop_le :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState} {ch : Choices}
      {out : ExecOutcome} {ch' : Choices} {fuel' : Nat},
      execProgLoop fuel m r ch = .ok (out, ch') → fuel' ≤ fuel →
      execProgLoop fuel' m r ch = .ok (out, ch')
        ∨ execProgLoop fuel' m r ch = .error .fuelOut := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r ch out ch' fuel' h hle
    have h0 : fuel' = 0 := Nat.le_zero.mp hle
    subst h0
    exact .inl h
  | succ n ih =>
    intro m r ch out ch' fuel' h hle
    cases fuel' with
    | zero =>
      -- fuel' = 0: the classification arms carry over verbatim; both
      -- step arms throw `.fuelOut` at the fuel gate.
      rw [execProgLoop_unfold] at h
      rw [execProgLoop_unfold]
      by_cases hemp : m.threads.isEmpty
      · rw [if_pos hemp] at h; cases h
      · rw [if_neg hemp] at h
        rw [if_neg hemp]
        cases hp : m.panicMsg? with
        | some msg => rw [hp] at h; cases h
        | none =>
          rw [hp] at h
          cases hm : m.mainOutcome? with
          | some o =>
            rw [hm] at h
            cases hrs : runnableIdxs m.shared m.threads with
            | nil =>
              rw [hrs] at h
              exact .inl h
            | cons r0 rest =>
              -- the BUG-044 window: exit pick carries over; the
              -- continue pick hits the fuel-0 gate.
              rw [hrs] at h
              dsimp only at h ⊢
              rcases hcons : Choices.consume ch 2 with ⟨pick, ch₁⟩
              rw [hcons] at h
              dsimp only at h ⊢
              by_cases hpick : (pick == 0) = true
              · rw [if_pos hpick] at h
                rw [if_pos hpick]
                exact .inl h
              · rw [if_neg hpick] at h
                rw [if_neg hpick]
                exact .inr rfl
          | none =>
            rw [hm] at h
            by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
            · rw [if_pos hrun] at h; cases h
            · rw [if_neg hrun] at h
              rw [if_neg hrun]
              exact .inr rfl
    | succ n' =>
      -- fuel' = n' + 1 ≤ n + 1: both runs take the same classification
      -- arm and (where they step) the same choice-determined step;
      -- recurse with n' ≤ n.
      rw [execProgLoop_unfold] at h
      rw [execProgLoop_unfold]
      by_cases hemp : m.threads.isEmpty
      · rw [if_pos hemp] at h; cases h
      · rw [if_neg hemp] at h
        rw [if_neg hemp]
        cases hp : m.panicMsg? with
        | some msg => rw [hp] at h; cases h
        | none =>
          rw [hp] at h
          cases hm : m.mainOutcome? with
          | some o =>
            rw [hm] at h
            cases hrs : runnableIdxs m.shared m.threads with
            | nil =>
              rw [hrs] at h
              exact .inl h
            | cons r0 rest =>
              rw [hrs] at h
              dsimp only at h ⊢
              rcases hcons : Choices.consume ch 2 with ⟨pick, ch₁⟩
              rw [hcons] at h
              dsimp only at h ⊢
              by_cases hpick : (pick == 0) = true
              · rw [if_pos hpick] at h
                rw [if_pos hpick]
                exact .inl h
              · rw [if_neg hpick] at h
                rw [if_neg hpick]
                cases hsm : stepMulti m ch₁ with
                | error e =>
                  rw [hsm] at h
                  simp [Bind.bind, Except.bind] at h
                | ok p =>
                  obtain ⟨m', ch₂⟩ := p
                  rw [hsm] at h
                  simp only [Bind.bind, Except.bind] at h ⊢
                  cases hru : raceUpdate m.shared m.threads ch₁ m' r with
                  | error e =>
                    rw [hru] at h
                    simp at h
                  | ok r' =>
                    rw [hru] at h
                    exact ih h (by omega)
          | none =>
            rw [hm] at h
            by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
            · rw [if_pos hrun] at h; cases h
            · rw [if_neg hrun] at h
              rw [if_neg hrun]
              dsimp only at h ⊢
              cases hsm : stepMulti m ch with
              | error e =>
                rw [hsm] at h
                simp [Bind.bind, Except.bind] at h
              | ok p =>
                obtain ⟨m', ch₁⟩ := p
                rw [hsm] at h
                simp only [Bind.bind, Except.bind] at h ⊢
                cases hru : raceUpdate m.shared m.threads ch m' r with
                | error e =>
                  rw [hru] at h
                  simp at h
                | ok r' =>
                  rw [hru] at h
                  exact ih h (by omega)

/-- `stepAllBranchesOk` is monotone in its recursive-knot parameter
`next`: every probe consults `next` in exactly one (positive) position,
so pointwise strengthening of `next` preserves certification. The
hinge for `allStreamsOkPool_mono`. -/
theorem stepAllBranchesOk_mono {next next' : MultiConfig → RaceState → Bool}
    {m : MultiConfig} {r : RaceState}
    (hnext : ∀ m' r', next m' r' = true → next' m' r' = true)
    (hall : stepAllBranchesOk next m r = true) :
    stepAllBranchesOk next' m r = true := by
  unfold stepAllBranchesOk at hall ⊢
  dsimp only at hall ⊢
  have hprobe : ∀ (i : Nat) (probeCh : Choices),
      (poolThreadOblivious m.shared m.threads i &&
        match stepMulti m probeCh with
        | .ok (m', chRem) =>
            chRem.isEmpty &&
            (match raceUpdate m.shared m.threads probeCh m' r with
             | .ok r' => next m' r'
             | .error _ => false)
        | .error _ => false) = true →
      (poolThreadOblivious m.shared m.threads i &&
        match stepMulti m probeCh with
        | .ok (m', chRem) =>
            chRem.isEmpty &&
            (match raceUpdate m.shared m.threads probeCh m' r with
             | .ok r' => next' m' r'
             | .error _ => false)
        | .error _ => false) = true := by
    intro i probeCh hpr
    rw [Bool.and_eq_true] at hpr ⊢
    obtain ⟨hobl, hpr⟩ := hpr
    refine ⟨hobl, ?_⟩
    cases hsm : stepMulti m probeCh with
    | error e => rw [hsm] at hpr; cases hpr
    | ok p =>
      obtain ⟨m', chRem⟩ := p
      rw [hsm] at hpr
      dsimp only at hpr ⊢
      rw [Bool.and_eq_true] at hpr ⊢
      obtain ⟨hemp', hpr⟩ := hpr
      refine ⟨hemp', ?_⟩
      cases hru : raceUpdate m.shared m.threads probeCh m' r with
      | error e => rw [hru] at hpr; cases hpr
      | ok r' =>
        rw [hru] at hpr
        dsimp only at hpr ⊢
        exact hnext _ _ hpr
  cases hti : m.threads[m.cur]? with
  | none => rw [hti] at hall; cases hall
  | some c =>
    rw [hti] at hall
    dsimp only at hall ⊢
    by_cases hb : c.atBoundary = true
    · rw [if_pos hb] at hall ⊢
      cases hrs : runnableIdxs m.shared m.threads with
      | nil => rw [hrs] at hall; cases hall
      | cons r0 rest =>
        rw [hrs] at hall
        cases rest with
        | nil => exact hprobe r0 [] hall
        | cons r1 rest' =>
          rw [List.all_eq_true] at hall ⊢
          intro j hj
          have hjj := hall j hj
          cases hget : (r0 :: r1 :: rest')[j]? with
          | none => rw [hget] at hjj; cases hjj
          | some i =>
            rw [hget] at hjj
            dsimp only at hjj ⊢
            exact hprobe i [j] hjj
    · rw [if_neg hb] at hall ⊢
      exact hprobe m.cur [] hall

/-- **Fuel monotonicity of the pool ∀-streams checker**: a certificate
at one bound holds at every larger bound — the checker only ever
returns `true` by reaching terminal pools, never by spending its
slack. With `execProgLoop_mono`/`execProgLoop_le` this is what lets
every certificate-backed statement shed its shipped literal fuel
(slice 6's fuel-independence lift). -/
theorem allStreamsOkPool_mono {post : ExecState → Bool} :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState} {fuel' : Nat},
      allStreamsOkPool post fuel m r = true → fuel ≤ fuel' →
      allStreamsOkPool post fuel' m r = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r fuel' h _
    simp [allStreamsOkPool] at h
  | succ n ih =>
    intro m r fuel' h hle
    cases fuel' with
    | zero => omega
    | succ n' =>
      have hnext : ∀ (m' : MultiConfig) (r' : RaceState),
          allStreamsOkPool post n m' r' = true →
          allStreamsOkPool post n' m' r' = true :=
        fun _ _ hm' => ih hm' (by omega)
      unfold allStreamsOkPool at h ⊢
      by_cases hemp : m.threads.isEmpty
      · rw [if_pos hemp] at h; cases h
      · rw [if_neg hemp] at h
        rw [if_neg hemp]
        cases hp : m.panicMsg? with
        | some msg => rw [hp] at h; cases h
        | none =>
          rw [hp] at h
          cases hm : m.mainOutcome? with
          | some o =>
            rw [hm] at h
            cases o with
            | normal σf =>
              cases hrs : runnableIdxs m.shared m.threads with
              | nil =>
                rw [hrs] at h
                exact h
              | cons r0 rest =>
                rw [hrs] at h
                rw [Bool.and_eq_true] at h ⊢
                obtain ⟨hpost, hstep⟩ := h
                exact ⟨hpost, stepAllBranchesOk_mono hnext hstep⟩
            | returned σf => cases h
            | broke σf => cases h
            | continued σf => cases h
          | none =>
            rw [hm] at h
            by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
            · rw [if_pos hrun] at h; cases h
            · rw [if_neg hrun] at h
              rw [if_neg hrun]
              exact stepAllBranchesOk_mono hnext h

end GoLean.GoCore.Machine
