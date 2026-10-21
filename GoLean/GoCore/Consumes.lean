import GoLean.GoCore.Multi

/-!
# The choice-site SHAPE predicates (re-homed 2026-10-20, lane `core/retire-relation-1020`)

Executable predicates over a configuration (and, for the pool, over a thread array) naming the
shapes at which a step MAY consume the choice tape: the fail-closed flags the certified dedup
checker (`EnumDedupCheck.lean`) and the CLI enumerator (`GoLean/EnumDedup.lean`) branch or
refuse on. Moved here VERBATIM from the retired proof modules — `consumesTryLock`,
`consumesAppendSlice`, `consumesRandIntn`, `consumesConvCap`, `consumesSelect` from
`MachineSound.lean`; `isMapIterNext`, `selectApplyDone`, `poolThreadOblivious` from
`MultiStreams.lean` — when the mainline relation and its coherence proofs left the build
(tag `relational/last-main-2026-10-20`); the names and signatures are unchanged. The
stream lemmas that reason about them (`stepFn_*_oblivious`, `stepFn_consumption_*`) live in
`StepFnFacts.lean`, which imports this module.
-/

namespace GoLean.GoCore.Machine

-- The program context is the first explicit parameter of every definition below that
-- reads it (`selectApplyDone`, `poolThreadOblivious`), as in their origin modules.
variable (ctx : ProgramCtx)

/-- Is this configuration a TRY head's sync-apply position (the one sync
apply that draws the `tryLock` site — Q-TRYLOCK)? Conservative, like
`consumesSelect`: flags the held-cell apply too (bound 1, which pops
nothing) — the checkers fail closed there rather than reasoning about
acquirability; the membership enumerator's `stepNeeds` computes the
exact width. -/
def consumesTryLock : Config → Bool
  | .retV _ (.syncStK op _ [] _ _) => op.tryTargets?.isSome
  | _ => false

/-- Is this configuration about to dispatch `applyStmtOp` with an
`appendSlice` op (the one stream-consuming wide op)? Conservative
shape check on the two `applyStmtOp` call sites in `stepFn`: the
`stmtOpK` apply position (the former nullary wide-statement arm is a
refusal since A8 — no `stmtPlan` emits an empty operand list). -/
def consumesAppendSlice : Config → Bool
  | .retV _ (.stmtOpK op _ _ [] _ _) =>
      match op with
      | .appendSlice _ => true
      | _ => false
  | .exec stmt _ _ =>
      match stmtPlan stmt with
      | some (op, _, []) =>
          match op with
          | .appendSlice _ => true
          | _ => false
      | _ => false
  | _ => false

/-- Is this configuration about to dispatch `applyStmtOp` with the `randIntn`
op — the `[0, n)` draw (`Stmt.randIntn`, window unit 5b), the SECOND
stream-consuming wide op? Conservative, like `consumesAppendSlice`: flags
every `randIntn` apply, including the bound-1 one that pops nothing — the
obliviousness checkers fail closed there rather than reading the bound; the
certified dedup engine refuses it too (`innerVecs`) and the CLI enumerator
carries such rows. -/
def consumesRandIntn : Config → Bool
  | .retV _ (.stmtOpK op _ _ [] _ _) =>
      match op with
      | .randIntn => true
      | _ => false
  | .exec stmt _ _ =>
      match stmtPlan stmt with
      | some (op, _, []) =>
          match op with
          | .randIntn => true
          | _ => false
      | _ => false
  | _ => false

/-- Is this configuration about to dispatch the strict apply of a CONVERSION head —
`[]byte(s)` / `[]rune(s)`, whose funnel `applyStrictOpPick` draws `ChoiceSite.convCap`
(R3 / b6, 2026-10-07)? Conservative, like `consumesRandIntn`: flags every conversion
apply, including the one-member instance that pops nothing (every literal conversion)
and the refusing one — the obliviousness checkers fail closed there rather than reading
the operand; the certified dedup engine refuses it too (`innerVecs`, design D7) and the
CLI enumerator carries such rows. No nullary conversion exists (`strictPlan` always
produces one operand), so the `.evalE` nullary-apply shape is never a conversion. -/
def consumesConvCap : Config → Bool
  | .retV _ (.strictK op _ [] _ _) => op.convKind?.isSome
  | _ => false

/-- Is this configuration the select APPLY position (whose
`applySelect` may consume the L2 clause pick — slice 4)? Conservative,
like `consumesAppendSlice`: flags every select apply, including the
stream-oblivious single-ready/default ones — the checker fails closed
there rather than reasoning about readiness. -/
def consumesSelect : Config → Bool
  | .retV _ (.selectOpsK _ _ _ [] _ _) => true
  | _ => false

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
def selectApplyDone (s : Store) : Config → Bool
  | .retV v (.selectOpsK clauses default? done [] env k) =>
      match applySelectCore ctx s clauses default? ((v :: done).reverse) env k with
      | .ok (.done _ _ _ _) => true
      | _ => false
  | _ => false

/-- The fail-closed per-thread obliviousness check: `true` only on
shapes whose `stepThread` provably ignores the choice stream
(`stepThread_oblivious`). Select applies (spec-parity slice 4): no
longer a blanket refusal — accepted exactly when the arrival analysis
is partnerless (`.cellPath`) AND the apply is non-consuming
(`selectApplyDone`, the `.done` shape); a multi-ready (L2-consuming)
or partnered select still fails closed. -/
def poolThreadOblivious (s : Store) (ts : Array Thread) (i : Nat) : Bool :=
  match ts[i]? with
  | none => false
  | some (.aborted _) => true
  | some (.running _ (some _)) => true
  | some (.running c none) =>
    if isBlockedConfig c then true
    -- THE ABORT (B4) is oblivious exactly outside the `repanicCollapse`
    -- shape (landing chunk L3): a recovered head with an equal successor
    -- payload draws the collapse pick at bound 2 — fail closed.
    else if c.abort?.isSome then !consumesRepanicCollapse c
    -- Unit 6b: the preprint PHASE step at an unsettled chain draws the same
    -- site at a collision (bound 2) — fail closed; the CLI enumerator
    -- carries such rows (the non-colliding phase step pops nothing and is
    -- oblivious through the generic arm below).
    else if consumesRepanicCollapse c then false
    else if (spawnPlan c).isSome then !consumesNilValueMethod ctx c
    else if consumesSelect c then
      (match arrivalCases ctx s ts i c with
       | .ok .cellPath => selectApplyDone ctx s c
       | _ => false)
    else if consumesAppendSlice c then false
    -- Unit 5b: a `randIntn` apply draws the `intn` site at bound `n`; the
    -- checker refuses it (fail closed, even at the bound-1 instance that pops
    -- nothing) — the CLI enumerator carries such rows.
    else if consumesRandIntn c then false
    -- R3 / b6: a conversion head's strict apply draws the `convCap` site at the
    -- member count; the checker refuses it (fail closed, even at the one-member
    -- instance that pops nothing) — the CLI enumerator carries such rows.
    else if consumesConvCap c then false
    -- Q-TRYLOCK: a TRY head's sync apply draws the `tryLock` site; the
    -- checker refuses it (fail closed, even at the held cell's bound 1)
    -- — the CLI enumerator's `stepNeeds` carries such rows.
    else if consumesTryLock c then false
    else if isMapIterNext c then false
    else if consumesNilValueMethod ctx c then false
    -- E13 option (b): a panic that reached an unsequenced-operand probe
    -- frame draws the `unseqPanic` site; the checker refuses it (fail
    -- closed) — the CLI enumerator carries such rows.
    else if consumesUnseqPanic c then false
    -- Stage B/D: the `unseq` scheduler's pick position draws the `unseqNext`
    -- site at bound `|ready|`, read off the frame (`unseqNextBound`). A
    -- bound-≤-1 consult pops nothing (G-U), so the step is oblivious; a
    -- WIDE pick is a genuine draw — not oblivious, and the certified dedup
    -- engine enumerates its branches instead (`innerVecs`, route α of
    -- v2.1 §3.6, Stage D).
    else if consumesUnseqNext c then decide (unseqNextBound c ≤ 1)
    else
      match arrivalCases ctx s ts i c with
      | .ok .cellPath => true
      | .ok (.single _ cs) => cs.length == 1
      | _ => false

end GoLean.GoCore.Machine
