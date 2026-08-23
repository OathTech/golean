import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Specs.Raft.AbsState

/-!
# A4-U1 pilot: per-callee interpreter-run equations (generic layer)

The seam design's layer (B) at its smallest instance: run equations
for the callees of `raft.raft.becomeFollower`, stated over an ABSTRACT
machine state with the executable facts as hypotheses (StepKit
conditioned style), program-generic (no pin import here — the pinned
instantiation and the discharge witness live in
`Specs/Raft/BecomeFollowerWitness.lean`).

Layering: proof infrastructure, never imported by statement modules.

Kit-gap register for this module (per-item disposition in the arc
log): `storeTarget_field` below is the struct-field store form the kit
lacks (§23 "struct-cell generalization, parked" — the raft target hits
it immediately; promotion-ledger candidate, ≥2 consumers certain).
-/

namespace GoLean.RaftSeam

open GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

/-! ## Struct-field store (the kit gap, closed locally)

`storeTarget` at a `fieldAddr` target: anchor is the pointer value,
one `.field` step, no indexes. `storeLoc` loads the base cell's struct,
sets the field, and re-stores the WHOLE struct at the cell's declared
type — so the conditioned facts are the cell lookup, the field set,
and the whole-struct normalization. -/

/-- Struct-field store through a pointer anchor, conditioned on the
cell, the field update, and the struct re-normalization. The
`raft.raft`-typed cells of the twin hit this on every handler field
write. -/
theorem storeTarget_field {σ : ExecState} {a : Addr} {tid : TypeId}
    {fld : String} {ty : Ty} {fs fs' : Array (String × GoValue)}
    {v nv : GoValue}
    (hcell : Heap.lookup σ.heap (.base a) = some ⟨some ty, .struct tid fs⟩)
    (hset : StructFields.set fs fld v = .ok fs')
    (hnorm : normalizeValueForTy σ ty (.struct tid fs') = .ok nv) :
    storeTarget σ (.chain (.addr (.base a)) [] [.field tid fld]) v
      = .ok { σ with heap := Heap.set σ.heap (.base a) ⟨some ty, nv⟩ } := by
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind, Except.bind,
    pure, Except.pure, storeLoc, loadLoc, hcell, hset, hnorm, bne_self_eq_false,
    Bool.false_and]
  rfl

/-! ## The leaf: `raft.raft.abortLeaderTransfer`

The smallest callee on `becomeFollower`'s dynamic path — one
struct-field store (`r.leadTransferee = None`). Its span equation
validates the pilot's equation FORM end to end: abstract state, frame
entry conditioned on `enterFrame`, a symbolic-struct field store, frame
exit, exact step count. Body literal transcribed from the decoded pin
(`artifacts/probe/DumpFuncs.lean` output); the pinned instantiation
re-checks it against `twinLowered` by `rfl`. -/

/-- The lowered body of `raft.raft.abortLeaderTransfer`, verbatim. -/
def altBody : Stmt :=
  .block #[] #[.seqn #[.assign
    (.addr (.fieldAddr (.var "r") ⟨"raft.raft"⟩ "leadTransferee"))
    (.intLit 0 .uint64)]]

def fidALT : FuncId := ⟨"raft.raft.abortLeaderTransfer"⟩

set_option maxHeartbeats 1000000 in
/-- **Span equation for `abortLeaderTransfer`** (the pilot's leaf):
from the drained call configuration, the run crosses the whole call —
frame entry, body, frame exit — in exactly 15 steps, no choices
consumed, landing on the caller's continuation with the raft cell's
`leadTransferee` field stored (as part of the re-normalized struct)
and one fresh param cell at the old `nextAddr`. -/
theorem alt_call_span (σ σ₁ : ExecState) (a : Addr) (altF : Func)
    (fenv : LocalEnv) (env : LocalEnv) (k : Cont) (ch : Choices)
    {ty : Ty} {fs fs' : Array (String × GoValue)}
    {nv : GoValue}
    (henter : enterFrame σ fidALT [.addr (.base a)]
      = .ok (altF, fenv, [], σ₁))
    (hbody : altF.body = altBody)
    (hfenv : fenv = [[("r", .base ⟨σ.nextAddr⟩)]])
    (hcellr : Heap.lookup σ₁.heap (.base ⟨σ.nextAddr⟩)
      = some ⟨some (.pointer (.defined ⟨"raft.raft"⟩)), .addr (.base a)⟩)
    (hcell : Heap.lookup σ₁.heap (.base a)
      = some ⟨some ty, .struct ⟨"raft.raft"⟩ fs⟩)
    (hset : StructFields.set fs "leadTransferee" (.int 0 .uint64) = .ok fs')
    (hnorm : normalizeValueForTy σ₁ ty (.struct ⟨"raft.raft"⟩ fs') = .ok nv) :
    stepFnIter 15 σ (.retV (.addr (.base a)) (.callArgsK fidALT [] [] [] env k)) ch
      = .ok (.next k,
          { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }, ch) := by
  -- Naming the recurring scene: the frame, the body scope's env, the
  -- assign statement, and the target spine continuation.
  have e1 : stepFn σ (.retV (.addr (.base a)) (.callArgsK fidALT [] [] [] env k)) ch
      = .ok (.exec altBody fenv (.frame [] env [] [] k altF.wrapper), σ₁, ch) := by
    have h := stepFn_call_enter (plans := []) (vals := [])
      (v := .addr (.base a)) (k := k) (env := env) (ch := ch) henter
    rwa [hbody] at h
  -- window 1 (2 steps): entry + block scope push
  have w1 : stepFnIter 2 σ
      (.retV (.addr (.base a)) (.callArgsK fidALT [] [] [] env k)) ch
      = .ok (.next (.seq [.seqn #[.assign
            (.addr (.fieldAddr (.var "r") ⟨"raft.raft"⟩ "leadTransferee"))
            (.intLit 0 .uint64)]] ([] :: fenv)
          (.frame [] env [] [] k altF.wrapper)), σ₁, ch) := by
    simp only [stepFnIter, e1, altBody, stepFn_block, Bind.bind, Except.bind]
  -- window 2 (1 step): seq pop
  have w2 : stepFnIter 1 σ₁
      (.next (.seq [.seqn #[.assign
          (.addr (.fieldAddr (.var "r") ⟨"raft.raft"⟩ "leadTransferee"))
          (.intLit 0 .uint64)]] ([] :: fenv)
        (.frame [] env [] [] k altF.wrapper))) ch
      = .ok (.exec (.seqn #[.assign
            (.addr (.fieldAddr (.var "r") ⟨"raft.raft"⟩ "leadTransferee"))
            (.intLit 0 .uint64)]) ([] :: fenv)
          (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper)), σ₁, ch) := rfl
  -- window 3 (1 step): the seqn splice (env-equality discharge)
  have w3 : stepFnIter 1 σ₁
      (.exec (.seqn #[.assign
          (.addr (.fieldAddr (.var "r") ⟨"raft.raft"⟩ "leadTransferee"))
          (.intLit 0 .uint64)]) ([] :: fenv)
        (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper))) ch
      = .ok (.next (.seq [.assign
            (.addr (.fieldAddr (.var "r") ⟨"raft.raft"⟩ "leadTransferee"))
            (.intLit 0 .uint64)] ([] :: fenv)
          (.frame [] env [] [] k altF.wrapper)), σ₁, ch) := by
    simp only [stepFnIter, stepFn_seqn_splice, Bind.bind, Except.bind]
    rfl
  -- window 4 (2 steps): seq pop + assign plan
  have w4 : stepFnIter 2 σ₁
      (.next (.seq [.assign
          (.addr (.fieldAddr (.var "r") ⟨"raft.raft"⟩ "leadTransferee"))
          (.intLit 0 .uint64)] ([] :: fenv)
        (.frame [] env [] [] k altF.wrapper))) ch
      = .ok (.evalE (.var "r") ([] :: fenv)
          (.tgtOpK (.chain [.field ⟨"raft.raft"⟩ "leadTransferee"]) [] [] [] []
            .vals [.intLit 0 .uint64] [] (.seqn #[]) ([] :: fenv)
            (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper))), σ₁, ch) := rfl
  -- window 5 (1 step): the receiver read
  have henv2 : LocalEnv.lookup ([] :: fenv) "r" = some (.base ⟨σ.nextAddr⟩) := by
    rw [hfenv]; rfl
  have w5 : stepFnIter 1 σ₁
      (.evalE (.var "r") ([] :: fenv)
        (.tgtOpK (.chain [.field ⟨"raft.raft"⟩ "leadTransferee"]) [] [] [] []
          .vals [.intLit 0 .uint64] [] (.seqn #[]) ([] :: fenv)
          (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper)))) ch
      = .ok (.retV (.addr (.base a))
          (.tgtOpK (.chain [.field ⟨"raft.raft"⟩ "leadTransferee"]) [] [] [] []
            .vals [.intLit 0 .uint64] [] (.seqn #[]) ([] :: fenv)
            (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper))), σ₁, ch) := by
    simp only [stepFnIter, stepFn_var henv2 hcellr, Bind.bind, Except.bind]
  -- window 6 (3 steps): target completes, RHS literal, into phase 2
  have w6 : stepFnIter 3 σ₁
      (.retV (.addr (.base a))
        (.tgtOpK (.chain [.field ⟨"raft.raft"⟩ "leadTransferee"]) [] [] [] []
          .vals [.intLit 0 .uint64] [] (.seqn #[]) ([] :: fenv)
          (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper)))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base a)) [] [.field ⟨"raft.raft"⟩ "leadTransferee"]]
          [.int 0 .uint64] (.seqn #[]) ([] :: fenv)
          (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper))), σ₁, ch) := rfl
  -- window 7 (1 step): THE STORE
  have hstore := storeTarget_field (σ := σ₁) hcell hset hnorm
  have w7 : stepFnIter 1 σ₁
      (.next (.storeK
        [.chain (.addr (.base a)) [] [.field ⟨"raft.raft"⟩ "leadTransferee"]]
        [.int 0 .uint64] (.seqn #[]) ([] :: fenv)
        (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: fenv)
          (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper))),
          { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }, ch) := by
    simp only [stepFnIter, stepFn_store_step hstore, Bind.bind, Except.bind]
  -- window 8 (1 step): drained store runs the (empty) body
  have w8 : stepFnIter 1
      { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }
      (.next (.storeK [] [] (.seqn #[]) ([] :: fenv)
        (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper)))) ch
      = .ok (.exec (.seqn #[]) ([] :: fenv)
          (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper)),
          { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }, ch) := rfl
  -- window 9 (1 step): empty splice (env-equality discharge again)
  have w9 : stepFnIter 1
      { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }
      (.exec (.seqn #[]) ([] :: fenv)
        (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper))) ch
      = .ok (.next (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper)),
          { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }, ch) := by
    simp only [stepFnIter, stepFn_seqn_splice, Bind.bind, Except.bind]
    rfl
  -- window 10 (2 steps): scope discard + frame pop
  have w10 : stepFnIter 2
      { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }
      (.next (.seq [] ([] :: fenv) (.frame [] env [] [] k altF.wrapper))) ch
      = .ok (.next k,
          { σ₁ with heap := Heap.set σ₁.heap (.base a) ⟨some ty, nv⟩ }, ch) := rfl
  -- assemble 15 = 2+1+1+2+1+3+1+1+1+2
  exact stepFnIter_chain w1 (stepFnIter_chain w2 (stepFnIter_chain w3
    (stepFnIter_chain w4 (stepFnIter_chain w5 (stepFnIter_chain w6
    (stepFnIter_chain w7 (stepFnIter_chain w8 (stepFnIter_chain w9 w10))))))))

end GoLean.RaftSeam
