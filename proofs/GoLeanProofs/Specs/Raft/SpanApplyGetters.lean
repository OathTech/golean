import GoLeanProofs.Specs.Raft.SpanCells

/-!
# The four pb-getter call spans (A4d-SM1 item 4, the banked piece)

`main.twin.apply` opens on the four protobuf getters —
`raftpb.Entry.GetIndex/GetTerm/GetType/GetData` (nil-checked
pointer-field reads; `Index`/`Term`/`Type` are pointer fields, `Data`
is a direct byte slice). This module pins each getter verbatim
(whole-`Func`, the `utoa_pinned` pattern) and proves its CALL SPAN at
the populated-entry shape: from the delivered receiver value to the
caller's resumption, the target cell holding EXACTLY the entry's
field value, the two dead frame cells between the frontiers, frame
respect throughout.

Scope note (the boundary line, priced in the log): these four spans
are the banked item-4 piece. The FULL `apply` walk assembly
(`s23_span_computes`) additionally needs two UNBANKED map-fragment
models — the string-keyed `got` map and the slot-struct-valued
`byIndex` map (the latter with defined-value-type normalization, the
U23 table-footprint class) — measured at more than twice the banked
price; the arc's chartered boundary-stop applies there, with the
measurement recorded in the log.

LINEAGE: P-H call-span composition over conditioned singles (the
`utoa_call_span`/`viol_call_span` pattern).
-/

namespace GoLean.RaftSeam.SpanApplyGetters

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk (envB flagCell flagSet stepFn_ref normalize_bool
  lookup_pushScope)
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ## 1. The spelled getters + pins -/

abbrev tyEntD : Ty := .defined ⟨"raftpb.Entry"⟩
abbrev tidE : TypeId := ⟨"raftpb.Entry"⟩

/-- A pointer-field getter's body (`Index`/`Term` at uint64;
`Type` at the `EntryType` alias). -/
def ptrGetterBody (f : String) (ty : Ty) (zero : Expr) : Stmt :=
  .block #[]
    #[.ifThenElse
        (.and
          (.neqCmp (.pointer tyEntD) (.var "x") (.nil none))
          (.neqCmp (.pointer ty)
            (.fieldGet (.deref (.var "x") tyEntD) tidE f)
            (.nil none)))
        (.block #[] #[.seqn
          #[.assign (.var "$res0")
              (.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f)
                ty),
            .returnStmt]])
        (.seqn #[]),
      .seqn #[.assign (.var "$res0") zero, .returnStmt]]

def getIndexFunc : Func :=
  { id := ⟨"raftpb.Entry.GetIndex"⟩,
    args := #[{ id := "x", typ := .pointer tyEntD }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := ptrGetterBody "Index" (.int .uint64)
      (.intLit 0 .uint64) }

def getTermFunc : Func :=
  { id := ⟨"raftpb.Entry.GetTerm"⟩,
    args := #[{ id := "x", typ := .pointer tyEntD }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := ptrGetterBody "Term" (.int .uint64)
      (.intLit 0 .uint64) }

def getTypeFunc : Func :=
  { id := ⟨"raftpb.Entry.GetType"⟩,
    args := #[{ id := "x", typ := .pointer tyEntD }],
    results := #[{ id := "$res0", typ := .defined ⟨"raftpb.EntryType"⟩ }],
    body := ptrGetterBody "Type" (.defined ⟨"raftpb.EntryType"⟩)
      (.intLit 0 .int32) }

def getDataFunc : Func :=
  { id := ⟨"raftpb.Entry.GetData"⟩,
    args := #[{ id := "x", typ := .pointer tyEntD }],
    results := #[{ id := "$res0", typ := .slice (.int .uint8) }],
    body := .block #[]
      #[.ifThenElse
          (.neqCmp (.pointer tyEntD) (.var "x") (.nil none))
          (.block #[] #[.seqn
            #[.assign (.var "$res0")
                (.fieldGet (.deref (.var "x") tyEntD) tidE "Data"),
              .returnStmt]])
          (.seqn #[]),
        .seqn #[.assign (.var "$res0")
            (.nil (some (.slice (.int .uint8)))),
          .returnStmt]] }

/-- **PINS**: the four spelled getters ARE the pinned lowering's
(`artifacts/probe/getterdump.out`). -/
theorem getIndex_pinned :
    findFunctionIn? twinLowered.funcs ⟨"raftpb.Entry.GetIndex"⟩
      = some getIndexFunc := by
  kernel_rfl

theorem getTerm_pinned :
    findFunctionIn? twinLowered.funcs ⟨"raftpb.Entry.GetTerm"⟩
      = some getTermFunc := by
  kernel_rfl

theorem getType_pinned :
    findFunctionIn? twinLowered.funcs ⟨"raftpb.Entry.GetType"⟩
      = some getTypeFunc := by
  kernel_rfl

theorem getData_pinned :
    findFunctionIn? twinLowered.funcs ⟨"raftpb.Entry.GetData"⟩
      = some getDataFunc := by
  kernel_rfl

/-- The `raftpb.EntryType` declaration pin (a defined `int32` — its
normalization footprint at the type table). -/
theorem entryTypeDecl_pinned :
    TypeEnv.lookup twinTypes ⟨"raftpb.EntryType"⟩
      = some (.defined (.int .int32)) := by
  kernel_rfl

/-! ## 2. The shared singles -/

/-- `!=` at a pointer type on an address vs `nil`: `true`
(constructor-headed, any state, any address). -/
theorem applyStrictOp_neq_addr_nil {σ : ExecState} {ty : Ty} {l : Loc} :
    applyStrictOp σ (.neqCmp (.pointer ty)) [.addr l, .nil]
      = .ok (.bool true, σ) := by
  with_unfolding_all rfl

/-- EntryType normalization at an in-range `int32` payload (the type
table resolves the alias to `int32`). -/
theorem normalize_entryType {σ : ExecState}
    (htypes : σ.types = twinTypes) {v : Int}
    (h0 : -(2 ^ 31) ≤ v) (h1 : v < 2 ^ 31) :
    normalizeValueForTy σ (.defined ⟨"raftpb.EntryType"⟩)
        (.int v .int32)
      = .ok (.int v .int32) := by
  cases σ with
  | mk types functions methods methodSets heap nextAddr =>
    simp only at htypes
    subst htypes
    have hraw : normalizeValueForTy
        ⟨twinTypes, functions, methods, methodSets, heap, nextAddr⟩
        (.defined ⟨"raftpb.EntryType"⟩) (.int v .int32)
        = .ok (.int (IntKind.normalize .int32 v) .int32) := by
      kernel_rfl
    rw [hraw]
    rw [show IntKind.normalize .int32 v = v from by
      simp only [IntKind.normalize, IntKind.bits?, IntKind.signed,
        if_true]
      split <;> omega]

/-! ## 3. The frame entries (kernel, at the twin tables) -/

/-- The getters' frame environment. -/
def getterEnv (na : Nat) : LocalEnv :=
  [[("$res0", .base ⟨na + 1⟩), ("x", .base ⟨na⟩)]]

/-- The receiver frame cell. -/
abbrev xCell (lw : Nat) : HeapCell :=
  ⟨some (.pointer tyEntD), .addr (.base ⟨lw⟩)⟩

theorem getIndex_enterFrame (h : Heap) (na lw : Nat) :
    enterFrame (twinSt h na) ⟨"raftpb.Entry.GetIndex"⟩
        [.addr (.base ⟨lw⟩)]
      = .ok (getIndexFunc, getterEnv na, [.base ⟨na + 1⟩],
          twinSt (Heap.set (Heap.set h (.base ⟨na⟩) (xCell lw))
            (.base ⟨na + 1⟩) ⟨some (.int .uint64), .int 0 .uint64⟩)
            (na + 2)) := by
  kernel_rfl

theorem getTerm_enterFrame (h : Heap) (na lw : Nat) :
    enterFrame (twinSt h na) ⟨"raftpb.Entry.GetTerm"⟩
        [.addr (.base ⟨lw⟩)]
      = .ok (getTermFunc, getterEnv na, [.base ⟨na + 1⟩],
          twinSt (Heap.set (Heap.set h (.base ⟨na⟩) (xCell lw))
            (.base ⟨na + 1⟩) ⟨some (.int .uint64), .int 0 .uint64⟩)
            (na + 2)) := by
  kernel_rfl

theorem getType_enterFrame (h : Heap) (na lw : Nat) :
    enterFrame (twinSt h na) ⟨"raftpb.Entry.GetType"⟩
        [.addr (.base ⟨lw⟩)]
      = .ok (getTypeFunc, getterEnv na, [.base ⟨na + 1⟩],
          twinSt (Heap.set (Heap.set h (.base ⟨na⟩) (xCell lw))
            (.base ⟨na + 1⟩)
            ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
            (na + 2)) := by
  kernel_rfl

theorem getData_enterFrame (h : Heap) (na lw : Nat) :
    enterFrame (twinSt h na) ⟨"raftpb.Entry.GetData"⟩
        [.addr (.base ⟨lw⟩)]
      = .ok (getDataFunc, getterEnv na, [.base ⟨na + 1⟩],
          twinSt (Heap.set (Heap.set h (.base ⟨na⟩) (xCell lw))
            (.base ⟨na + 1⟩)
            ⟨some (.slice (.int .uint8)),
              .slice ⟨none, 0, 0, 0⟩⟩)
            (na + 2)) := by
  kernel_rfl

/-- Slice normalization is the identity (no arm matches a slice
type; any value, any state). -/
theorem normalize_slice {σ : ExecState} {t : Ty} {v : GoValue} :
    normalizeValueForTy σ (.slice t) v = .ok v := by
  simp only [normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, pure, Except.pure]

/-! ## 4. The generic pointer-getter body walk -/

section Body

variable {f : String} {ty : Ty} {zero : Expr} {na lw li : Nat}
  {dtyEw dtyI : Option Ty} {fsE : Array (String × GoValue)}
  {fv fv' : GoValue} {rty : Ty} {resDef : GoValue}

/-- **The pointer-getter body span** (43 steps, populated shape):
nil checks pass, the field pointer dereferenced, the result stored
(normalized at the result type by the instance's `hnorm`), the frame
returned. -/
theorem ptrGetter_body_span
    (σ' : ExecState) (ch : Choices) (FK : Cont)
    (hx : Heap.lookup σ'.heap (.base ⟨na⟩) = some (xCell lw))
    (hres : Heap.lookup σ'.heap (.base ⟨na + 1⟩)
      = some ⟨some rty, resDef⟩)
    (hEw : Heap.lookup σ'.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hf : StructFields.lookup fsE f = some (.addr (.base ⟨li⟩)))
    (hIc : Heap.lookup σ'.heap (.base ⟨li⟩) = some ⟨dtyI, fv⟩)
    (hnorm : normalizeValueForTy σ' rty fv = .ok fv') :
    stepFnIter 43 σ'
        (.exec (ptrGetterBody f ty zero) (getterEnv na) FK) ch
      = .ok (.returning FK,
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }, ch) := by
  let env1g : LocalEnv := [] :: getterEnv na
  let zeroSeqn : Stmt := .seqn #[.assign (.var "$res0") zero,
    .returnStmt]
  let KG : Cont := .seq [zeroSeqn] env1g FK
  -- B1+B2: block/pop + if entry + and + neq1 dispatch (5 steps)
  have hB1 : stepFnIter 5 σ'
      (.exec (ptrGetterBody f ty zero) (getterEnv na) FK) ch
      = .ok (.evalE (.var "x") env1g
          (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
            (.andK (.neqCmp (.pointer ty)
                (.fieldGet (.deref (.var "x") tyEntD) tidE f)
                (.nil none)) env1g
              (.ifK (.block #[] #[.seqn
                  #[.assign (.var "$res0")
                      (.deref (.fieldGet (.deref (.var "x") tyEntD)
                        tidE f) ty),
                    .returnStmt]])
                (.seqn #[]) env1g KG))), σ', ch) := by
    have b1 : stepFnIter 2 σ'
        (.exec (ptrGetterBody f ty zero) (getterEnv na) FK) ch
        = .ok (.exec (.ifThenElse
            (.and
              (.neqCmp (.pointer tyEntD) (.var "x") (.nil none))
              (.neqCmp (.pointer ty)
                (.fieldGet (.deref (.var "x") tyEntD) tidE f)
                (.nil none)))
            (.block #[] #[.seqn
              #[.assign (.var "$res0")
                  (.deref (.fieldGet (.deref (.var "x") tyEntD)
                    tidE f) ty),
                .returnStmt]])
            (.seqn #[])) env1g KG, σ', ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_block)
        (stepFnIter_one stepFn_seq_pop)
    have b2 : stepFnIter 3 σ' (.exec (.ifThenElse
        (.and
          (.neqCmp (.pointer tyEntD) (.var "x") (.nil none))
          (.neqCmp (.pointer ty)
            (.fieldGet (.deref (.var "x") tyEntD) tidE f)
            (.nil none)))
        (.block #[] #[.seqn
          #[.assign (.var "$res0")
              (.deref (.fieldGet (.deref (.var "x") tyEntD)
                tidE f) ty),
            .returnStmt]])
        (.seqn #[])) env1g KG) ch
        = .ok (.evalE (.var "x") env1g
            (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
              (.andK (.neqCmp (.pointer ty)
                  (.fieldGet (.deref (.var "x") tyEntD) tidE f)
                  (.nil none)) env1g
                (.ifK (.block #[] #[.seqn
                    #[.assign (.var "$res0")
                        (.deref (.fieldGet (.deref (.var "x") tyEntD)
                          tidE f) ty),
                      .returnStmt]])
                  (.seqn #[]) env1g KG))), σ', ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain b1 b2
  -- B3: the x read
  have hB3 : stepFnIter 1 σ' (.evalE (.var "x") env1g
      (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
        (.andK (.neqCmp (.pointer ty)
            (.fieldGet (.deref (.var "x") tyEntD) tidE f)
            (.nil none)) env1g
          (.ifK (.block #[] #[.seqn
              #[.assign (.var "$res0")
                  (.deref (.fieldGet (.deref (.var "x") tyEntD)
                    tidE f) ty),
                .returnStmt]])
            (.seqn #[]) env1g KG)))) ch
      = .ok (.retV (.addr (.base ⟨lw⟩))
          (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
            (.andK (.neqCmp (.pointer ty)
                (.fieldGet (.deref (.var "x") tyEntD) tidE f)
                (.nil none)) env1g
              (.ifK (.block #[] #[.seqn
                  #[.assign (.var "$res0")
                      (.deref (.fieldGet (.deref (.var "x") tyEntD)
                        tidE f) ty),
                    .returnStmt]])
                (.seqn #[]) env1g KG))), σ', ch) :=
    stepFnIter_one (stepFn_var (henv := rfl) (hlook := hx))
  -- B4+B5: nil + the first neq (3 steps)
  have hB5 : stepFnIter 3 σ' (.retV (.addr (.base ⟨lw⟩))
      (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
        (.andK (.neqCmp (.pointer ty)
            (.fieldGet (.deref (.var "x") tyEntD) tidE f)
            (.nil none)) env1g
          (.ifK (.block #[] #[.seqn
              #[.assign (.var "$res0")
                  (.deref (.fieldGet (.deref (.var "x") tyEntD)
                    tidE f) ty),
                .returnStmt]])
            (.seqn #[]) env1g KG)))) ch
      = .ok (.retV (.bool true)
          (.andK (.neqCmp (.pointer ty)
              (.fieldGet (.deref (.var "x") tyEntD) tidE f)
              (.nil none)) env1g
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0")
                    (.deref (.fieldGet (.deref (.var "x") tyEntD)
                      tidE f) ty),
                  .returnStmt]])
              (.seqn #[]) env1g KG)), σ', ch) := by
    have b4 : stepFnIter 2 σ' (.retV (.addr (.base ⟨lw⟩))
        (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
          (.andK (.neqCmp (.pointer ty)
              (.fieldGet (.deref (.var "x") tyEntD) tidE f)
              (.nil none)) env1g
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0")
                    (.deref (.fieldGet (.deref (.var "x") tyEntD)
                      tidE f) ty),
                  .returnStmt]])
              (.seqn #[]) env1g KG)))) ch
        = .ok (.retV (.nil)
            (.strictK (.neqCmp (.pointer tyEntD))
              [.addr (.base ⟨lw⟩)] [] env1g
              (.andK (.neqCmp (.pointer ty)
                  (.fieldGet (.deref (.var "x") tyEntD) tidE f)
                  (.nil none)) env1g
                (.ifK (.block #[] #[.seqn
                    #[.assign (.var "$res0")
                        (.deref (.fieldGet (.deref (.var "x") tyEntD)
                          tidE f) ty),
                      .returnStmt]])
                  (.seqn #[]) env1g KG))), σ', ch) := by
      with_unfolding_all rfl
    refine stepFnIter_chain b4 (stepFnIter_one
      (stepFn_strict_apply (h := ?_)))
    rw [show (List.reverse [GoValue.nil,
        GoValue.addr (.base ⟨lw⟩)])
      = [GoValue.addr (.base ⟨lw⟩), GoValue.nil] from rfl]
    exact applyStrictOp_neq_addr_nil
  -- B6+B7: andK true + neq2 dispatch (2 steps)
  have hB6 : stepFnIter 2 σ' (.retV (.bool true)
      (.andK (.neqCmp (.pointer ty)
          (.fieldGet (.deref (.var "x") tyEntD) tidE f)
          (.nil none)) env1g
        (.ifK (.block #[] #[.seqn
            #[.assign (.var "$res0")
                (.deref (.fieldGet (.deref (.var "x") tyEntD)
                  tidE f) ty),
              .returnStmt]])
          (.seqn #[]) env1g KG))) ch
      = .ok (.evalE (.fieldGet (.deref (.var "x") tyEntD) tidE f)
          env1g
          (.strictK (.neqCmp (.pointer ty)) [] [.nil none] env1g
            (.boolK
              (.ifK (.block #[] #[.seqn
                  #[.assign (.var "$res0")
                      (.deref (.fieldGet (.deref (.var "x") tyEntD)
                        tidE f) ty),
                    .returnStmt]])
                (.seqn #[]) env1g KG))), σ', ch) := by
    with_unfolding_all rfl
  -- B8: the field-pointer read (5)
  have hB8 : stepFnIter 5 σ'
      (.evalE (.fieldGet (.deref (.var "x") tyEntD) tidE f) env1g
        (.strictK (.neqCmp (.pointer ty)) [] [.nil none] env1g
          (.boolK
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0")
                    (.deref (.fieldGet (.deref (.var "x") tyEntD)
                      tidE f) ty),
                  .returnStmt]])
              (.seqn #[]) env1g KG)))) ch
      = .ok (.retV (.addr (.base ⟨li⟩))
          (.strictK (.neqCmp (.pointer ty)) [] [.nil none] env1g
            (.boolK
              (.ifK (.block #[] #[.seqn
                  #[.assign (.var "$res0")
                      (.deref (.fieldGet (.deref (.var "x") tyEntD)
                        tidE f) ty),
                    .returnStmt]])
                (.seqn #[]) env1g KG))), σ', ch) :=
    read_field_seg (henv := rfl) (hp := hx) (hw := hEw) (hf := hf)
  -- B9-B12: nil, neq2, boolK, ifK (5 steps) → the then-block
  have hB9 : stepFnIter 5 σ' (.retV (.addr (.base ⟨li⟩))
      (.strictK (.neqCmp (.pointer ty)) [] [.nil none] env1g
        (.boolK
          (.ifK (.block #[] #[.seqn
              #[.assign (.var "$res0")
                  (.deref (.fieldGet (.deref (.var "x") tyEntD)
                    tidE f) ty),
                .returnStmt]])
            (.seqn #[]) env1g KG)))) ch
      = .ok (.exec (.block #[] #[.seqn
          #[.assign (.var "$res0")
              (.deref (.fieldGet (.deref (.var "x") tyEntD)
                tidE f) ty),
            .returnStmt]]) env1g KG, σ', ch) := by
    have b9 : stepFnIter 2 σ' (.retV (.addr (.base ⟨li⟩))
        (.strictK (.neqCmp (.pointer ty)) [] [.nil none] env1g
          (.boolK
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0")
                    (.deref (.fieldGet (.deref (.var "x") tyEntD)
                      tidE f) ty),
                  .returnStmt]])
              (.seqn #[]) env1g KG)))) ch
        = .ok (.retV (.nil)
            (.strictK (.neqCmp (.pointer ty)) [.addr (.base ⟨li⟩)]
              [] env1g
              (.boolK
                (.ifK (.block #[] #[.seqn
                    #[.assign (.var "$res0")
                        (.deref (.fieldGet (.deref (.var "x") tyEntD)
                          tidE f) ty),
                      .returnStmt]])
                  (.seqn #[]) env1g KG))), σ', ch) := by
      with_unfolding_all rfl
    have b10 : stepFnIter 1 σ' (.retV (.nil)
        (.strictK (.neqCmp (.pointer ty)) [.addr (.base ⟨li⟩)]
          [] env1g
          (.boolK
            (.ifK (.block #[] #[.seqn
                #[.assign (.var "$res0")
                    (.deref (.fieldGet (.deref (.var "x") tyEntD)
                      tidE f) ty),
                  .returnStmt]])
              (.seqn #[]) env1g KG)))) ch
        = .ok (.retV (.bool true)
            (.boolK
              (.ifK (.block #[] #[.seqn
                  #[.assign (.var "$res0")
                      (.deref (.fieldGet (.deref (.var "x") tyEntD)
                        tidE f) ty),
                    .returnStmt]])
                (.seqn #[]) env1g KG)), σ', ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.nil,
          GoValue.addr (.base ⟨li⟩)])
        = [GoValue.addr (.base ⟨li⟩), GoValue.nil] from rfl]
      exact applyStrictOp_neq_addr_nil
    have b11 : stepFnIter 2 σ' (.retV (.bool true)
        (.boolK
          (.ifK (.block #[] #[.seqn
              #[.assign (.var "$res0")
                  (.deref (.fieldGet (.deref (.var "x") tyEntD)
                    tidE f) ty),
                .returnStmt]])
            (.seqn #[]) env1g KG))) ch
        = .ok (.exec (.block #[] #[.seqn
            #[.assign (.var "$res0")
                (.deref (.fieldGet (.deref (.var "x") tyEntD)
                  tidE f) ty),
              .returnStmt]]) env1g KG, σ', ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain b9 (stepFnIter_chain b10 b11)
  -- B13+B14: block/pop + splice/pop (4 steps) → the assign
  let env2g : LocalEnv := [] :: env1g
  have hB13 : stepFnIter 4 σ' (.exec (.block #[] #[.seqn
      #[.assign (.var "$res0")
          (.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f) ty),
        .returnStmt]]) env1g KG) ch
      = .ok (.exec (.assign (.var "$res0")
          (.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f) ty))
          env2g (.seq [.returnStmt] env2g KG),
        σ', ch) := by
    have b13 : stepFnIter 2 σ' (.exec (.block #[] #[.seqn
        #[.assign (.var "$res0")
            (.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f)
              ty),
          .returnStmt]]) env1g KG) ch
        = .ok (.exec (.seqn
            #[.assign (.var "$res0")
                (.deref (.fieldGet (.deref (.var "x") tyEntD)
                  tidE f) ty),
              .returnStmt]) env2g (.seq [] env2g KG), σ', ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_block)
        (stepFnIter_one stepFn_seq_pop)
    exact stepFnIter_chain b13 (stepFnIter_splice_pop
      (ss := #[.assign (.var "$res0")
          (.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f) ty),
        .returnStmt]) rfl)
  -- B15-B20: the assign walk to the field value (10 steps)
  let KA : Cont := .rhsK .vals
    [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] [] (.seqn #[]) env2g
    (.seq [.returnStmt] env2g KG)
  have hB15 : stepFnIter 2 σ' (.exec (.assign (.var "$res0")
      (.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f) ty))
      env2g (.seq [.returnStmt] env2g KG)) ch
      = .ok (.retV (.addr (.base ⟨na + 1⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f) ty]
            [] (.seqn #[]) env2g
            (.seq [.returnStmt] env2g KG)),
        σ', ch) := by
    have b15 : stepFnIter 1 σ' (.exec (.assign (.var "$res0")
        (.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f) ty))
        env2g (.seq [.returnStmt] env2g KG)) ch
        = .ok (.evalE (.ref "$res0") env2g
            (.tgtOpK (.chain []) [] [] [] [] .vals
              [.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f)
                ty] [] (.seqn #[]) env2g
              (.seq [.returnStmt] env2g KG)),
          σ', ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain b15 (stepFnIter_one (stepFn_ref rfl))
  have hB17 : stepFnIter 2 σ' (.retV (.addr (.base ⟨na + 1⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.deref (.fieldGet (.deref (.var "x") tyEntD) tidE f) ty]
        [] (.seqn #[]) env2g
        (.seq [.returnStmt] env2g KG))) ch
      = .ok (.evalE (.fieldGet (.deref (.var "x") tyEntD) tidE f)
          env2g (.strictK (.deref ty) [] [] env2g KA), σ', ch) := by
    with_unfolding_all rfl
  have hB19 : stepFnIter 5 σ'
      (.evalE (.fieldGet (.deref (.var "x") tyEntD) tidE f) env2g
        (.strictK (.deref ty) [] [] env2g KA)) ch
      = .ok (.retV (.addr (.base ⟨li⟩))
          (.strictK (.deref ty) [] [] env2g KA), σ', ch) :=
    read_field_seg (henv := rfl) (hp := hx) (hw := hEw) (hf := hf)
  have hB20 : stepFnIter 1 σ' (.retV (.addr (.base ⟨li⟩))
      (.strictK (.deref ty) [] [] env2g KA)) ch
      = .ok (.retV fv KA, σ', ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.addr (.base ⟨li⟩)])
      = [GoValue.addr (.base ⟨li⟩)] from rfl]
    exact GoLean.RaftSeam.DriverNet.applyStrictOp_deref
      (c := ⟨dtyI, fv⟩) hIc
  -- B21+B22: → the result store (2 steps)
  have hB21 : stepFnIter 1 σ' (.retV fv KA) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 1⟩)) [] []]
          [fv] (.seqn #[]) env2g
          (.seq [.returnStmt] env2g KG)), σ', ch) := by
    with_unfolding_all rfl
  have hB22 : stepFnIter 1 σ' (.next (.storeK
      [.chain (.addr (.base ⟨na + 1⟩)) [] []] [fv] (.seqn #[]) env2g
      (.seq [.returnStmt] env2g KG))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env2g
          (.seq [.returnStmt] env2g KG)),
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := rty) (old := resDef)
        (hlook := hres) (hnorm := hnorm)))
  -- B23+B24: drain + return unwind (6 steps)
  have hB23 : stepFnIter 6
      { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }
      (.next (.storeK [] [] (.seqn #[]) env2g
        (.seq [.returnStmt] env2g KG))) ch
      = .ok (.returning FK,
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }, ch) := by
    have b23 : stepFnIter 3
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }
        (.next (.storeK [] [] (.seqn #[]) env2g
          (.seq [.returnStmt] env2g KG))) ch
        = .ok (.exec .returnStmt env2g (.seq [] env2g KG),
          { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }, ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
        (stepFnIter_splice_pop (ss := #[]) rfl)
    have b24 : stepFnIter 3
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }
        (.exec .returnStmt env2g (.seq [] env2g KG)) ch
        = .ok (.returning FK,
          { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some rty, fv'⟩ }, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain b23 b24
  exact stepFnIter_chain hB1 (stepFnIter_chain hB3
    (stepFnIter_chain hB5 (stepFnIter_chain hB6 (stepFnIter_chain hB8
      (stepFnIter_chain hB9 (stepFnIter_chain hB13
        (stepFnIter_chain hB15 (stepFnIter_chain hB17
          (stepFnIter_chain hB19 (stepFnIter_chain hB20
            (stepFnIter_chain hB21 (stepFnIter_chain hB22
              hB23))))))))))))

/-- **The `GetData` body span** (29 steps, populated shape): single
nil check, the slice field read directly (no second deref), the
result stored (slice normalization is the identity). -/
theorem getData_body_span {na lw : Nat} {dtyEw : Option Ty}
    {fsE : Array (String × GoValue)} {sv : GoValue}
    {resDef : GoValue}
    (σ' : ExecState) (ch : Choices) (FK : Cont)
    (hx : Heap.lookup σ'.heap (.base ⟨na⟩) = some (xCell lw))
    (hres : Heap.lookup σ'.heap (.base ⟨na + 1⟩)
      = some ⟨some (.slice (.int .uint8)), resDef⟩)
    (hEw : Heap.lookup σ'.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hf : StructFields.lookup fsE "Data" = some sv) :
    stepFnIter 29 σ'
        (.exec getDataFunc.body (getterEnv na) FK) ch
      = .ok (.returning FK,
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) := by
  let env1g : LocalEnv := [] :: getterEnv na
  let zeroSeqn : Stmt := .seqn #[.assign (.var "$res0")
    (.nil (some (.slice (.int .uint8)))), .returnStmt]
  let KG : Cont := .seq [zeroSeqn] env1g FK
  let thnD : Stmt := .block #[] #[.seqn
    #[.assign (.var "$res0")
        (.fieldGet (.deref (.var "x") tyEntD) tidE "Data"),
      .returnStmt]]
  -- D1+D2: block/pop + if entry + neq dispatch (4 steps)
  have hD1 : stepFnIter 4 σ'
      (.exec getDataFunc.body (getterEnv na) FK) ch
      = .ok (.evalE (.var "x") env1g
          (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
            (.ifK thnD (.seqn #[]) env1g KG)), σ', ch) := by
    have d1 : stepFnIter 2 σ'
        (.exec getDataFunc.body (getterEnv na) FK) ch
        = .ok (.exec (.ifThenElse
            (.neqCmp (.pointer tyEntD) (.var "x") (.nil none))
            thnD (.seqn #[])) env1g KG, σ', ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_block)
        (stepFnIter_one stepFn_seq_pop)
    have d2 : stepFnIter 2 σ' (.exec (.ifThenElse
        (.neqCmp (.pointer tyEntD) (.var "x") (.nil none))
        thnD (.seqn #[])) env1g KG) ch
        = .ok (.evalE (.var "x") env1g
            (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none]
              env1g (.ifK thnD (.seqn #[]) env1g KG)), σ', ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain d1 d2
  -- D3-D6: x read, nil, neq, branch (5 steps)
  have hD3 : stepFnIter 1 σ' (.evalE (.var "x") env1g
      (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
        (.ifK thnD (.seqn #[]) env1g KG))) ch
      = .ok (.retV (.addr (.base ⟨lw⟩))
          (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
            (.ifK thnD (.seqn #[]) env1g KG)), σ', ch) :=
    stepFnIter_one (stepFn_var (henv := rfl) (hlook := hx))
  have hD4 : stepFnIter 4 σ' (.retV (.addr (.base ⟨lw⟩))
      (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
        (.ifK thnD (.seqn #[]) env1g KG))) ch
      = .ok (.exec thnD env1g KG, σ', ch) := by
    have d4 : stepFnIter 2 σ' (.retV (.addr (.base ⟨lw⟩))
        (.strictK (.neqCmp (.pointer tyEntD)) [] [.nil none] env1g
          (.ifK thnD (.seqn #[]) env1g KG))) ch
        = .ok (.retV (.nil)
            (.strictK (.neqCmp (.pointer tyEntD))
              [.addr (.base ⟨lw⟩)] [] env1g
              (.ifK thnD (.seqn #[]) env1g KG)), σ', ch) := by
      with_unfolding_all rfl
    have d5 : stepFnIter 1 σ' (.retV (.nil)
        (.strictK (.neqCmp (.pointer tyEntD)) [.addr (.base ⟨lw⟩)]
          [] env1g (.ifK thnD (.seqn #[]) env1g KG))) ch
        = .ok (.retV (.bool true)
            (.ifK thnD (.seqn #[]) env1g KG), σ', ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.nil,
          GoValue.addr (.base ⟨lw⟩)])
        = [GoValue.addr (.base ⟨lw⟩), GoValue.nil] from rfl]
      exact applyStrictOp_neq_addr_nil
    have d6 : stepFnIter 1 σ' (.retV (.bool true)
        (.ifK thnD (.seqn #[]) env1g KG)) ch
        = .ok (.exec thnD env1g KG, σ', ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain d4 (stepFnIter_chain d5 d6)
  -- D7: block/pop + splice/pop (4 steps)
  let env2g : LocalEnv := [] :: env1g
  have hD7 : stepFnIter 4 σ' (.exec thnD env1g KG) ch
      = .ok (.exec (.assign (.var "$res0")
          (.fieldGet (.deref (.var "x") tyEntD) tidE "Data")) env2g
          (.seq [.returnStmt] env2g KG), σ', ch) := by
    have d7 : stepFnIter 2 σ' (.exec thnD env1g KG) ch
        = .ok (.exec (.seqn
            #[.assign (.var "$res0")
                (.fieldGet (.deref (.var "x") tyEntD) tidE "Data"),
              .returnStmt]) env2g (.seq [] env2g KG), σ', ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_block)
        (stepFnIter_one stepFn_seq_pop)
    exact stepFnIter_chain d7 (stepFnIter_splice_pop
      (ss := #[.assign (.var "$res0")
          (.fieldGet (.deref (.var "x") tyEntD) tidE "Data"),
        .returnStmt]) rfl)
  -- D8-D10: entry, ref, field read (9 steps)
  let KD : Cont := .rhsK .vals
    [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] [] (.seqn #[]) env2g
    (.seq [.returnStmt] env2g KG)
  have hD8 : stepFnIter 2 σ' (.exec (.assign (.var "$res0")
      (.fieldGet (.deref (.var "x") tyEntD) tidE "Data")) env2g
      (.seq [.returnStmt] env2g KG)) ch
      = .ok (.retV (.addr (.base ⟨na + 1⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.fieldGet (.deref (.var "x") tyEntD) tidE "Data"] []
            (.seqn #[]) env2g (.seq [.returnStmt] env2g KG)),
        σ', ch) := by
    have d8 : stepFnIter 1 σ' (.exec (.assign (.var "$res0")
        (.fieldGet (.deref (.var "x") tyEntD) tidE "Data")) env2g
        (.seq [.returnStmt] env2g KG)) ch
        = .ok (.evalE (.ref "$res0") env2g
            (.tgtOpK (.chain []) [] [] [] [] .vals
              [.fieldGet (.deref (.var "x") tyEntD) tidE "Data"] []
              (.seqn #[]) env2g (.seq [.returnStmt] env2g KG)),
          σ', ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain d8 (stepFnIter_one (stepFn_ref rfl))
  have hD9 : stepFnIter 1 σ' (.retV (.addr (.base ⟨na + 1⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.fieldGet (.deref (.var "x") tyEntD) tidE "Data"] []
        (.seqn #[]) env2g (.seq [.returnStmt] env2g KG))) ch
      = .ok (.evalE (.fieldGet (.deref (.var "x") tyEntD) tidE
          "Data") env2g KD, σ', ch) := by
    with_unfolding_all rfl
  have hD10 : stepFnIter 5 σ'
      (.evalE (.fieldGet (.deref (.var "x") tyEntD) tidE "Data")
        env2g KD) ch
      = .ok (.retV sv KD, σ', ch) :=
    read_field_seg (henv := rfl) (hp := hx) (hw := hEw) (hf := hf)
  -- D11+D12: → the store (2 steps)
  have hD11 : stepFnIter 1 σ' (.retV sv KD) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 1⟩)) [] []]
          [sv] (.seqn #[]) env2g (.seq [.returnStmt] env2g KG)),
        σ', ch) := by
    with_unfolding_all rfl
  have hD12 : stepFnIter 1 σ' (.next (.storeK
      [.chain (.addr (.base ⟨na + 1⟩)) [] []] [sv] (.seqn #[]) env2g
      (.seq [.returnStmt] env2g KG))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env2g
          (.seq [.returnStmt] env2g KG)),
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .slice (.int .uint8)) (old := resDef)
        (hlook := hres) (hnorm := normalize_slice)))
  -- D13: drain + return (6 steps)
  have hD13 : stepFnIter 6
      { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }
      (.next (.storeK [] [] (.seqn #[]) env2g
        (.seq [.returnStmt] env2g KG))) ch
      = .ok (.returning FK,
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) := by
    have d13 : stepFnIter 3
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }
        (.next (.storeK [] [] (.seqn #[]) env2g
          (.seq [.returnStmt] env2g KG))) ch
        = .ok (.exec .returnStmt env2g (.seq [] env2g KG),
          { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
        (stepFnIter_splice_pop (ss := #[]) rfl)
    have d14 : stepFnIter 3
        { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }
        (.exec .returnStmt env2g (.seq [] env2g KG)) ch
        = .ok (.returning FK,
          { σ' with heap := Heap.set σ'.heap (.base ⟨na + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain d13 d14
  exact stepFnIter_chain hD1 (stepFnIter_chain hD3
    (stepFnIter_chain hD4 (stepFnIter_chain hD7 (stepFnIter_chain hD8
      (stepFnIter_chain hD9 (stepFnIter_chain hD10
        (stepFnIter_chain hD11 (stepFnIter_chain hD12 hD13))))))))

end Body

/-! ## 5. The four call spans -/

section Calls

variable {envC : LocalEnv} {tgt : String} {ltc : Nat} {Kc : Cont}
  {lw li : Nat} {dtyEw dtyI : Option Ty}
  {fsE : Array (String × GoValue)}

/-- **`GetIndex` call span** (49 steps): the target cell receives
exactly the entry's `Index` payload. -/
theorem getIndex_call_span
    (henvT : LocalEnv.lookup envC tgt = some (.base ⟨ltc⟩))
    {v : Nat} (hv : v < 2 ^ 64) {told : GoValue}
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hEw : Heap.lookup σ.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hf : StructFields.lookup fsE "Index"
      = some (.addr (.base ⟨li⟩)))
    (hIc : Heap.lookup σ.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int (v : Int) .uint64⟩)
    (htc : Heap.lookup σ.heap (.base ⟨ltc⟩)
      = some ⟨some (.int .uint64), told⟩)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (_hd1 : ltc ≠ lw) (_hd2 : ltc ≠ li) :
    stepFnIter 49 σ (.retV (.addr (.base ⟨lw⟩))
        (.callArgsK ⟨"raftpb.Entry.GetIndex"⟩
          [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        twinSt (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩) (xCell lw))
            (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
          (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
          (σ.nextAddr + 2), ch) := by
  have hlwna : lw < σ.nextAddr := by
    rcases Nat.lt_or_ge lw σ.nextAddr with h | h
    · exact h
    · rw [hfr lw h] at hEw; cases hEw
  have hlina : li < σ.nextAddr := by
    rcases Nat.lt_or_ge li σ.nextAddr with h | h
    · exact h
    · rw [hfr li h] at hIc; cases hIc
  have hltcna : ltc < σ.nextAddr := by
    rcases Nat.lt_or_ge ltc σ.nextAddr with h | h
    · exact h
    · rw [hfr ltc h] at htc; cases htc
  have hσ := twinSt_of_agrees hag
  have henter : enterFrame σ ⟨"raftpb.Entry.GetIndex"⟩
      [.addr (.base ⟨lw⟩)]
      = .ok (getIndexFunc, getterEnv σ.nextAddr,
        [.base ⟨σ.nextAddr + 1⟩],
        twinSt (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.int .uint64), .int 0 .uint64⟩)
          (σ.nextAddr + 2)) := by
    have h0 := getIndex_enterFrame σ.heap σ.nextAddr lw
    rw [← hσ] at h0
    exact h0
  let σ₁ : ExecState := twinSt (Heap.set (Heap.set σ.heap
    (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
    ⟨some (.int .uint64), .int 0 .uint64⟩) (σ.nextAddr + 2)
  have hV1 : stepFnIter 1 σ (.retV (.addr (.base ⟨lw⟩))
      (.callArgsK ⟨"raftpb.Entry.GetIndex"⟩
        [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec getIndexFunc.body (getterEnv σ.nextAddr)
          (.frame [(.chain [], [.ref tgt])] envC
            [.base ⟨σ.nextAddr + 1⟩] [] Kc getIndexFunc.wrapper),
        σ₁, ch) :=
    stepFnIter_one (stepFn_call_enter (vals := [])
      (v := .addr (.base ⟨lw⟩)) (h := henter))
  -- the entered-state cells
  have hxσ1 : Heap.lookup σ₁.heap (.base ⟨σ.nextAddr⟩)
      = some (xCell lw) := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  have hEwσ1 : Heap.lookup σ₁.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨lw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ lw),
      lookup_set_other (by omega : σ.nextAddr ≠ lw)]
    exact hEw
  have hIcσ1 : Heap.lookup σ₁.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int (v : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨li⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ li),
      lookup_set_other (by omega : σ.nextAddr ≠ li)]
    exact hIc
  have hbody := ptrGetter_body_span (f := "Index")
    (ty := .int .uint64) (zero := .intLit 0 .uint64)
    (rty := .int .uint64)
    (resDef := .int 0 .uint64) σ₁ ch
    (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
      [] Kc getIndexFunc.wrapper)
    hxσ1 lookup_set_self hEwσ1 hf hIcσ1
    (normalize_int_u64 hv)
  -- the exit (5 steps)
  let σ₂ : ExecState := { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }
  have hres2 : Heap.lookup σ₂.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some (.int .uint64), .int (v : Int) .uint64⟩ :=
    lookup_set_self
  have htc2 : Heap.lookup σ₂.heap (.base ⟨ltc⟩)
      = some ⟨some (.int .uint64), told⟩ := by
    show Heap.lookup (Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc)]
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc),
      lookup_set_other (by omega : σ.nextAddr ≠ ltc)]
    exact htc
  have hX : stepFnIter 5 σ₂ (.returning
      (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
        [] Kc getIndexFunc.wrapper)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }, ch) := by
    have x1 : stepFnIter 1 σ₂ (.returning
        (.frame [(.chain [], [.ref tgt])] envC
          [.base ⟨σ.nextAddr + 1⟩] [] Kc getIndexFunc.wrapper)) ch
        = .ok (.evalE (.ref tgt) envC
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.int (v : Int) .uint64] (.seqn #[]) envC Kc),
          σ₂, ch) :=
      stepFnIter_one (stepFn_return_frame
        (h := loadMany_one (c := ⟨some (.int .uint64),
          .int (v : Int) .uint64⟩) hres2))
    have x2 : stepFnIter 1 σ₂ (.evalE (.ref tgt) envC
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int (v : Int) .uint64] (.seqn #[]) envC Kc)) ch
        = .ok (.retV (.addr (.base ⟨ltc⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.int (v : Int) .uint64] (.seqn #[]) envC Kc),
          σ₂, ch) :=
      stepFnIter_one (stepFn_ref henvT)
    have x3 : stepFnIter 1 σ₂ (.retV (.addr (.base ⟨ltc⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int (v : Int) .uint64] (.seqn #[]) envC Kc)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨ltc⟩)) [] []]
            [.int (v : Int) .uint64] (.seqn #[]) envC Kc),
          σ₂, ch) := by
      with_unfolding_all rfl
    have x4 : stepFnIter 1 σ₂ (.next (.storeK
        [.chain (.addr (.base ⟨ltc⟩)) [] []]
        [.int (v : Int) .uint64] (.seqn #[]) envC Kc)) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) envC Kc),
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }, ch) :=
      stepFnIter_one (stepFn_store_step
        (storeTarget_addr (ty := .int .uint64) (old := told)
          (hlook := htc2) (hnorm := normalize_int_u64 hv)))
    have x5 : stepFnIter 1
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }
        (.next (.storeK [] [] (.seqn #[]) envC Kc)) ch
        = .ok (.exec (.seqn #[]) envC Kc,
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }, ch) :=
      stepFnIter_one stepFn_storeK_nil
    exact stepFnIter_chain x1 (stepFnIter_chain x2
      (stepFnIter_chain x3 (stepFnIter_chain x4 x5)))
  -- collapse the double res-cell set and assemble
  have hfin : ({ σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ } : ExecState)
      = twinSt (Heap.set (Heap.set (Heap.set σ.heap
          (.base ⟨σ.nextAddr⟩) (xCell lw))
          (.base ⟨σ.nextAddr + 1⟩)
          ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
        (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
        (σ.nextAddr + 2) := by
    show twinSt (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
        ⟨some (.int .uint64), .int 0 .uint64⟩)
        (.base ⟨σ.nextAddr + 1⟩)
        ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
      (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
      (σ.nextAddr + 2) = _
    rw [set_set]
  rw [← hfin]
  exact stepFnIter_chain hV1 (stepFnIter_chain hbody hX)


/-- **`GetTerm` call span** (49 steps): the target cell receives
exactly the entry's `Index` payload. -/
theorem getTerm_call_span
    (henvT : LocalEnv.lookup envC tgt = some (.base ⟨ltc⟩))
    {v : Nat} (hv : v < 2 ^ 64) {told : GoValue}
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hEw : Heap.lookup σ.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hf : StructFields.lookup fsE "Term"
      = some (.addr (.base ⟨li⟩)))
    (hIc : Heap.lookup σ.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int (v : Int) .uint64⟩)
    (htc : Heap.lookup σ.heap (.base ⟨ltc⟩)
      = some ⟨some (.int .uint64), told⟩)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (_hd1 : ltc ≠ lw) (_hd2 : ltc ≠ li) :
    stepFnIter 49 σ (.retV (.addr (.base ⟨lw⟩))
        (.callArgsK ⟨"raftpb.Entry.GetTerm"⟩
          [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        twinSt (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩) (xCell lw))
            (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
          (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
          (σ.nextAddr + 2), ch) := by
  have hlwna : lw < σ.nextAddr := by
    rcases Nat.lt_or_ge lw σ.nextAddr with h | h
    · exact h
    · rw [hfr lw h] at hEw; cases hEw
  have hlina : li < σ.nextAddr := by
    rcases Nat.lt_or_ge li σ.nextAddr with h | h
    · exact h
    · rw [hfr li h] at hIc; cases hIc
  have hltcna : ltc < σ.nextAddr := by
    rcases Nat.lt_or_ge ltc σ.nextAddr with h | h
    · exact h
    · rw [hfr ltc h] at htc; cases htc
  have hσ := twinSt_of_agrees hag
  have henter : enterFrame σ ⟨"raftpb.Entry.GetTerm"⟩
      [.addr (.base ⟨lw⟩)]
      = .ok (getTermFunc, getterEnv σ.nextAddr,
        [.base ⟨σ.nextAddr + 1⟩],
        twinSt (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.int .uint64), .int 0 .uint64⟩)
          (σ.nextAddr + 2)) := by
    have h0 := getTerm_enterFrame σ.heap σ.nextAddr lw
    rw [← hσ] at h0
    exact h0
  let σ₁ : ExecState := twinSt (Heap.set (Heap.set σ.heap
    (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
    ⟨some (.int .uint64), .int 0 .uint64⟩) (σ.nextAddr + 2)
  have hV1 : stepFnIter 1 σ (.retV (.addr (.base ⟨lw⟩))
      (.callArgsK ⟨"raftpb.Entry.GetTerm"⟩
        [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec getTermFunc.body (getterEnv σ.nextAddr)
          (.frame [(.chain [], [.ref tgt])] envC
            [.base ⟨σ.nextAddr + 1⟩] [] Kc getTermFunc.wrapper),
        σ₁, ch) :=
    stepFnIter_one (stepFn_call_enter (vals := [])
      (v := .addr (.base ⟨lw⟩)) (h := henter))
  -- the entered-state cells
  have hxσ1 : Heap.lookup σ₁.heap (.base ⟨σ.nextAddr⟩)
      = some (xCell lw) := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  have hEwσ1 : Heap.lookup σ₁.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨lw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ lw),
      lookup_set_other (by omega : σ.nextAddr ≠ lw)]
    exact hEw
  have hIcσ1 : Heap.lookup σ₁.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int (v : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨li⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ li),
      lookup_set_other (by omega : σ.nextAddr ≠ li)]
    exact hIc
  have hbody := ptrGetter_body_span (f := "Term")
    (ty := .int .uint64) (zero := .intLit 0 .uint64)
    (rty := .int .uint64)
    (resDef := .int 0 .uint64) σ₁ ch
    (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
      [] Kc getTermFunc.wrapper)
    hxσ1 lookup_set_self hEwσ1 hf hIcσ1
    (normalize_int_u64 hv)
  -- the exit (5 steps)
  let σ₂ : ExecState := { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }
  have hres2 : Heap.lookup σ₂.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some (.int .uint64), .int (v : Int) .uint64⟩ :=
    lookup_set_self
  have htc2 : Heap.lookup σ₂.heap (.base ⟨ltc⟩)
      = some ⟨some (.int .uint64), told⟩ := by
    show Heap.lookup (Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc)]
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc),
      lookup_set_other (by omega : σ.nextAddr ≠ ltc)]
    exact htc
  have hX : stepFnIter 5 σ₂ (.returning
      (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
        [] Kc getTermFunc.wrapper)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }, ch) := by
    have x1 : stepFnIter 1 σ₂ (.returning
        (.frame [(.chain [], [.ref tgt])] envC
          [.base ⟨σ.nextAddr + 1⟩] [] Kc getTermFunc.wrapper)) ch
        = .ok (.evalE (.ref tgt) envC
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.int (v : Int) .uint64] (.seqn #[]) envC Kc),
          σ₂, ch) :=
      stepFnIter_one (stepFn_return_frame
        (h := loadMany_one (c := ⟨some (.int .uint64),
          .int (v : Int) .uint64⟩) hres2))
    have x2 : stepFnIter 1 σ₂ (.evalE (.ref tgt) envC
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int (v : Int) .uint64] (.seqn #[]) envC Kc)) ch
        = .ok (.retV (.addr (.base ⟨ltc⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.int (v : Int) .uint64] (.seqn #[]) envC Kc),
          σ₂, ch) :=
      stepFnIter_one (stepFn_ref henvT)
    have x3 : stepFnIter 1 σ₂ (.retV (.addr (.base ⟨ltc⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int (v : Int) .uint64] (.seqn #[]) envC Kc)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨ltc⟩)) [] []]
            [.int (v : Int) .uint64] (.seqn #[]) envC Kc),
          σ₂, ch) := by
      with_unfolding_all rfl
    have x4 : stepFnIter 1 σ₂ (.next (.storeK
        [.chain (.addr (.base ⟨ltc⟩)) [] []]
        [.int (v : Int) .uint64] (.seqn #[]) envC Kc)) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) envC Kc),
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }, ch) :=
      stepFnIter_one (stepFn_store_step
        (storeTarget_addr (ty := .int .uint64) (old := told)
          (hlook := htc2) (hnorm := normalize_int_u64 hv)))
    have x5 : stepFnIter 1
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }
        (.next (.storeK [] [] (.seqn #[]) envC Kc)) ch
        = .ok (.exec (.seqn #[]) envC Kc,
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ }, ch) :=
      stepFnIter_one stepFn_storeK_nil
    exact stepFnIter_chain x1 (stepFnIter_chain x2
      (stepFnIter_chain x3 (stepFnIter_chain x4 x5)))
  -- collapse the double res-cell set and assemble
  have hfin : ({ σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩ } : ExecState)
      = twinSt (Heap.set (Heap.set (Heap.set σ.heap
          (.base ⟨σ.nextAddr⟩) (xCell lw))
          (.base ⟨σ.nextAddr + 1⟩)
          ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
        (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
        (σ.nextAddr + 2) := by
    show twinSt (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
        ⟨some (.int .uint64), .int 0 .uint64⟩)
        (.base ⟨σ.nextAddr + 1⟩)
        ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
      (.base ⟨ltc⟩) ⟨some (.int .uint64), .int (v : Int) .uint64⟩)
      (σ.nextAddr + 2) = _
    rw [set_set]
  rw [← hfin]
  exact stepFnIter_chain hV1 (stepFnIter_chain hbody hX)


/-- **`GetType` call span** (49 steps): the target cell receives
exactly the entry's `Index` payload. -/
theorem getType_call_span
    (henvT : LocalEnv.lookup envC tgt = some (.base ⟨ltc⟩))
    {v : Int} (hv0 : -(2 ^ 31) ≤ v) (hv1 : v < 2 ^ 31) {told : GoValue}
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hEw : Heap.lookup σ.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hf : StructFields.lookup fsE "Type"
      = some (.addr (.base ⟨li⟩)))
    (hIc : Heap.lookup σ.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int v .int32⟩)
    (htc : Heap.lookup σ.heap (.base ⟨ltc⟩)
      = some ⟨some (.defined ⟨"raftpb.EntryType"⟩), told⟩)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (_hd1 : ltc ≠ lw) (_hd2 : ltc ≠ li) :
    stepFnIter 49 σ (.retV (.addr (.base ⟨lw⟩))
        (.callArgsK ⟨"raftpb.Entry.GetType"⟩
          [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        twinSt (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩) (xCell lw))
            (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩)
          (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩)
          (σ.nextAddr + 2), ch) := by
  have hlwna : lw < σ.nextAddr := by
    rcases Nat.lt_or_ge lw σ.nextAddr with h | h
    · exact h
    · rw [hfr lw h] at hEw; cases hEw
  have hlina : li < σ.nextAddr := by
    rcases Nat.lt_or_ge li σ.nextAddr with h | h
    · exact h
    · rw [hfr li h] at hIc; cases hIc
  have hltcna : ltc < σ.nextAddr := by
    rcases Nat.lt_or_ge ltc σ.nextAddr with h | h
    · exact h
    · rw [hfr ltc h] at htc; cases htc
  have hσ := twinSt_of_agrees hag
  have henter : enterFrame σ ⟨"raftpb.Entry.GetType"⟩
      [.addr (.base ⟨lw⟩)]
      = .ok (getTypeFunc, getterEnv σ.nextAddr,
        [.base ⟨σ.nextAddr + 1⟩],
        twinSt (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
          (σ.nextAddr + 2)) := by
    have h0 := getType_enterFrame σ.heap σ.nextAddr lw
    rw [← hσ] at h0
    exact h0
  let σ₁ : ExecState := twinSt (Heap.set (Heap.set σ.heap
    (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
    ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩) (σ.nextAddr + 2)
  have hV1 : stepFnIter 1 σ (.retV (.addr (.base ⟨lw⟩))
      (.callArgsK ⟨"raftpb.Entry.GetType"⟩
        [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec getTypeFunc.body (getterEnv σ.nextAddr)
          (.frame [(.chain [], [.ref tgt])] envC
            [.base ⟨σ.nextAddr + 1⟩] [] Kc getTypeFunc.wrapper),
        σ₁, ch) :=
    stepFnIter_one (stepFn_call_enter (vals := [])
      (v := .addr (.base ⟨lw⟩)) (h := henter))
  -- the entered-state cells
  have hxσ1 : Heap.lookup σ₁.heap (.base ⟨σ.nextAddr⟩)
      = some (xCell lw) := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  have hEwσ1 : Heap.lookup σ₁.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨lw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ lw),
      lookup_set_other (by omega : σ.nextAddr ≠ lw)]
    exact hEw
  have hIcσ1 : Heap.lookup σ₁.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int v .int32⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨li⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ li),
      lookup_set_other (by omega : σ.nextAddr ≠ li)]
    exact hIc
  have hbody := ptrGetter_body_span (f := "Type")
    (ty := .defined ⟨"raftpb.EntryType"⟩)
    (zero := .intLit 0 .int32)
    (rty := .defined ⟨"raftpb.EntryType"⟩)
    (resDef := .int 0 .int32) σ₁ ch
    (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
      [] Kc getTypeFunc.wrapper)
    hxσ1 lookup_set_self hEwσ1 hf hIcσ1
    (normalize_entryType (σ := σ₁) rfl hv0 hv1)
  -- the exit (5 steps)
  let σ₂ : ExecState := { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩ }
  have hres2 : Heap.lookup σ₂.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩ :=
    lookup_set_self
  have htc2 : Heap.lookup σ₂.heap (.base ⟨ltc⟩)
      = some ⟨some (.defined ⟨"raftpb.EntryType"⟩), told⟩ := by
    show Heap.lookup (Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc)]
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc),
      lookup_set_other (by omega : σ.nextAddr ≠ ltc)]
    exact htc
  have hX : stepFnIter 5 σ₂ (.returning
      (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
        [] Kc getTypeFunc.wrapper)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩ }, ch) := by
    have x1 : stepFnIter 1 σ₂ (.returning
        (.frame [(.chain [], [.ref tgt])] envC
          [.base ⟨σ.nextAddr + 1⟩] [] Kc getTypeFunc.wrapper)) ch
        = .ok (.evalE (.ref tgt) envC
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.int v .int32] (.seqn #[]) envC Kc),
          σ₂, ch) :=
      stepFnIter_one (stepFn_return_frame
        (h := loadMany_one (c := ⟨some (.defined ⟨"raftpb.EntryType"⟩),
          .int v .int32⟩) hres2))
    have x2 : stepFnIter 1 σ₂ (.evalE (.ref tgt) envC
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int v .int32] (.seqn #[]) envC Kc)) ch
        = .ok (.retV (.addr (.base ⟨ltc⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals []
              [.int v .int32] (.seqn #[]) envC Kc),
          σ₂, ch) :=
      stepFnIter_one (stepFn_ref henvT)
    have x3 : stepFnIter 1 σ₂ (.retV (.addr (.base ⟨ltc⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals []
          [.int v .int32] (.seqn #[]) envC Kc)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨ltc⟩)) [] []]
            [.int v .int32] (.seqn #[]) envC Kc),
          σ₂, ch) := by
      with_unfolding_all rfl
    have x4 : stepFnIter 1 σ₂ (.next (.storeK
        [.chain (.addr (.base ⟨ltc⟩)) [] []]
        [.int v .int32] (.seqn #[]) envC Kc)) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) envC Kc),
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩ }, ch) :=
      stepFnIter_one (stepFn_store_step
        (storeTarget_addr (ty := .defined ⟨"raftpb.EntryType"⟩) (old := told)
          (hlook := htc2)
          (hnorm := normalize_entryType (σ := σ₂) rfl hv0 hv1)))
    have x5 : stepFnIter 1
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩ }
        (.next (.storeK [] [] (.seqn #[]) envC Kc)) ch
        = .ok (.exec (.seqn #[]) envC Kc,
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩ }, ch) :=
      stepFnIter_one stepFn_storeK_nil
    exact stepFnIter_chain x1 (stepFnIter_chain x2
      (stepFnIter_chain x3 (stepFnIter_chain x4 x5)))
  -- collapse the double res-cell set and assemble
  have hfin : ({ σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩ } : ExecState)
      = twinSt (Heap.set (Heap.set (Heap.set σ.heap
          (.base ⟨σ.nextAddr⟩) (xCell lw))
          (.base ⟨σ.nextAddr + 1⟩)
          ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩)
        (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩)
        (σ.nextAddr + 2) := by
    show twinSt (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
        ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
        (.base ⟨σ.nextAddr + 1⟩)
        ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩)
      (.base ⟨ltc⟩) ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int v .int32⟩)
      (σ.nextAddr + 2) = _
    rw [set_set]
  rw [← hfin]
  exact stepFnIter_chain hV1 (stepFnIter_chain hbody hX)



/-- **`GetData` call span** (35 steps): the target cell receives
exactly the entry's `Data` slice value. -/
theorem getData_call_span
    (henvT : LocalEnv.lookup envC tgt = some (.base ⟨ltc⟩))
    {sv : GoValue} {told : GoValue}
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hEw : Heap.lookup σ.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hf : StructFields.lookup fsE "Data" = some sv)
    (htc : Heap.lookup σ.heap (.base ⟨ltc⟩)
      = some ⟨some (.slice (.int .uint8)), told⟩)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (_hd1 : ltc ≠ lw) :
    stepFnIter 35 σ (.retV (.addr (.base ⟨lw⟩))
        (.callArgsK ⟨"raftpb.Entry.GetData"⟩
          [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        twinSt (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩) (xCell lw))
            (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.slice (.int .uint8)), sv⟩)
          (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩)
          (σ.nextAddr + 2), ch) := by
  have hlwna : lw < σ.nextAddr := by
    rcases Nat.lt_or_ge lw σ.nextAddr with h | h
    · exact h
    · rw [hfr lw h] at hEw; cases hEw
  have hltcna : ltc < σ.nextAddr := by
    rcases Nat.lt_or_ge ltc σ.nextAddr with h | h
    · exact h
    · rw [hfr ltc h] at htc; cases htc
  have hσ := twinSt_of_agrees hag
  have henter : enterFrame σ ⟨"raftpb.Entry.GetData"⟩
      [.addr (.base ⟨lw⟩)]
      = .ok (getDataFunc, getterEnv σ.nextAddr,
        [.base ⟨σ.nextAddr + 1⟩],
        twinSt (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
            ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩)
          (σ.nextAddr + 2)) := by
    have h0 := getData_enterFrame σ.heap σ.nextAddr lw
    rw [← hσ] at h0
    exact h0
  let σ₁ : ExecState := twinSt (Heap.set (Heap.set σ.heap
    (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
    ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩)
    (σ.nextAddr + 2)
  have hV1 : stepFnIter 1 σ (.retV (.addr (.base ⟨lw⟩))
      (.callArgsK ⟨"raftpb.Entry.GetData"⟩
        [(.chain [], [.ref tgt])] [] [] envC Kc)) ch
      = .ok (.exec getDataFunc.body (getterEnv σ.nextAddr)
          (.frame [(.chain [], [.ref tgt])] envC
            [.base ⟨σ.nextAddr + 1⟩] [] Kc getDataFunc.wrapper),
        σ₁, ch) :=
    stepFnIter_one (stepFn_call_enter (vals := [])
      (v := .addr (.base ⟨lw⟩)) (h := henter))
  have hxσ1 : Heap.lookup σ₁.heap (.base ⟨σ.nextAddr⟩)
      = some (xCell lw) := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  have hEwσ1 : Heap.lookup σ₁.heap (.base ⟨lw⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨lw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ lw),
      lookup_set_other (by omega : σ.nextAddr ≠ lw)]
    exact hEw
  have hbody := getData_body_span (resDef := .slice ⟨none, 0, 0, 0⟩)
    σ₁ ch
    (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
      [] Kc getDataFunc.wrapper)
    hxσ1 lookup_set_self hEwσ1 hf
  let σ₂ : ExecState := { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩ }
  have hres2 : Heap.lookup σ₂.heap (.base ⟨σ.nextAddr + 1⟩)
      = some ⟨some (.slice (.int .uint8)), sv⟩ := lookup_set_self
  have htc2 : Heap.lookup σ₂.heap (.base ⟨ltc⟩)
      = some ⟨some (.slice (.int .uint8)), told⟩ := by
    show Heap.lookup (Heap.set σ₁.heap (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc)]
    show Heap.lookup (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
      _) (.base ⟨σ.nextAddr + 1⟩) _) (.base ⟨ltc⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ ltc),
      lookup_set_other (by omega : σ.nextAddr ≠ ltc)]
    exact htc
  have hX : stepFnIter 5 σ₂ (.returning
      (.frame [(.chain [], [.ref tgt])] envC [.base ⟨σ.nextAddr + 1⟩]
        [] Kc getDataFunc.wrapper)) ch
      = .ok (.exec (.seqn #[]) envC Kc,
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) := by
    have x1 : stepFnIter 1 σ₂ (.returning
        (.frame [(.chain [], [.ref tgt])] envC
          [.base ⟨σ.nextAddr + 1⟩] [] Kc getDataFunc.wrapper)) ch
        = .ok (.evalE (.ref tgt) envC
            (.tgtOpK (.chain []) [] [] [] [] .vals [] [sv]
              (.seqn #[]) envC Kc), σ₂, ch) :=
      stepFnIter_one (stepFn_return_frame
        (h := loadMany_one
          (c := ⟨some (.slice (.int .uint8)), sv⟩) hres2))
    have x2 : stepFnIter 1 σ₂ (.evalE (.ref tgt) envC
        (.tgtOpK (.chain []) [] [] [] [] .vals [] [sv]
          (.seqn #[]) envC Kc)) ch
        = .ok (.retV (.addr (.base ⟨ltc⟩))
            (.tgtOpK (.chain []) [] [] [] [] .vals [] [sv]
              (.seqn #[]) envC Kc), σ₂, ch) :=
      stepFnIter_one (stepFn_ref henvT)
    have x3 : stepFnIter 1 σ₂ (.retV (.addr (.base ⟨ltc⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [] [sv]
          (.seqn #[]) envC Kc)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨ltc⟩)) [] []]
            [sv] (.seqn #[]) envC Kc), σ₂, ch) := by
      with_unfolding_all rfl
    have x4 : stepFnIter 1 σ₂ (.next (.storeK
        [.chain (.addr (.base ⟨ltc⟩)) [] []] [sv] (.seqn #[])
        envC Kc)) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) envC Kc),
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) :=
      stepFnIter_one (stepFn_store_step
        (storeTarget_addr (ty := .slice (.int .uint8)) (old := told)
          (hlook := htc2) (hnorm := normalize_slice)))
    have x5 : stepFnIter 1
        { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩ }
        (.next (.storeK [] [] (.seqn #[]) envC Kc)) ch
        = .ok (.exec (.seqn #[]) envC Kc,
          { σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩ }, ch) :=
      stepFnIter_one stepFn_storeK_nil
    exact stepFnIter_chain x1 (stepFnIter_chain x2
      (stepFnIter_chain x3 (stepFnIter_chain x4 x5)))
  have hfin : ({ σ₂ with heap := Heap.set σ₂.heap (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩ } : ExecState)
      = twinSt (Heap.set (Heap.set (Heap.set σ.heap
          (.base ⟨σ.nextAddr⟩) (xCell lw))
          (.base ⟨σ.nextAddr + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩)
        (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩)
        (σ.nextAddr + 2) := by
    show twinSt (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (xCell lw)) (.base ⟨σ.nextAddr + 1⟩)
        ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩)
        (.base ⟨σ.nextAddr + 1⟩) ⟨some (.slice (.int .uint8)), sv⟩)
      (.base ⟨ltc⟩) ⟨some (.slice (.int .uint8)), sv⟩)
      (σ.nextAddr + 2) = _
    rw [set_set]
  rw [← hfin]
  exact stepFnIter_chain hV1 (stepFnIter_chain hbody hX)

end Calls

end GoLean.RaftSeam.SpanApplyGetters
