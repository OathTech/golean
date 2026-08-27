import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.SliceMem

/-!
# The slice-walk loop schema (A4-U20 = C2b, the driver-loop
symbolic-net kit)

The native frontend desugars `for i := range s { body }` (index-only
range over a slice) into ONE fixed shape (verified against the pinned
twin lowering, `artifacts/probe/c2bdump.out` (untracked scratch) — both the driver's
live-map rebuild and `main.twin.liveCount` carry it verbatim, with
the SAME `$rcoll/$rlen/$ridx/$rfirst` temp names and only the user
index variable and guarded body differing):

```
block [] [
  init $rcoll; $rcoll := <collection expr>;
  init $rlen;  $rlen  := len($rcoll);
  init $ridx;  $ridx  := 0;
  init $rfirst; $rfirst := true;
  while true {
    if $rfirst { $rfirst = false } else { $ridx = $ridx + 1 };
    if $ridx >= $rlen { break };
    init uVar; uVar := $ridx;
    body
  }]
```

This module carries the WHILE part — the |collection|-dependent span:
the per-iteration head glue (flag/increment + bound check + index
bind), the exit path, and the composed LOOP schema
(`sliceWalk_loop`), stated in the compositional mode (I2, the
flexibility redesign §3): symbolic preconditions (cell lookups as
hypotheses, per StepKit rules 1–5), a state-family invariant, and a
BOUNDED-COMPLETION conclusion (`∃ m ≤ …`) — never a literal chain
per collection shape. The prologue above the `while` is fixed-cost
(no |collection| dependence) and deliberately NOT schematized here
(middle-path §7: no demonstrated demand — fixed spans ride the
mirror); the map-range PICK loop is already covered by
`MapLoops.mapPickLoop_generic`.

Consumers (the demonstrated ≥2 of §7's two-axis test): the driver's
live-map rebuild and `liveCount` (`Specs/Raft/DriverNet.lean` — the
span-lemma instances; their concrete witness module was W0-killed,
archived, witness owed on first consumption per the K-4 record);
`pickFor`/`projection`/`complete` are latent further consumers of
the same shape.

LINEAGE (clever-tricks doctrine): the Floyd/Hoare loop invariant —
the schema is a per-iteration-fact induction in the exact style of
`FuelMeasure.stepFnIter_iterate_bail_rel` and
`MapLoops.mapCountLoop_generic`, specialized to the frontend's
range-desugar shape so instances prove ONLY their body.

## The measured anatomy (census `artifacts/probe/c2bloopcensus2.out` (untracked scratch),
compiled-walk verified at collection lengths 0–3, mixed guard flags)

From the loop-head config (`.exec (.while true …)`), per iteration:
- head glue, first iteration (flag true): 17 steps to the bound
  check, writing `$rfirst := false`;
- head glue, subsequent (flag false): 21 steps, writing
  `$ridx := old + 1`;
- bound check, continue case: 9 steps to the index `initialization`;
- bound check, exit case: 10 steps to `.next k` (break unwind);
- index bind: 11 steps to the body config, allocating the index cell
  (ONE fresh cell per iteration — the frontend's per-iteration
  variable; the machine does not prune it, so the family threads a
  growing dead region, the MapLoops `DeadFrom` pattern);
- body → head back edge: 2 steps.
-/

namespace GoLean.SliceWalk

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! ## 1. The desugared shape (statement vocabulary) -/

abbrev tI : Ty := .int .int

/-- The flag statement: first iteration clears `$rfirst`, later ones
increment `$ridx`. -/
def flagIf (rF rI : String) : Stmt :=
  .ifThenElse (.var rF) (.assign (.var rF) (.boolLit false))
    (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))

/-- The bound check: `$ridx >= $rlen → break`. -/
def boundIf (rI rL : String) : Stmt :=
  .ifThenElse (.atLeastCmp (.var rI) (.var rL)) .breakStmt (.seqn #[])

def initU (uV : String) : Stmt := .initialization { id := uV, typ := tI }

def bindU (uV rI : String) : Stmt := .assign (.var uV) (.var rI)

/-- The while body (the frontend's fixed shape). -/
def rbody (rF rI rL uV : String) (body : Stmt) : Stmt :=
  .block #[] #[flagIf rF rI, boundIf rI rL, initU uV, bindU uV rI, body]

/-- The whole loop statement. -/
def rwhile (rF rI rL uV : String) (body : Stmt) : Stmt :=
  .while (.boolLit true) (rbody rF rI rL uV body)

/-! ## 2. The configuration vocabulary -/

/-- The loop continuation (the back edge's carrier; its `env` is the
while statement's own, so the loop-head configuration is IDENTICAL
every iteration — census-verified). -/
def wloopK (rF rI rL uV : String) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Cont :=
  .loop (.boolLit true) (rbody rF rI rL uV body) envW k

/-- The loop-head configuration (the schema's anchor). -/
def headCfg (rF rI rL uV : String) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Config :=
  .exec (rwhile rF rI rL uV body) envW k

/-- The while body's block scope. -/
def envB (envW : LocalEnv) : LocalEnv := [] :: envW

/-- The body-statement scope: block scope + the index variable at its
per-iteration cell. -/
def envU (envW : LocalEnv) (uV : String) (na : Nat) : LocalEnv :=
  [(uV, Loc.base ⟨na⟩)] :: envW

/-- The bound-check configuration (glue segments meet here). -/
def boundCfg (rF rI rL uV : String) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Config :=
  .exec (boundIf rI rL) (envB envW)
    (.seq [initU uV, bindU uV rI, body] (envB envW)
      (wloopK rF rI rL uV body envW k))

/-- The index-bind entry configuration. -/
def bindCfg (rF rI rL uV : String) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Config :=
  .exec (initU uV) (envB envW)
    (.seq [bindU uV rI, body] (envB envW)
      (wloopK rF rI rL uV body envW k))

/-- The body configuration at index-cell address `na` (what an
instance's body fact runs from). -/
def bodyCfg (rF rI rL uV : String) (body : Stmt) (envW : LocalEnv)
    (k : Cont) (na : Nat) : Config :=
  .exec body (envU envW uV na)
    (.seq [] (envU envW uV na) (wloopK rF rI rL uV body envW k))

/-- The body's exit configuration (a body completing normally hands
back exactly this; 2 further steps reach the head). -/
def bodyDoneCfg (rF rI rL uV : String) (body : Stmt) (envW : LocalEnv)
    (k : Cont) (na : Nat) : Config :=
  .next (.seq [] (envU envW uV na) (wloopK rF rI rL uV body envW k))

/-! ## 3. Environment helpers -/

theorem lookup_pushScope (env : LocalEnv) (x : String) :
    LocalEnv.lookup ([] :: env) x = LocalEnv.lookup env x := rfl

/-- Lookup through the index-variable scope, same name. -/
theorem lookup_envU_self {envW : LocalEnv} {uV : String} {na : Nat} :
    LocalEnv.lookup (envU envW uV na) uV = some (.base ⟨na⟩) := by
  simp [envU, LocalEnv.lookup, Scope.lookup]

/-- Lookup through the index-variable scope, other name. -/
theorem lookup_envU_ne {envW : LocalEnv} {uV x : String} {na : Nat}
    (h : uV ≠ x) :
    LocalEnv.lookup (envU envW uV na) x = LocalEnv.lookup envW x := by
  simp [envU, LocalEnv.lookup, Scope.lookup, h]

/-! ## 4. Small machine facts the glue consumes -/

/-- `defaultValue` at signed int is 0 (state-free). -/
theorem defaultValue_tI {σ : ExecState} :
    defaultValue σ tI = .ok (.int 0 .int) := by
  with_unfolding_all rfl

/-- The `ref` step (address-of a local), conditioned on the binding —
`stepFn_var`'s target-position sibling. -/
theorem stepFn_ref {σ : ExecState} {x : String} {env : LocalEnv}
    {l : Loc} {k : Cont} {ch : Choices}
    (henv : LocalEnv.lookup env x = some l) :
    stepFn σ (.evalE (.ref x) env k) ch = .ok (.retV (.addr l) k, σ, ch) := by
  simp only [stepFn, henv, pure, Except.pure]

/-- Bool normalization is the identity. -/
theorem normalize_bool {σ : ExecState} {b : Bool} :
    normalizeValueForTy σ .bool (.bool b) = .ok (.bool b) := by
  simp only [normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, pure, Except.pure]

/-- Signed-64 normalization is the identity in range. -/
theorem normalize_int_signed {σ : ExecState} {v : Int}
    (h0 : -(2 ^ 63) ≤ v) (h1 : v < 2 ^ 63) :
    normalizeValueForTy σ tI (.int v .int) = .ok (.int v .int) := by
  simp only [normalizeValueForTy, normalizeValueForTyFuel,
    typeResolutionFuel, GoLean.SliceMem.inorm_of_range h0 h1, pure,
    Except.pure]

/-! ## 5. The head-glue segments (composed; each conclusion pins the
full configuration and state, StepKit rules 1–3) -/

/-- The flag-cell store target. -/
abbrev flagCell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
/-- The index-cell payload. -/
abbrev idxCell (v : Int) : HeapCell := ⟨some tI, .int v .int⟩

/-- The state after the index bind at iteration value `a` (the fresh
index cell at the entry `nextAddr`, first defaulted then stored). -/
def bindState (σ : ExecState) (a : Int) : ExecState :=
  { σ with
      heap := Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) (idxCell 0))
        (.base ⟨σ.nextAddr⟩) (idxCell a),
      nextAddr := σ.nextAddr + 1 }

section Glue

variable {rF rI rL uV : String} {body : Stmt} {envW : LocalEnv} {k : Cont}
  {σ : ExecState} {ch : Choices} {lf li ll : Nat}

/-- Pure prefix: loop head → the flag read (6 steps, state untouched). -/
private theorem segA :
    stepFnIter 6 σ (headCfg rF rI rL uV body envW k) ch
      = .ok (.evalE (.var rF) (envB envW)
          (.ifK (.assign (.var rF) (.boolLit false))
            (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
            (envB envW)
            (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
              (wloopK rF rI rL uV body envW k))),
        σ, ch) := by
  with_unfolding_all rfl

/-- **Head glue, FIRST iteration** (flag true): 17 steps to the bound
check, `$rfirst := false` written. -/
theorem glue_first
    (henvF : LocalEnv.lookup envW rF = some (.base ⟨lf⟩))
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell true)) :
    stepFnIter 17 σ (headCfg rF rI rL uV body envW k) ch
      = .ok (boundCfg rF rI rL uV body envW k,
        { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) },
        ch) := by
  have hA := segA (rF := rF) (rI := rI) (rL := rL) (uV := uV)
    (body := body) (envW := envW) (k := k) (σ := σ) (ch := ch)
  have h7 : stepFnIter 1 σ (.evalE (.var rF) (envB envW)
      (.ifK (.assign (.var rF) (.boolLit false))
        (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
        (envB envW)
        (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.retV (.bool true)
          (.ifK (.assign (.var rF) (.boolLit false))
            (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
            (envB envW)
            (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
              (wloopK rF rI rL uV body envW k))),
        σ, ch) := by
    refine stepFnIter_one ?_
    have := stepFn_var (σ := σ)
      (henv := (lookup_pushScope envW rF).trans henvF)
      (hlook := hflag) (k := (.ifK (.assign (.var rF) (.boolLit false))
        (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
        (envB envW)
        (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
          (wloopK rF rI rL uV body envW k)))) (ch := ch)
    exact this
  -- retV true → exec assign → evalE ref (2 pure steps)
  have hB : stepFnIter 2 σ (.retV (.bool true)
      (.ifK (.assign (.var rF) (.boolLit false))
        (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
        (envB envW)
        (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.evalE (.ref rF) (envB envW)
          (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
            (.seqn #[]) (envB envW)
            (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
              (wloopK rF rI rL uV body envW k))),
        σ, ch) := by
    with_unfolding_all rfl
  have h10 : stepFnIter 1 σ (.evalE (.ref rF) (envB envW)
      (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
        (.seqn #[]) (envB envW)
        (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.retV (.addr (.base ⟨lf⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
            (.seqn #[]) (envB envW)
            (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
              (wloopK rF rI rL uV body envW k))),
        σ, ch) :=
    stepFnIter_one (stepFn_ref ((lookup_pushScope envW rF).trans henvF))
  -- retV addr → evalE rhs → retV rhs → storeK entry (3 pure steps)
  have hC : stepFnIter 3 σ (.retV (.addr (.base ⟨lf⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
        (.seqn #[]) (envB envW)
        (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨lf⟩)) [] []]
          [.bool false] (.seqn #[]) (envB envW)
          (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
            (wloopK rF rI rL uV body envW k))),
        σ, ch) := by
    with_unfolding_all rfl
  have h14 : stepFnIter 1 σ (.next (.storeK
      [.chain (.addr (.base ⟨lf⟩)) [] []] [.bool false] (.seqn #[])
      (envB envW)
      (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
        (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envB envW)
          (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
            (wloopK rF rI rL uV body envW k))),
        { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) },
        ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .bool) (old := .bool true)
        (hlook := hflag) (hnorm := normalize_bool)))
  have hD : stepFnIter 3
      { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) }
      (.next (.storeK [] [] (.seqn #[]) (envB envW)
        (.seq [boundIf rI rL, initU uV, bindU uV rI, body] (envB envW)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (boundCfg rF rI rL uV body envW k,
        { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) },
        ch) := by
    refine stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_chain (stepFnIter_one stepFn_seqn_splice)
        (stepFnIter_one stepFn_seq_pop))
  exact stepFnIter_chain hA (stepFnIter_chain h7 (stepFnIter_chain hB
    (stepFnIter_chain h10 (stepFnIter_chain hC
      (stepFnIter_chain h14 hD)))))

/-- `+` on two signed-64 ints, in-range result. -/
theorem applyStrictOp_add_int {σ : ExecState} {a b : Int}
    (h0 : -(2 ^ 63) ≤ a + b) (h1 : a + b < 2 ^ 63) :
    applyStrictOp σ .add [.int a .int, .int b .int]
      = .ok (.int (a + b) .int, σ) := by
  have hc : IntKind.compatibleResult IntKind.int IntKind.int
      = some IntKind.int := rfl
  simp [applyStrictOp, intBinaryResult, valueAsIntValue, Bind.bind,
    Except.bind, hc, GoLean.SliceMem.inorm_of_range h0 h1]

/-- `>=` on two signed-64 ints. -/
theorem applyStrictOp_atLeast_int {σ : ExecState} {a b : Int} :
    applyStrictOp σ .atLeastCmp [.int a .int, .int b .int]
      = .ok (.bool (decide (b ≤ a)), σ) := by
  simp only [applyStrictOp, valueAtLeast, Bind.bind, Except.bind, pure,
    Except.pure, ge_iff_le]

/-- **Head glue, SUBSEQUENT iteration** (flag false, `$ridx` holds
`a`): 21 steps to the bound check, `$ridx := a + 1` written. -/
theorem glue_next
    (henvF : LocalEnv.lookup envW rF = some (.base ⟨lf⟩))
    (henvI : LocalEnv.lookup envW rI = some (.base ⟨li⟩))
    {a : Int} (h0 : 0 ≤ a) (h1 : a + 1 < 2 ^ 63)
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell false))
    (hidx : Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell a)) :
    stepFnIter 21 σ (headCfg rF rI rL uV body envW k) ch
      = .ok (boundCfg rF rI rL uV body envW k,
        { σ with heap := Heap.set σ.heap (.base ⟨li⟩) (idxCell (a + 1)) },
        ch) := by
  have hA := segA (rF := rF) (rI := rI) (rL := rL) (uV := uV)
    (body := body) (envW := envW) (k := k) (σ := σ) (ch := ch)
  -- the tail continuation, abbreviated
  let K1 : Cont := .seq [boundIf rI rL, initU uV, bindU uV rI, body]
    (envB envW) (wloopK rF rI rL uV body envW k)
  have h7 : stepFnIter 1 σ (.evalE (.var rF) (envB envW)
      (.ifK (.assign (.var rF) (.boolLit false))
        (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
        (envB envW) K1)) ch
      = .ok (.retV (.bool false)
          (.ifK (.assign (.var rF) (.boolLit false))
            (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
            (envB envW) K1), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW rF).trans henvF) (hlook := hflag))
  -- retV false → exec else-assign → evalE ref (2 pure steps)
  have hB : stepFnIter 2 σ (.retV (.bool false)
      (.ifK (.assign (.var rF) (.boolLit false))
        (.assign (.var rI) (.add (.var rI) (.intLit 1 .int)))
        (envB envW) K1)) ch
      = .ok (.evalE (.ref rI) (envB envW)
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.add (.var rI) (.intLit 1 .int)] [] (.seqn #[]) (envB envW)
            K1), σ, ch) := by
    with_unfolding_all rfl
  have h10 : stepFnIter 1 σ (.evalE (.ref rI) (envB envW)
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.add (.var rI) (.intLit 1 .int)] [] (.seqn #[]) (envB envW)
        K1)) ch
      = .ok (.retV (.addr (.base ⟨li⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.add (.var rI) (.intLit 1 .int)] [] (.seqn #[]) (envB envW)
            K1), σ, ch) :=
    stepFnIter_one (stepFn_ref ((lookup_pushScope envW rI).trans henvI))
  -- addr → evalE add → evalE (var rI) (2 pure steps)
  have hC : stepFnIter 2 σ (.retV (.addr (.base ⟨li⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.add (.var rI) (.intLit 1 .int)] [] (.seqn #[]) (envB envW)
        K1)) ch
      = .ok (.evalE (.var rI) (envB envW)
          (.strictK .add [] [.intLit 1 .int] (envB envW)
            (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
              (.seqn #[]) (envB envW) K1)), σ, ch) := by
    with_unfolding_all rfl
  have h13 : stepFnIter 1 σ (.evalE (.var rI) (envB envW)
      (.strictK .add [] [.intLit 1 .int] (envB envW)
        (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
          (.seqn #[]) (envB envW) K1))) ch
      = .ok (.retV (.int a .int)
          (.strictK .add [] [.intLit 1 .int] (envB envW)
            (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
              (.seqn #[]) (envB envW) K1)), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW rI).trans henvI) (hlook := hidx))
  -- retV a → evalE intLit → retV 1 (2 pure steps)
  have hD : stepFnIter 2 σ (.retV (.int a .int)
      (.strictK .add [] [.intLit 1 .int] (envB envW)
        (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
          (.seqn #[]) (envB envW) K1))) ch
      = .ok (.retV (.int 1 .int)
          (.strictK .add [.int a .int] [] (envB envW)
            (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
              (.seqn #[]) (envB envW) K1)), σ, ch) := by
    with_unfolding_all rfl
  have h16 : stepFnIter 1 σ (.retV (.int 1 .int)
      (.strictK .add [.int a .int] [] (envB envW)
        (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
          (.seqn #[]) (envB envW) K1))) ch
      = .ok (.retV (.int (a + 1) .int)
          (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
            (.seqn #[]) (envB envW) K1), σ, ch) :=
    stepFnIter_one (stepFn_strict_apply
      (h := applyStrictOp_add_int (by omega) h1))
  -- rhsK drain → storeK entry (1 pure step)
  have hE : stepFnIter 1 σ (.retV (.int (a + 1) .int)
      (.rhsK .vals [.chain (.addr (.base ⟨li⟩)) [] []] [] []
        (.seqn #[]) (envB envW) K1)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨li⟩)) [] []]
          [.int (a + 1) .int] (.seqn #[]) (envB envW) K1), σ, ch) := by
    with_unfolding_all rfl
  have h18 : stepFnIter 1 σ (.next (.storeK
      [.chain (.addr (.base ⟨li⟩)) [] []] [.int (a + 1) .int]
      (.seqn #[]) (envB envW) K1)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envB envW) K1),
        { σ with heap := Heap.set σ.heap (.base ⟨li⟩) (idxCell (a + 1)) },
        ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := tI) (old := .int a .int)
        (hlook := hidx)
        (hnorm := normalize_int_signed (by omega) h1)))
  have hF : stepFnIter 3
      { σ with heap := Heap.set σ.heap (.base ⟨li⟩) (idxCell (a + 1)) }
      (.next (.storeK [] [] (.seqn #[]) (envB envW) K1)) ch
      = .ok (boundCfg rF rI rL uV body envW k,
        { σ with heap := Heap.set σ.heap (.base ⟨li⟩) (idxCell (a + 1)) },
        ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_chain (stepFnIter_one stepFn_seqn_splice)
        (stepFnIter_one stepFn_seq_pop))
  exact stepFnIter_chain hA (stepFnIter_chain h7 (stepFnIter_chain hB
    (stepFnIter_chain h10 (stepFnIter_chain hC (stepFnIter_chain h13
      (stepFnIter_chain hD (stepFnIter_chain h16 (stepFnIter_chain hE
        (stepFnIter_chain h18 hF)))))))))

/-- **Bound check, CONTINUE case** (`a < b`): 9 steps from the bound
check to the index bind, state untouched. -/
theorem bound_lt
    (henvI : LocalEnv.lookup envW rI = some (.base ⟨li⟩))
    (henvL : LocalEnv.lookup envW rL = some (.base ⟨ll⟩))
    {a b : Int} (hab : a < b)
    (hidx : Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell a))
    (hlen : Heap.lookup σ.heap (.base ⟨ll⟩) = some (idxCell b)) :
    stepFnIter 9 σ (boundCfg rF rI rL uV body envW k) ch
      = .ok (bindCfg rF rI rL uV body envW k, σ, ch) := by
  let K2 : Cont := .seq [initU uV, bindU uV rI, body] (envB envW)
    (wloopK rF rI rL uV body envW k)
  have hA : stepFnIter 2 σ (boundCfg rF rI rL uV body envW k) ch
      = .ok (.evalE (.var rI) (envB envW)
          (.strictK .atLeastCmp [] [.var rL] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) := by
    with_unfolding_all rfl
  have h3 : stepFnIter 1 σ (.evalE (.var rI) (envB envW)
      (.strictK .atLeastCmp [] [.var rL] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.int a .int)
          (.strictK .atLeastCmp [] [.var rL] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW rI).trans henvI) (hlook := hidx))
  have hB : stepFnIter 1 σ (.retV (.int a .int)
      (.strictK .atLeastCmp [] [.var rL] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.evalE (.var rL) (envB envW)
          (.strictK .atLeastCmp [.int a .int] [] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) := by
    with_unfolding_all rfl
  have h5 : stepFnIter 1 σ (.evalE (.var rL) (envB envW)
      (.strictK .atLeastCmp [.int a .int] [] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.int b .int)
          (.strictK .atLeastCmp [.int a .int] [] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW rL).trans henvL) (hlook := hlen))
  have h6 : stepFnIter 1 σ (.retV (.int b .int)
      (.strictK .atLeastCmp [.int a .int] [] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.bool false)
          (.ifK .breakStmt (.seqn #[]) (envB envW) K2), σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int b .int, GoValue.int a .int])
      = [GoValue.int a .int, GoValue.int b .int] from rfl,
      applyStrictOp_atLeast_int]
    congr 2
    simp [decide_eq_false_iff_not]
    omega
  have hC : stepFnIter 3 σ (.retV (.bool false)
      (.ifK .breakStmt (.seqn #[]) (envB envW) K2)) ch
      = .ok (bindCfg rF rI rL uV body envW k, σ, ch) := by
    have hif : stepFnIter 1 σ (.retV (.bool false)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2)) ch
        = .ok (.exec (.seqn #[]) (envB envW) K2, σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain hif (stepFnIter_splice_pop (ss := #[]) rfl)
  exact stepFnIter_chain hA (stepFnIter_chain h3 (stepFnIter_chain hB
    (stepFnIter_chain h5 (stepFnIter_chain h6 hC))))

/-- **Bound check, EXIT case** (`a ≥ b`): 10 steps from the bound
check to the loop's `.next k`, state untouched. -/
theorem bound_ge
    (henvI : LocalEnv.lookup envW rI = some (.base ⟨li⟩))
    (henvL : LocalEnv.lookup envW rL = some (.base ⟨ll⟩))
    {a b : Int} (hab : b ≤ a)
    (hidx : Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell a))
    (hlen : Heap.lookup σ.heap (.base ⟨ll⟩) = some (idxCell b)) :
    stepFnIter 10 σ (boundCfg rF rI rL uV body envW k) ch
      = .ok (.next k, σ, ch) := by
  let K2 : Cont := .seq [initU uV, bindU uV rI, body] (envB envW)
    (wloopK rF rI rL uV body envW k)
  have hA : stepFnIter 2 σ (boundCfg rF rI rL uV body envW k) ch
      = .ok (.evalE (.var rI) (envB envW)
          (.strictK .atLeastCmp [] [.var rL] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) := by
    with_unfolding_all rfl
  have h3 : stepFnIter 1 σ (.evalE (.var rI) (envB envW)
      (.strictK .atLeastCmp [] [.var rL] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.int a .int)
          (.strictK .atLeastCmp [] [.var rL] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW rI).trans henvI) (hlook := hidx))
  have hB : stepFnIter 1 σ (.retV (.int a .int)
      (.strictK .atLeastCmp [] [.var rL] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.evalE (.var rL) (envB envW)
          (.strictK .atLeastCmp [.int a .int] [] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) := by
    with_unfolding_all rfl
  have h5 : stepFnIter 1 σ (.evalE (.var rL) (envB envW)
      (.strictK .atLeastCmp [.int a .int] [] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.int b .int)
          (.strictK .atLeastCmp [.int a .int] [] (envB envW)
            (.ifK .breakStmt (.seqn #[]) (envB envW) K2)), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW rL).trans henvL) (hlook := hlen))
  have h6 : stepFnIter 1 σ (.retV (.int b .int)
      (.strictK .atLeastCmp [.int a .int] [] (envB envW)
        (.ifK .breakStmt (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.bool true)
          (.ifK .breakStmt (.seqn #[]) (envB envW) K2), σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int b .int, GoValue.int a .int])
      = [GoValue.int a .int, GoValue.int b .int] from rfl,
      applyStrictOp_atLeast_int]
    congr 2
    simp
    omega
  have hC : stepFnIter 4 σ (.retV (.bool true)
      (.ifK .breakStmt (.seqn #[]) (envB envW) K2)) ch
      = .ok (.next k, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain hA (stepFnIter_chain h3 (stepFnIter_chain hB
    (stepFnIter_chain h5 (stepFnIter_chain h6 hC))))

/-- **The index bind**: 11 steps from the bind entry to the body
configuration — the per-iteration index cell allocated at the current
`nextAddr` and set to the index value. -/
theorem bind_seg
    (henvI : LocalEnv.lookup envW rI = some (.base ⟨li⟩))
    (hUI : uV ≠ rI)
    {a : Int} (h0 : 0 ≤ a) (h1 : a < 2 ^ 63)
    (hidx : Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell a))
    (hfresh : Heap.lookup σ.heap (.base ⟨σ.nextAddr⟩) = none) :
    stepFnIter 11 σ (bindCfg rF rI rL uV body envW k) ch
      = .ok (bodyCfg rF rI rL uV body envW k σ.nextAddr,
        bindState σ a, ch) := by
  have hline : (li : Nat) ≠ σ.nextAddr := by
    intro he
    rw [he, hfresh] at hidx
    cases hidx
  let na := σ.nextAddr
  -- init: allocate the index cell (default 0), declare
  have h1s : stepFnIter 1 σ (bindCfg rF rI rL uV body envW k) ch
      = .ok (.next (.seq [bindU uV rI, body]
          ((envB envW).declare uV (.base ⟨na⟩))
          (wloopK rF rI rL uV body envW k)),
        { σ with heap := Heap.set σ.heap (.base ⟨na⟩) (idxCell 0), nextAddr := na + 1 }, ch) := by
    refine stepFnIter_one ?_
    have := stepFn_init_seq (σ := σ)
      (p := { id := uV, typ := tI })
      (rest := [bindU uV rI, body]) (env := envB envW)
      (k := wloopK rF rI rL uV body envW k) (ch := ch)
      (v := .int 0 .int) (hdef := defaultValue_tI)
    exact this
  have henvUeq : (envB envW).declare uV (.base ⟨na⟩) = envU envW uV na := rfl
  rw [henvUeq] at h1s
  let σ1 : ExecState :=
    { σ with heap := Heap.set σ.heap (.base ⟨na⟩) (idxCell 0), nextAddr := na + 1 }
  -- pop, exec assign, evalE ref (3 steps: 1 pure pop + assign entry + ref)
  have hB : stepFnIter 2 σ1 (.next (.seq [bindU uV rI, body]
      (envU envW uV na) (wloopK rF rI rL uV body envW k))) ch
      = .ok (.evalE (.ref uV) (envU envW uV na)
          (.tgtOpK (.chain []) [] [] [] [] .vals [.var rI] []
            (.seqn #[]) (envU envW uV na)
            (.seq [body] (envU envW uV na)
              (wloopK rF rI rL uV body envW k))), σ1, ch) := by
    with_unfolding_all rfl
  have h4s : stepFnIter 1 σ1 (.evalE (.ref uV) (envU envW uV na)
      (.tgtOpK (.chain []) [] [] [] [] .vals [.var rI] []
        (.seqn #[]) (envU envW uV na)
        (.seq [body] (envU envW uV na)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.retV (.addr (.base ⟨na⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [.var rI] []
            (.seqn #[]) (envU envW uV na)
            (.seq [body] (envU envW uV na)
              (wloopK rF rI rL uV body envW k))), σ1, ch) :=
    stepFnIter_one (stepFn_ref lookup_envU_self)
  have hC : stepFnIter 1 σ1 (.retV (.addr (.base ⟨na⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals [.var rI] []
        (.seqn #[]) (envU envW uV na)
        (.seq [body] (envU envW uV na)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.evalE (.var rI) (envU envW uV na)
          (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
            (.seqn #[]) (envU envW uV na)
            (.seq [body] (envU envW uV na)
              (wloopK rF rI rL uV body envW k))), σ1, ch) := by
    with_unfolding_all rfl
  have hidx1 : Heap.lookup σ1.heap (.base ⟨li⟩) = some (idxCell a) := by
    show Heap.lookup (Heap.set σ.heap (.base ⟨na⟩) (idxCell 0))
      (.base ⟨li⟩) = some (idxCell a)
    rw [lookup_set_other (Ne.symm hline)]
    exact hidx
  have h6s : stepFnIter 1 σ1 (.evalE (.var rI) (envU envW uV na)
      (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
        (.seqn #[]) (envU envW uV na)
        (.seq [body] (envU envW uV na)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.retV (.int a .int)
          (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
            (.seqn #[]) (envU envW uV na)
            (.seq [body] (envU envW uV na)
              (wloopK rF rI rL uV body envW k))), σ1, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_envU_ne hUI).trans henvI) (hlook := hidx1))
  have hD : stepFnIter 1 σ1 (.retV (.int a .int)
      (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
        (.seqn #[]) (envU envW uV na)
        (.seq [body] (envU envW uV na)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
          [.int a .int] (.seqn #[]) (envU envW uV na)
          (.seq [body] (envU envW uV na)
            (wloopK rF rI rL uV body envW k))), σ1, ch) := by
    with_unfolding_all rfl
  have h8s : stepFnIter 1 σ1 (.next (.storeK
      [.chain (.addr (.base ⟨na⟩)) [] []] [.int a .int] (.seqn #[])
      (envU envW uV na)
      (.seq [body] (envU envW uV na)
        (wloopK rF rI rL uV body envW k)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envU envW uV na)
          (.seq [body] (envU envW uV na)
            (wloopK rF rI rL uV body envW k))),
        { σ1 with heap := Heap.set σ1.heap (.base ⟨na⟩) (idxCell a) },
        ch) := by
    refine stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := tI) (old := .int 0 .int)
        (hlook := ?_) (hnorm := normalize_int_signed (by omega) h1)))
    show Heap.lookup (Heap.set σ.heap (.base ⟨na⟩) (idxCell 0))
      (.base ⟨na⟩) = some ⟨some tI, .int 0 .int⟩
    exact lookup_set_self
  have hE : stepFnIter 3
      { σ1 with heap := Heap.set σ1.heap (.base ⟨na⟩) (idxCell a) }
      (.next (.storeK [] [] (.seqn #[]) (envU envW uV na)
        (.seq [body] (envU envW uV na)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (bodyCfg rF rI rL uV body envW k na,
        { σ1 with heap := Heap.set σ1.heap (.base ⟨na⟩) (idxCell a) },
        ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_chain (stepFnIter_one stepFn_seqn_splice)
        (stepFnIter_one stepFn_seq_pop))
  have hfin := stepFnIter_chain h1s (stepFnIter_chain hB
    (stepFnIter_chain h4s (stepFnIter_chain hC (stepFnIter_chain h6s
      (stepFnIter_chain hD (stepFnIter_chain h8s hE))))))
  exact hfin

/-- **The back edge**: a normally-completed body reaches the loop
head in 2 steps, state untouched. -/
theorem back_edge {na : Nat} :
    stepFnIter 2 σ (bodyDoneCfg rF rI rL uV body envW k na) ch
      = .ok (headCfg rF rI rL uV body envW k, σ, ch) := by
  with_unfolding_all rfl

end Glue

/-! ## 6. The composed iteration and the LOOP SCHEMA -/

/-- The idx-cell value at the loop head of iteration `i` (the
increment happens INSIDE the iteration's glue). -/
def idxAt : Nat → Int
  | 0 => 0
  | i + 1 => i

@[simp] theorem idxAt_zero : idxAt 0 = 0 := rfl
@[simp] theorem idxAt_succ {i : Nat} : idxAt (i + 1) = i := rfl

/-- The flag-clear write (first iteration's glue). -/
def flagSet (lf : Nat) (σ : ExecState) : ExecState :=
  { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) }

/-- The index write (subsequent iterations' glue). -/
def idxSet (li : Nat) (v : Int) (σ : ExecState) : ExecState :=
  { σ with heap := Heap.set σ.heap (.base ⟨li⟩) (idxCell v) }

/-- The glue's head-state write at iteration `i`: the first iteration
clears the flag, later ones set the index. -/
def glueState (lf li : Nat) (i : Nat) (σ : ExecState) : ExecState :=
  if i = 0 then flagSet lf σ else idxSet li i σ

/-- `bindState` over a glue-written state, re-based on the ORIGINAL
state's record (the glue changes only the heap; the collapse the
instance body facts rewrite with). -/
theorem bindState_glue (lf li i : Nat) (σ : ExecState) (a : Int) :
    bindState (glueState lf li i σ) a
      = { σ with
          heap := (Heap.set (glueState lf li i σ).heap
            (.base ⟨σ.nextAddr⟩) (idxCell a)),
          nextAddr := σ.nextAddr + 1 } := by
  unfold glueState flagSet idxSet bindState
  split <;> simp [set_set]

/-- The glue's step count at iteration `i`. -/
def glueSteps : Nat → Nat
  | 0 => 17
  | _ + 1 => 21

section Loop

variable {rF rI rL uV : String} {body : Stmt} {envW : LocalEnv} {k : Cont}
  {σ : ExecState} {ch : Choices} {lf li ll : Nat}

/-- **The composed head → body walk of iteration `i`**
(`glueSteps i + 20` steps): glue + bound check (continue) + index
bind. -/
theorem iter_head_to_body
    (hFI : lf ≠ li) (hLF : ll ≠ lf) (hLI : ll ≠ li) (hUI : uV ≠ rI)
    (henvF : LocalEnv.lookup envW rF = some (.base ⟨lf⟩))
    (henvI : LocalEnv.lookup envW rI = some (.base ⟨li⟩))
    (henvL : LocalEnv.lookup envW rL = some (.base ⟨ll⟩))
    {i n : Nat} (hin : i < n) (hn63 : (n : Int) < 2 ^ 63)
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0)))
    (hidx : Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell (idxAt i)))
    (hlen : Heap.lookup σ.heap (.base ⟨ll⟩) = some (idxCell n))
    (hfresh : Heap.lookup σ.heap (.base ⟨σ.nextAddr⟩) = none) :
    stepFnIter (glueSteps i + 20) σ (headCfg rF rI rL uV body envW k) ch
      = .ok (bodyCfg rF rI rL uV body envW k σ.nextAddr,
        bindState (glueState lf li i σ) i, ch) := by
  have hlfna : lf ≠ σ.nextAddr := by
    intro he; rw [he, hfresh] at hflag; cases hflag
  have hlina : li ≠ σ.nextAddr := by
    intro he; rw [he, hfresh] at hidx; cases hidx
  cases i with
  | zero =>
      -- glue_first (17) + bound_lt (9) + bind_seg (11)
      have hg := glue_first (rI := rI) (rL := rL) (uV := uV)
        (body := body) (k := k) (ch := ch) henvF hflag
      have hσf_idx : Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩)
          (flagCell false)) (.base ⟨li⟩) = some (idxCell (idxAt 0)) := by
        rw [lookup_set_other hFI]; exact hidx
      have hσf_len : Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩)
          (flagCell false)) (.base ⟨ll⟩) = some (idxCell n) := by
        rw [lookup_set_other (Ne.symm hLF)]; exact hlen
      have hσf_fresh : Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩)
          (flagCell false)) (.base ⟨σ.nextAddr⟩) = none := by
        rw [lookup_set_other hlfna]; exact hfresh
      have hb := bound_lt (rF := rF) (uV := uV) (body := body) (k := k)
        (ch := ch)
        (σ := flagSet lf σ)
        henvI henvL (a := idxAt 0) (b := (n : Int))
        (by rw [idxAt_zero]; omega)
        hσf_idx hσf_len
      have hd := bind_seg (rF := rF) (rL := rL) (body := body) (k := k)
        (ch := ch)
        (σ := flagSet lf σ)
        henvI hUI (a := idxAt 0)
        (by rw [idxAt_zero]; omega) (by rw [idxAt_zero]; omega)
        hσf_idx hσf_fresh
      have := stepFnIter_chain hg (stepFnIter_chain hb hd)
      exact this
  | succ j =>
      -- glue_next (21) + bound_lt (9) + bind_seg (11)
      have hcast : idxAt (j + 1) + 1 = ((j + 1 : Nat) : Int) := by
        rw [idxAt_succ]; omega
      have hg := glue_next (rL := rL) (uV := uV) (body := body)
        (k := k) (ch := ch) henvF henvI
        (a := idxAt (j + 1))
        (by rw [idxAt_succ]; omega)
        (by rw [idxAt_succ]; omega)
        hflag hidx
      rw [hcast] at hg
      have hσg_idx : Heap.lookup (Heap.set σ.heap (.base ⟨li⟩)
          (idxCell ((j + 1 : Nat) : Int))) (.base ⟨li⟩)
          = some (idxCell ((j + 1 : Nat) : Int)) := lookup_set_self
      have hσg_len : Heap.lookup (Heap.set σ.heap (.base ⟨li⟩)
          (idxCell ((j + 1 : Nat) : Int))) (.base ⟨ll⟩)
          = some (idxCell n) := by
        rw [lookup_set_other (Ne.symm hLI)]; exact hlen
      have hσg_fresh : Heap.lookup (Heap.set σ.heap (.base ⟨li⟩)
          (idxCell ((j + 1 : Nat) : Int))) (.base ⟨σ.nextAddr⟩)
          = none := by
        rw [lookup_set_other hlina]; exact hfresh
      have hb := bound_lt (rF := rF) (uV := uV) (body := body) (k := k)
        (ch := ch)
        (σ := idxSet li ((j + 1 : Nat) : Int) σ)
        henvI henvL (a := ((j + 1 : Nat) : Int)) (b := (n : Int))
        (by omega) hσg_idx hσg_len
      have hd := bind_seg (rF := rF) (rL := rL) (body := body) (k := k)
        (ch := ch)
        (σ := idxSet li ((j + 1 : Nat) : Int) σ)
        henvI hUI (a := ((j + 1 : Nat) : Int))
        (by omega) (by omega) hσg_idx hσg_fresh
      have hall := stepFnIter_chain hg (stepFnIter_chain hb hd)
      -- align the glueState/bindState spellings
      show stepFnIter 41 σ (headCfg rF rI rL uV body envW k) ch = _
      have hgs : glueState lf li (j + 1) σ
          = idxSet li ((j + 1 : Nat) : Int) σ := by
        unfold glueState
        rw [if_neg (Nat.succ_ne_zero j)]
      rw [hgs]
      exact hall

/-- **The exit walk from the head at index `n`**
(`glueSteps n + 10` steps): glue + bound check (break) to the loop's
continuation. -/
theorem exit_from_head
    (hFI : lf ≠ li) (hLF : ll ≠ lf) (hLI : ll ≠ li)
    (henvF : LocalEnv.lookup envW rF = some (.base ⟨lf⟩))
    (henvI : LocalEnv.lookup envW rI = some (.base ⟨li⟩))
    (henvL : LocalEnv.lookup envW rL = some (.base ⟨ll⟩))
    {n : Nat} (hn63 : (n : Int) < 2 ^ 63)
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (n == 0)))
    (hidx : Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell (idxAt n)))
    (hlen : Heap.lookup σ.heap (.base ⟨ll⟩) = some (idxCell n)) :
    stepFnIter (glueSteps n + 10) σ (headCfg rF rI rL uV body envW k) ch
      = .ok (.next k, glueState lf li n σ, ch) := by
  cases n with
  | zero =>
      have hg := glue_first (rI := rI) (rL := rL) (uV := uV)
        (body := body) (k := k) (ch := ch) henvF hflag
      have hσf_idx : Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩)
          (flagCell false)) (.base ⟨li⟩) = some (idxCell (idxAt 0)) := by
        rw [lookup_set_other hFI]; exact hidx
      have hσf_len : Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩)
          (flagCell false)) (.base ⟨ll⟩) = some (idxCell 0) := by
        rw [lookup_set_other (Ne.symm hLF)]; exact hlen
      have hb := bound_ge (rF := rF) (uV := uV) (body := body) (k := k)
        (ch := ch)
        (σ := flagSet lf σ)
        henvI henvL (a := idxAt 0) (b := (0 : Int))
        (by rw [idxAt_zero]; omega)
        hσf_idx hσf_len
      exact stepFnIter_chain hg hb
  | succ j =>
      have hcast : idxAt (j + 1) + 1 = ((j + 1 : Nat) : Int) := by
        rw [idxAt_succ]; omega
      have hg := glue_next (rL := rL) (uV := uV) (body := body)
        (k := k) (ch := ch) henvF henvI
        (a := idxAt (j + 1))
        (by rw [idxAt_succ]; omega)
        (by rw [idxAt_succ]; omega)
        hflag hidx
      rw [hcast] at hg
      have hσg_idx : Heap.lookup (Heap.set σ.heap (.base ⟨li⟩)
          (idxCell ((j + 1 : Nat) : Int))) (.base ⟨li⟩)
          = some (idxCell ((j + 1 : Nat) : Int)) := lookup_set_self
      have hσg_len : Heap.lookup (Heap.set σ.heap (.base ⟨li⟩)
          (idxCell ((j + 1 : Nat) : Int))) (.base ⟨ll⟩)
          = some (idxCell (j + 1)) := by
        rw [lookup_set_other (Ne.symm hLI)]; exact hlen
      have hb := bound_ge (rF := rF) (uV := uV) (body := body) (k := k)
        (ch := ch)
        (σ := idxSet li ((j + 1 : Nat) : Int) σ)
        henvI henvL (a := ((j + 1 : Nat) : Int)) (b := ((j + 1 : Nat) : Int))
        (by omega) hσg_idx hσg_len
      have hall := stepFnIter_chain hg hb
      show stepFnIter 31 σ (headCfg rF rI rL uV body envW k) ch = _
      have hgs : glueState lf li (j + 1) σ
          = idxSet li ((j + 1 : Nat) : Int) σ := by
        unfold glueState
        rw [if_neg (Nat.succ_ne_zero j)]
      rw [hgs]
      exact hall

/-- **THE SLICE-WALK LOOP SCHEMA** (the module's headline; the
Floyd/Hoare loop invariant over the frontend's range-desugar shape).

Given a state family `S` (the loop invariant, indexed by iteration)
whose members carry the control cells at their scheduled values and a
fresh allocation frontier, and a BODY fact — from the glue-written,
index-bound state, the body completes normally within `bB` steps and
re-establishes the invariant — every `S i` state at the loop head
completes the whole remaining loop within `(43 + bB) * (n - i) + 31`
steps, delivering `.next k` at the exit-glue-written `S n` state.

The conclusion is BOUNDED-COMPLETION (compositional mode I2): the
exact per-run step count varies with the body's branches; consumers
get the bound, the final configuration, and the invariant. -/
theorem sliceWalk_loop
    (hFI : lf ≠ li) (hLF : ll ≠ lf) (hLI : ll ≠ li) (hUI : uV ≠ rI)
    (henvF : LocalEnv.lookup envW rF = some (.base ⟨lf⟩))
    (henvI : LocalEnv.lookup envW rI = some (.base ⟨li⟩))
    (henvL : LocalEnv.lookup envW rL = some (.base ⟨ll⟩))
    {n bB : Nat} (hn63 : (n : Int) < 2 ^ 63)
    (S : Nat → ExecState → Prop)
    (hS : ∀ i σ, i ≤ n → S i σ →
      Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0))
      ∧ Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell (idxAt i))
      ∧ Heap.lookup σ.heap (.base ⟨ll⟩) = some (idxCell n)
      ∧ Heap.lookup σ.heap (.base ⟨σ.nextAddr⟩) = none)
    (hbody : ∀ i σ ch, i < n → S i σ →
      ∃ m ≤ bB, ∃ σ',
        stepFnIter m (bindState (glueState lf li i σ) i)
          (bodyCfg rF rI rL uV body envW k σ.nextAddr) ch
          = .ok (bodyDoneCfg rF rI rL uV body envW k σ.nextAddr, σ', ch)
        ∧ S (i + 1) σ') :
    ∀ i σ ch, i ≤ n → S i σ →
      ∃ m ≤ (43 + bB) * (n - i) + 31, ∃ σf, S n σf ∧
        stepFnIter m σ (headCfg rF rI rL uV body envW k) ch
          = .ok (.next k, glueState lf li n σf, ch) := by
  suffices key : ∀ μ i σ ch, μ = n - i → i ≤ n → S i σ →
      ∃ m ≤ (43 + bB) * (n - i) + 31, ∃ σf, S n σf ∧
        stepFnIter m σ (headCfg rF rI rL uV body envW k) ch
          = .ok (.next k, glueState lf li n σf, ch) by
    intro i σ ch hin hSi
    exact key (n - i) i σ ch rfl hin hSi
  intro μ
  induction μ with
  | zero =>
      intro i σ ch hμ hin hSi
      have hi : i = n := by omega
      subst hi
      obtain ⟨hflag, hidx, hlen, _⟩ := hS i σ (Nat.le_refl i) hSi
      refine ⟨glueSteps i + 10, ?_, σ, hSi, ?_⟩
      · have : glueSteps i ≤ 21 := by
          cases i <;> simp [glueSteps]
        omega
      · exact exit_from_head (uV := uV) (body := body) (k := k)
          (σ := σ) (ch := ch) hFI hLF hLI henvF henvI henvL hn63
          hflag hidx hlen
  | succ μ' ih =>
      intro i σ ch hμ hin hSi
      have hlt : i < n := by omega
      obtain ⟨hflag, hidx, hlen, hfresh⟩ := hS i σ (by omega) hSi
      have hhead := iter_head_to_body (body := body) (k := k)
        (σ := σ) (ch := ch) hFI hLF hLI hUI henvF henvI henvL
        hlt hn63 hflag hidx hlen hfresh
      obtain ⟨m, hm, σ', hrun, hS'⟩ := hbody i σ ch hlt hSi
      have hback := back_edge (rF := rF) (rI := rI) (rL := rL)
        (uV := uV) (body := body) (envW := envW) (k := k) (σ := σ')
        (ch := ch) (na := σ.nextAddr)
      obtain ⟨m', hm', σf, hSf, hrest⟩ :=
        ih (i + 1) σ' ch (by omega) (by omega) hS'
      refine ⟨(glueSteps i + 20) + (m + (2 + m')), ?_, σf, hSf, ?_⟩
      · have hgs : glueSteps i ≤ 21 := by
          cases i <;> simp [glueSteps]
        have hmul : (43 + bB) * (n - (i + 1)) + (43 + bB)
            = (43 + bB) * (n - i) := by
          have : n - i = (n - (i + 1)) + 1 := by omega
          rw [this, Nat.mul_succ]
        omega
      · exact stepFnIter_chain hhead (stepFnIter_chain hrun
          (stepFnIter_chain hback hrest))

end Loop

end GoLean.SliceWalk
