import Lean
import GoLean.GoCore.Equations
import GoLean.GoCore.Prefix

/-!
# The toy semantic-equation CLIENT (window packet D, 2026-10-03; charter row 7, decision 8)

[AGENT packet D worker]. The re-pin offer's THIRD check: an independent client, GoCore only, over
SYMBOLIC state, environment and continuation, that USES the equation set `stepFn_eqns`
(`GoLean/GoCore/Equations.lean`) together with the `Prefix`/`Finish` lemmas (`GoLean/GoCore/
Prefix.lean`) and NEVER re-unfolds `stepFn` — `scripts/check-equations` greps this file for the
forbidden spellings and runs it. NOT an iris-lean `Language` instance (typed profiles PARKED
2026-09-16): no resource vocabulary, no facade, no runtime module imports this file.

§A — the FACTS: small symbolic runs proved only by rewriting with the equations (`simp only
[stepFn_eqns]`, or an equation applied to its explicit operation premises) and by
`Prefix.step`/`Prefix.done`/`Finish.aborted`. §B — the EXHAUSTIVE ENROLLMENT: one pin `Pin.<name>`
per theorem of the namespace `GoLean.GoCore.Equations`, its statement written out, checked by the
`#eval` at the end against the environment (every equation theorem has a pin, and the pin's type
IS the theorem's type up to alpha-equivalence — a statement drift fails here as well as in
`BridgeSet.lean`) — and the NO-UNFOLD CHECK of every fact's PROOF TERM and of every declaration of this file
the proof depends on, transitively, up to the PUBLISHED API (`apiModules`; the client's imports are WHITELISTED — pre-landing round, audit F2; window review F2; the re-verification's R1: no `stepFn.*` constant, no
reflexivity on a `stepFn`-headed term, the term re-type-checked with `stepFn` irreducible on every obligation
that can reach `stepFn`, the classical trio at most). `main` prints the PASS line the gate greps for; the
`#eval` fails the file before `main` can run when a fact — or a helper it uses — unfolds `stepFn`, an equation
is unenrolled or a pin has drifted.
-/

namespace Tests.EquationClient

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Equations
open GoLean.GoCore.ExecutionStatement (Prefix Finish FinishOutcome LRun)

/-! ## §A — the facts -/

section Facts
variable {ctx : ProgramCtx}

/-- A silent label, for readability. -/
abbrev silent : StepLabel := ⟨[], [], []⟩

/-- A read of the cell `l` recorded at the cell itself. -/
abbrev readOf (l : Loc) : StepLabel := ⟨[.access .read (.data l.canon)], [], []⟩

/-- A write of the cell `l`. -/
abbrev writeOf (l : Loc) : StepLabel := ⟨[.access .write (.data l.canon)], [], []⟩

/-- The drivers' barrier frame over the empty continuation, naming the subject `fid`. -/
abbrev barrier (fid : FuncId) : Cont := .frame [] [] [] [] .stop fid

/-- The caller's sequence frame of FACT 3 after its first statement: the call of `f` pending. -/
abbrev callerSeq (f : FuncId) (env : LocalEnv) (fid : FuncId) : Cont :=
  .seq [.call #[] f #[]] env (barrier fid)

/-- The callee's frame of FACT 3: targetless, resultless, defer-free, over the caller's continuation
after the call (the drained sequence glue on the barrier). -/
abbrev calleeFrame (env : LocalEnv) (fid cid : FuncId) : Cont :=
  .frame [] env [] [] (.seq [] env (barrier fid)) cid

/-- The chain entry a BOXED string payload raises (`panic(any("…"))`: the string at the dynamic type
`string`, `renderPanicPayload`'s string arm renders it). Settled — no preprint phase — when `string`
carries neither `Error` nor `String`: FACT 3's premise `hsettled`, inhabited below. The window
review's F1: an UNBOXED `.string` is not a Go interface value and has no rendering arm
(`witness_unboxed_payload_unrenderable`). -/
abbrev strEntry (ctx : ProgramCtx) (txt : GoString) : PanicEntry :=
  panicEntryOf ctx (.interface .string (.string txt))

/-- FACT 1 — a call entry then a return: a nullary declared call enters its frame (the entry
premise bottoms out in `enterFrame`, which `enterFrame_declared` reduces to `bindParams`/
`allocDecls`), the body returns, the empty frame pops: three steps to `.next k`, the entry's trace
the only label. -/
theorem fact_call_then_return {s s' : Store} {fid : FuncId} {func : Func} {fenv : LocalEnv}
    {tr : AccessTrace} (env : LocalEnv) (k : Cont) (ch : Choices)
    (he : enterFrame ctx s fid [] = .ok (.run func fenv [], s', tr)) (hbody : func.body = .returnStmt) :
    Prefix ctx 3 s (.exec (.call #[] fid #[]) env k) ch [⟨tr, [], []⟩, silent, silent] s' (.next k) ch := by
  refine .step (c₁ := .exec func.body fenv (.frame [] env [] [] k func.id)) (s₁ := s') (ch₁ := ch) ?_
    (.step (c₁ := .signal .ret (.frame [] env [] [] k func.id)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .next k) (s₁ := s') (ch₁ := ch) ?_ .done))
  · rw [exec_call_nullary env k ch rfl rfl he]; rfl
  · rw [hbody]; simp only [stepFn_eqns]
  · simp only [stepFn_eqns]

/-- FACT 2 — a `defer` registered then drained on return: the deferred callee is read from a local
(`loadRoot`), registered on the enclosing frame through the sequence glue (`pushDefer`), and at
the frame's `return` the pending call is entered on the frame (the drain), returns, and the frame
pops — twelve steps, two labels: the callee read and the drain's entry trace. -/
theorem fact_defer_then_drain {s s' : Store} {g : VarId} {gl : Loc} {gfid : FuncId} {gfunc : Func}
    {genv : LocalEnv} {tr : AccessTrace} (fenv env : LocalEnv) (k : Cont) (fid : FuncId) (ch : Choices)
    (hl : LocalEnv.lookup fenv g = some gl) (hv : loadRoot ctx s gl = .ok (.funcVal gfid []))
    (he : enterFrame ctx s gfid [] = .ok (.run gfunc genv [], s', tr)) (hbody : gfunc.body = .returnStmt) :
    Prefix ctx 12 s (.exec (.seqn #[.deferCall (.var g) #[], .returnStmt]) fenv (.frame [] env [] [] k fid)) ch
      [silent, silent, silent, readOf gl, silent, silent, silent, silent, ⟨tr, [], []⟩, silent, silent, silent]
      s' (.next k) ch := by
  refine .step (c₁ := .next (.seq [.deferCall (.var g) #[], .returnStmt] fenv (.frame [] env [] [] k fid)))
      (s₁ := s) (ch₁ := ch) ?_ (.step (c₁ := .exec (.deferCall (.var g) #[]) fenv
        (.seq [.returnStmt] fenv (.frame [] env [] [] k fid))) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .evalE (.var g) fenv (.deferCalleeK [] fenv (.seq [.returnStmt] fenv (.frame [] env [] [] k fid))))
        (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .retV (.funcVal gfid []) (.deferCalleeK [] fenv (.seq [.returnStmt] fenv (.frame [] env [] [] k fid))))
        (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .next (.seq [.returnStmt] fenv (.frame [] env [] [(.funcVal gfid [], [])] k fid)))
        (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .exec .returnStmt fenv (.seq [] fenv (.frame [] env [] [(.funcVal gfid [], [])] k fid)))
        (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .signal .ret (.seq [] fenv (.frame [] env [] [(.funcVal gfid [], [])] k fid)))
        (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .signal .ret (.frame [] env [] [(.funcVal gfid [], [])] k fid)) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .exec gfunc.body genv (.frame [] [] [] [] (.frame [] env [] [] k fid) gfunc.id))
        (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .signal .ret (.frame [] [] [] [] (.frame [] env [] [] k fid) gfunc.id)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .next (.frame [] env [] [] k fid)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .next k) (s₁ := s') (ch₁ := ch) ?_ .done)))))))))))
  · simp only [stepFn_eqns]; rfl
  · simp only [stepFn_eqns]
  · simp only [stepFn_eqns]
  · rw [evalE_var fenv _ ch hl hv]; rfl
  · rw [retV_deferCalleeK_push fenv ch rfl rfl]
  · simp only [stepFn_eqns]
  · simp only [stepFn_eqns]
  · rw [signal_table ch (signalStep_seq .ret [] fenv _)]
  · rw [signal_ret_frame, frameExit_defer_run [] env [] [] k fid ch he]
  · rw [hbody]; simp only [stepFn_eqns]
  · simp only [stepFn_eqns]
  · simp only [stepFn_eqns]

/-- FACT 3 — a write, then a CALLEE's panic: the store `x = y` lands in the caller (one `loadRoot`, one
`storeLoc`), the nullary declared call `f()` ENTERS its frame (`enterFrame`, FACT 1's entry premise; its
trace `tr` is the call's one label), the callee's body `panic(any(txt))` BOXES the string
(`applyStrictOp_toInterface_string`) and RAISES it, the chain unwinds through the callee's empty frame, the
caller's sequence glue and the barrier frame to the empty continuation, and the run FINISHES aborted at the
endpoint store `s'`, the written one: the write survives the abort. Twenty steps. The premises: the memory
floor (`hlx`/`hly`/`hy`/`hst`), the entry (`he`, store-preserving for a parameterless, resultless callee) and
its body (`hbody`), and the boxed string entry's rendering — SETTLED (`hsettled`: `string` carries no
`Error`/`String` method, so no preprint phase; the `repanicCollapse` consult is then at bound 1, nothing
drawn) and the renderer's text `t` (`hmsg`). Every premise is INHABITED by
`fact_inhabit_write_survives_panic` below (the window review's F1: the previous statement raised an UNBOXED
`.string`, whose `hmsg` no context satisfies — `witness_unboxed_premise_false`). -/
theorem fact_write_survives_panic {s s' : Store} {x y : VarId} {lx ly : Loc} {vy : GoValue}
    {f : FuncId} {func : Func} {fenv : LocalEnv} {tr : AccessTrace} {ty : Ty} {txt : GoString} {t : String}
    (env : LocalEnv) (fid : FuncId) (ch : Choices)
    (hlx : LocalEnv.lookup env x = some lx) (hly : LocalEnv.lookup env y = some ly)
    (hy : loadRoot ctx s ly = .ok vy) (hst : storeLoc ctx s lx vy = .ok s')
    (he : enterFrame ctx s' f [] = .ok (.run func fenv [], s', tr))
    (hbody : func.body = .panicStmt (.toInterface ty .string (.stringLit txt)))
    (hsettled : splitNewestPending? [strEntry ctx txt] = none)
    (hmsg : abortMsg ctx (strEntry ctx txt) [] 0 = .ok t) :
    LRun ctx s (.exec (.seqn #[.assign (.var x) (.var y), .call #[] f #[]]) env (barrier fid)) ch
      [silent, silent, silent, silent, silent, readOf ly, silent, writeOf lx, silent, silent, silent,
        ⟨tr, [], []⟩, silent, silent, silent, silent, silent, silent, silent, silent]
      [] (.aborted t s' ch) := by
  have hprefix : Prefix ctx 20 s (.exec (.seqn #[.assign (.var x) (.var y), .call #[] f #[]]) env (barrier fid)) ch
      [silent, silent, silent, silent, silent, readOf ly, silent, writeOf lx, silent, silent, silent,
        ⟨tr, [], []⟩, silent, silent, silent, silent, silent, silent, silent, silent]
      s' (.panicking [strEntry ctx txt] .stop) ch := by
    refine .step (c₁ := .next (.seq [.assign (.var x) (.var y), .call #[] f #[]] env (barrier fid))) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .exec (.assign (.var x) (.var y)) env (callerSeq f env fid)) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .evalE (.ref x) env (.tgtOpK (.chain []) [] [] [] [] .vals [.var y] [] (.seqn #[]) env (callerSeq f env fid))) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .retV (.addr lx) (.tgtOpK (.chain []) [] [] [] [] .vals [.var y] [] (.seqn #[]) env (callerSeq f env fid))) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .evalE (.var y) env (.rhsK .vals [.chain (.addr lx) [] []] [] [] (.seqn #[]) env (callerSeq f env fid))) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .retV vy (.rhsK .vals [.chain (.addr lx) [] []] [] [] (.seqn #[]) env (callerSeq f env fid))) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .next (.storeK [.chain (.addr lx) [] []] [vy] (.seqn #[]) env (callerSeq f env fid))) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .next (.storeK [] [] (.seqn #[]) env (callerSeq f env fid))) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .exec (.seqn #[]) env (callerSeq f env fid)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .next (callerSeq f env fid)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .exec (.call #[] f #[]) env (.seq [] env (barrier fid))) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .exec func.body fenv (calleeFrame env fid func.id)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .evalE (.toInterface ty .string (.stringLit txt)) fenv (.panicArgK (calleeFrame env fid func.id))) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .evalE (.stringLit txt) fenv (.strictK (.toInterface ty .string) [] [] fenv (.panicArgK (calleeFrame env fid func.id)))) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .retV (.string txt) (.strictK (.toInterface ty .string) [] [] fenv (.panicArgK (calleeFrame env fid func.id)))) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .retV (.interface .string (.string txt)) (.panicArgK (calleeFrame env fid func.id))) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .panicking [strEntry ctx txt] (calleeFrame env fid func.id)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .panicking [strEntry ctx txt] (.seq [] env (barrier fid))) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .panicking [strEntry ctx txt] (barrier fid)) (s₁ := s') (ch₁ := ch) ?_
      (.step (c₁ := .panicking [strEntry ctx txt] .stop) (s₁ := s') (ch₁ := ch) ?_ .done)))))))))))))))))))
    · simp only [stepFn_eqns]; rfl
    · simp only [stepFn_eqns]
    · simp only [stepFn_eqns]
    · rw [evalE_ref env _ ch hlx]
    · rw [retV_tgtOpK_rhs [] .vals (.var y) [] [] (.seqn #[]) env (callerSeq f env fid) ch (completeTargetRef_var (.addr lx))]; rfl
    · rw [evalE_var env _ ch hly hy]; rfl
    · rw [retV_rhsK_apply [.chain (.addr lx) [] []] (.seqn #[]) env (callerSeq f env fid) ch (applyRhsOp_vals s [vy])]
    · rw [next_storeK_var [] [] (.seqn #[]) env (callerSeq f env fid) ch hst]
    · simp only [stepFn_eqns]
    · rw [exec_seqn, seqCont_seq]; rfl
    · simp only [stepFn_eqns]
    · rw [exec_call_nullary env _ ch rfl rfl he]; rfl
    · rw [hbody]; simp only [stepFn_eqns]
    · rw [evalE_strict_more (e := .toInterface ty .string (.stringLit txt)) fenv _ ch rfl]
    · simp only [stepFn_eqns]
    · rw [retV_strictK_apply (v := .string txt) (done := []) fenv _ ch rfl
        (applyStrictOp_toInterface_string s' _ ty (.string txt))]
    · simp only [stepFn_eqns, panicPayload]
    · simp only [stepFn_eqns]
    · simp only [stepFn_eqns]
    · simp only [stepFn_eqns]
  -- the finish: a settled single-entry chain at the empty continuation is the abort; its consult is at
  -- bound 1 (a single entry has no equal successor), so nothing is drawn
  have hwidth : repanicCollapseWidth (strEntry ctx txt) [] = 1 := rfl
  refine ⟨20, s', .panicking [strEntry ctx txt] .stop, ch, 1, hprefix, ?_⟩
  refine Finish.aborted (Config.abort?_of_settled hsettled) ?_ hmsg
  rw [hwidth]
  exact Choices.consumeAtE_le_one (Nat.le_refl 1)

/-! ### FACT 3's premises are INHABITED (window review F1) -/

/-- The payload text of the inhabitation. -/
def boomText : GoString := GoString.fromLeanString "boom"

/-- The boxing target: the empty interface. -/
def anyTy : Ty := .interface ⟨"any"⟩

/-- The callee `boom()`: parameterless, resultless, its body `panic(any("boom"))`. -/
def boomFunc : Func :=
  { id := ⟨"boom"⟩, args := #[], results := #[], body := .panicStmt (.toInterface anyTy .string (.stringLit boomText)) }

/-- The context: the reserved types and the one function. -/
def boomCtx : ProgramCtx := ProgramCtx.ofTables TypeEnv.reserved #[boomFunc]

/-- Two root `int` cells — `x` (cell 0, holding 0) and `y` (cell 1, holding 7) — … -/
def boomStore₀ : Store := { heap := #[.value .int (.int 0 .int), .value .int (.int 7 .int)] }

/-- … and the store after `x = y`: the write FACT 3 says survives. -/
def boomStore₁ : Store := { heap := #[.value .int (.int 7 .int), .value .int (.int 7 .int)] }

/-- The caller's environment: `x ↦ cell 0`, `y ↦ cell 1`. -/
def boomEnv : LocalEnv := [[(0, .base ⟨0⟩), (1, .base ⟨1⟩)]]

/-- FACT 3 INHABITED: every premise discharged by computation at the concrete context, stores and environment
above (the lookups, the read, the write, the entry — `enterFrame` of a parameterless callee is store- and
trace-free — the body, the settled chain, and the renderer's `"boom"` by `with_unfolding_all rfl`: the abort's
UTF-8 decoding is well-founded recursion). The conclusion is FACT 3's at these values — so the symbolic
statement is not vacuous. The enrollment check verifies this proof too (it is a `fact_*`): its premise
obligations name no constant that unfolds to `stepFn`, so none is re-run. -/
theorem fact_inhabit_write_survives_panic :
    LRun boomCtx boomStore₀
      (.exec (.seqn #[.assign (.var 0) (.var 1), .call #[] ⟨"boom"⟩ #[]]) boomEnv (barrier ⟨"main"⟩)) []
      [silent, silent, silent, silent, silent, readOf (.base ⟨1⟩), silent, writeOf (.base ⟨0⟩), silent, silent,
        silent, silent, silent, silent, silent, silent, silent, silent, silent, silent]
      [] (.aborted "boom" boomStore₁ []) :=
  fact_write_survives_panic (lx := .base ⟨0⟩) (ly := .base ⟨1⟩) (vy := .int 7 .int) (func := boomFunc) (fenv := [])
    (ty := anyTy) (txt := boomText) boomEnv ⟨"main"⟩ [] rfl rfl rfl rfl rfl rfl rfl (by with_unfolding_all rfl)

/-- FACT 4 — an `if` on a symbolic Boolean: the condition is read from a local, and the branch
taken is `if bv then t else e` for the symbolic `bv` — three steps, one read. -/
theorem fact_if_symbolic {s : Store} {b : VarId} {lb : Loc} {bv : Bool} (t e : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices) (hl : LocalEnv.lookup env b = some lb) (hv : loadRoot ctx s lb = .ok (.bool bv)) :
    Prefix ctx 3 s (.exec (.ifThenElse (.var b) t e) env k) ch [silent, readOf lb, silent] s
      (.exec (if bv then t else e) env k) ch := by
  refine .step (c₁ := .evalE (.var b) env (.ifK t e env k)) (s₁ := s) (ch₁ := ch) ?_
    (.step (c₁ := .retV (.bool bv) (.ifK t e env k)) (s₁ := s) (ch₁ := ch) ?_
      (.step (c₁ := .exec (if bv then t else e) env k) (s₁ := s) (ch₁ := ch) ?_ .done))
  · simp only [stepFn_eqns]
  · rw [evalE_var env _ ch hl hv]; rfl
  · cases bv
    · rw [retV_ifK_false t e env k ch (valueAsBool_bool false)]; rfl
    · rw [retV_ifK_true t e env k ch (valueAsBool_bool true)]; rfl

/-- FACT 5 — a load/store pair: the assignment `x = y` is seven steps on the target spine — the
target's address, the right-hand side's read (`loadRoot`), the value source, the store
(`storeLoc`) — ending at the statement's empty body with the written store. -/
theorem fact_load_store {s s' : Store} {x y : VarId} {lx ly : Loc} {vy : GoValue} (env : LocalEnv) (k : Cont)
    (ch : Choices) (hlx : LocalEnv.lookup env x = some lx) (hly : LocalEnv.lookup env y = some ly)
    (hy : loadRoot ctx s ly = .ok vy) (hst : storeLoc ctx s lx vy = .ok s') :
    Prefix ctx 7 s (.exec (.assign (.var x) (.var y)) env k) ch
      [silent, silent, silent, readOf ly, silent, writeOf lx, silent] s' (.exec (.seqn #[]) env k) ch := by
  refine .step (c₁ := .evalE (.ref x) env (.tgtOpK (.chain []) [] [] [] [] .vals [.var y] [] (.seqn #[]) env k))
      (s₁ := s) (ch₁ := ch) ?_
    (.step (c₁ := .retV (.addr lx) (.tgtOpK (.chain []) [] [] [] [] .vals [.var y] [] (.seqn #[]) env k))
      (s₁ := s) (ch₁ := ch) ?_
    (.step (c₁ := .evalE (.var y) env (.rhsK .vals [.chain (.addr lx) [] []] [] [] (.seqn #[]) env k))
      (s₁ := s) (ch₁ := ch) ?_
    (.step (c₁ := .retV vy (.rhsK .vals [.chain (.addr lx) [] []] [] [] (.seqn #[]) env k)) (s₁ := s) (ch₁ := ch) ?_
    (.step (c₁ := .next (.storeK [.chain (.addr lx) [] []] [vy] (.seqn #[]) env k)) (s₁ := s) (ch₁ := ch) ?_
    (.step (c₁ := .next (.storeK [] [] (.seqn #[]) env k)) (s₁ := s') (ch₁ := ch) ?_
    (.step (c₁ := .exec (.seqn #[]) env k) (s₁ := s') (ch₁ := ch) ?_ .done))))))
  · simp only [stepFn_eqns]
  · rw [evalE_ref env _ ch hlx]
  · rw [retV_tgtOpK_rhs [] .vals (.var y) [] [] (.seqn #[]) env k ch (completeTargetRef_var (.addr lx))]; rfl
  · rw [evalE_var env _ ch hly hy]; rfl
  · rw [retV_rhsK_apply [.chain (.addr lx) [] []] (.seqn #[]) env k ch (applyRhsOp_vals s [vy])]
  · rw [next_storeK_var [] [] (.seqn #[]) env k ch hst]
  · simp only [stepFn_eqns]

/-- FACT 6 — the store reads back: the root-cell write law and the root-cell read law compose —
the cell holds the value NORMALIZED at its declared type. -/
theorem fact_store_then_load {s s' : Store} {a : Addr} {ty : Ty} {old v v' : GoValue}
    (hcell : Heap.lookup s.heap (.base a) = some (.value ty old))
    (hn : normalizeValueForTy ctx ty v = .ok v') (hst : storeLoc ctx s (.base a) v = .ok s') :
    loadRoot ctx s' (.base a) = .ok v' := by
  rw [storeLoc_root hcell hn] at hst
  cases hst
  exact loadRoot_base (Heap.lookup_set_self (hi := Heap.lookup_lt hcell))

/-- FACT 7 — a block entry allocating, then a lookup: entering `{ var p bool; if p … }` allocates
`p`'s cell at the entry slot (`Store.alloc`, bottomed out through `allocDecls_cons`/`_nil`), binds it
in the fresh scope, and the condition's read finds the zero value in the new cell — the else branch
runs. Five steps, one read. -/
theorem fact_block_then_lookup {s s' : Store} {p : Param} {loc : Loc} (t e : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices) (hty : p.typ = .bool) (hal : Store.alloc ctx s (.bool false) .bool = .ok (loc, s')) :
    Prefix ctx 5 s (.exec (.block #[p] #[.ifThenElse (.var p.id) t e]) env k) ch
      [silent, silent, silent, readOf loc, silent] s'
      (.exec e (env.pushScope.declare p.id loc) (.seq [] (env.pushScope.declare p.id loc) k)) ch := by
  have hd : defaultValue ctx p.typ = .ok (.bool false) := by rw [hty]; rfl
  have hal' : Store.alloc ctx s (.bool false) p.typ = .ok (loc, s') := by rw [hty]; exact hal
  have ha : allocDecls ctx env.pushScope s [p] = .ok (env.pushScope.declare p.id loc, s') := by
    rw [allocDecls_cons [] hd hal', allocDecls_nil]
  obtain ⟨vz, hnorm, hheap⟩ := Store.alloc_cell hal
  obtain ⟨rfl, -⟩ := Store.alloc_shape hal
  have hz : vz = .bool false := by
    have : normalizeValueForTy ctx .bool (.bool false) = .ok (.bool false) := rfl
    rw [this] at hnorm; cases hnorm; rfl
  subst hz
  have hread : loadRoot ctx s' (.base ⟨s.heap.size⟩) = .ok (.bool false) := by
    apply loadRoot_base
    rw [hheap]
    exact Heap.lookup_push_self
  refine .step (c₁ := .next (.seq [.ifThenElse (.var p.id) t e] (env.pushScope.declare p.id (.base ⟨s.heap.size⟩)) k))
      (s₁ := s') (ch₁ := ch) ?_
    (.step (c₁ := .exec (.ifThenElse (.var p.id) t e) (env.pushScope.declare p.id (.base ⟨s.heap.size⟩))
        (.seq [] (env.pushScope.declare p.id (.base ⟨s.heap.size⟩)) k)) (s₁ := s') (ch₁ := ch) ?_
    (.step (c₁ := .evalE (.var p.id) (env.pushScope.declare p.id (.base ⟨s.heap.size⟩))
        (.ifK t e (env.pushScope.declare p.id (.base ⟨s.heap.size⟩)) (.seq [] (env.pushScope.declare p.id (.base ⟨s.heap.size⟩)) k)))
      (s₁ := s') (ch₁ := ch) ?_
    (.step (c₁ := .retV (.bool false) (.ifK t e (env.pushScope.declare p.id (.base ⟨s.heap.size⟩))
        (.seq [] (env.pushScope.declare p.id (.base ⟨s.heap.size⟩)) k))) (s₁ := s') (ch₁ := ch) ?_
    (.step (c₁ := .exec e (env.pushScope.declare p.id (.base ⟨s.heap.size⟩))
        (.seq [] (env.pushScope.declare p.id (.base ⟨s.heap.size⟩)) k)) (s₁ := s') (ch₁ := ch) ?_ .done))))
  · rw [exec_block #[.ifThenElse (.var p.id) t e] k ch ha]
  · simp only [stepFn_eqns]
  · simp only [stepFn_eqns]
  · rw [evalE_var _ _ ch (LocalEnv.lookup_declare_self _ _ _) hread]; rfl
  · rw [retV_ifK_false t e _ _ ch (valueAsBool_bool false)]

/-- FACT 8 — the plain simp-set idiom: a premise-free arm closes by `simp only [stepFn_eqns]` alone. The gate's
bypass self-tests replace THIS proof line (the `BYPASS-ANCHOR`) by each unfolding spelling the audit listed and
require the enrollment check to REFUSE the fact by name. -/
theorem fact_usage_simp_set (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec .returnStmt env k) ch = .ok (.signal .ret k, s, ch, silent) := by
  simp only [stepFn_eqns]  -- BYPASS-ANCHOR

/-- FACT 9 — the INSTANTIATION idiom (`rw`): a premised arm whose successor names premise-bound values
(`loc`, `v`) is applied to its premises. -/
theorem fact_usage_rw {s : Store} {id : VarId} {loc : Loc} {v : GoValue} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hl : LocalEnv.lookup env id = some loc) (hv : loadRoot ctx s loc = .ok v) :
    stepFn ctx s (.evalE (.var id) env k) ch = .ok (.retV v k, s, ch, readOf (projChainTarget ctx s k loc)) := by
  rw [evalE_var env k ch hl hv]

/-- FACT 10 — the instantiated-simp idiom: the same arm, handed to `simp only` already applied to its premises. -/
theorem fact_usage_simp_instance {s : Store} {id : VarId} {loc : Loc} {v : GoValue} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hl : LocalEnv.lookup env id = some loc) (hv : loadRoot ctx s loc = .ok v) :
    stepFn ctx s (.evalE (.var id) env k) ch = .ok (.retV v k, s, ch, readOf (projChainTarget ctx s k loc)) := by
  simp only [evalE_var env k ch hl hv]

/-- FACT 11 — the DISCHARGER idiom: the whole rewrite set, the arm's premises found in context by `assumption`
(the plain `simp only [stepFn_eqns, hl, hv]` cannot fire here — the successor names `loc` and `v`). -/
theorem fact_usage_simp_discharger {s : Store} {id : VarId} {loc : Loc} {v : GoValue} (env : LocalEnv) (k : Cont) (ch : Choices)
    (hl : LocalEnv.lookup env id = some loc) (hv : loadRoot ctx s loc = .ok v) :
    stepFn ctx s (.evalE (.var id) env k) ch = .ok (.retV v k, s, ch, readOf (projChainTarget ctx s k loc)) := by
  simp (discharger := assumption) only [stepFn_eqns]

end Facts

/-! ### The window review's witnesses (F1): the UNBOXED payload has no rendering -/

section Witnesses

/-- An unboxed `.string` payload is not a Go interface value: `renderPanicPayload` has no arm for it, for
every context and text. -/
theorem witness_unboxed_payload_unrenderable (ctx : ProgramCtx) (txt : GoString) :
    renderPanicPayload ctx (panicEntryOf ctx (.string txt)) = none := rfl

/-- … so the previous FACT 3's rendering premise — `abortMsg` of that entry answering `.ok t` — was
UNSATISFIABLE: it refutes itself for every context, text and `t` (the previous fact was vacuous). -/
theorem witness_unboxed_premise_false (ctx : ProgramCtx) (txt : GoString) (t : String)
    (hmsg : abortMsg ctx (panicEntryOf ctx (.string txt)) [] 0 = .ok t) : False := by
  cases hmsg

end Witnesses

/-- The number of facts above (cross-checked against the environment by the `#eval` below). -/
def factCount : Nat := 12

/-! ## §B — the exhaustive enrollment: one pin per equation theorem, the statement written out -/

section Pins
-- GENERATED from GoLean/GoCore/Equations.lean (one `Pin.<name>` per theorem of the namespace
-- `GoLean.GoCore.Equations`, its statement written out); the `#eval` below checks the set is
-- exhaustive and every pin's type is the theorem's.
-- PINS-BEGIN
theorem Pin.storeTarget_inv_panic : ∀ {ctx : ProgramCtx} {s : Store} {r : TargetRef} {v : GoValue}
    {msg : String} (_h : storeTarget ctx s r v = .error (.panic msg)),
    storeTarget.plan ctx s r v = .error (.panic msg) :=
  @GoLean.GoCore.Equations.storeTarget_inv_panic

theorem Pin.applyStmtOp_inv_panic : ∀ {ctx : ProgramCtx} {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {msg : String} (_h : applyStmtOp ctx s ch op nt vs = .error (.panic msg)),
    applyStmtOp.plan ctx s ch op nt vs = .error (.panic msg) :=
  @GoLean.GoCore.Equations.applyStmtOp_inv_panic

theorem Pin.toResult_of_error : ∀ {α : Type} {x : Except Stop α} {e : Stop} (_h : x = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    toResult x = .error e :=
  @GoLean.GoCore.Equations.toResult_of_error

theorem Pin.valueAsBool_bool : ∀ (b : Bool),
    valueAsBool (.bool b) = .ok b :=
  @GoLean.GoCore.Equations.valueAsBool_bool

theorem Pin.valueAsLoc_addr : ∀ (loc : Loc),
    valueAsLoc (.addr loc) = .ok loc :=
  @GoLean.GoCore.Equations.valueAsLoc_addr

theorem Pin.valueAsLoc_nil :
    valueAsLoc .nil = .error (.panic nilDerefPanicText) :=
  @GoLean.GoCore.Equations.valueAsLoc_nil

theorem Pin.targetPlan_var : ∀ (id : VarId),
    targetPlan (.var id) = some (.chain [], [.ref id]) :=
  @GoLean.GoCore.Equations.targetPlan_var

theorem Pin.completeTargetRef_var : ∀ (a : GoValue),
    completeTargetRef (.chain []) [a] = some (.chain a [] []) :=
  @GoLean.GoCore.Equations.completeTargetRef_var

theorem Pin.resolveChain_nil : ∀ {ctx : ProgramCtx} (s : Store) (a : GoValue),
    resolveChain ctx s a [] [] = .ok a :=
  @GoLean.GoCore.Equations.resolveChain_nil

theorem Pin.applyRhsOp_vals : ∀ {ctx : ProgramCtx} (s : Store) (vs : List GoValue),
    applyRhsOp ctx s .vals vs = .ok (vs, []) :=
  @GoLean.GoCore.Equations.applyRhsOp_vals

theorem Pin.applyStrictOp_toInterface_string : ∀ {ctx : ProgramCtx} (s : Store) (tgt : Loc → Loc) (ty : Ty) (v : GoValue),
    applyStrictOp ctx s tgt (.toInterface ty .string) [v] = .ok (.interface .string v, s, []) :=
  @GoLean.GoCore.Equations.applyStrictOp_toInterface_string

theorem Pin.loadRoot_base : ∀ {ctx : ProgramCtx} {s : Store} {a : Addr} {ty : Ty} {v : GoValue}
    (_hl : Heap.lookup s.heap (.base a) = some (.value ty v)),
    loadRoot ctx s (.base a) = .ok v :=
  @GoLean.GoCore.Equations.loadRoot_base

theorem Pin.storeLoc_root : ∀ {ctx : ProgramCtx} {s : Store} {a : Addr} {ty : Ty} {old v v' : GoValue}
    (hl : Heap.lookup s.heap (.base a) = some (.value ty old)) (_hn : normalizeValueForTy ctx ty v = .ok v'),
    storeLoc ctx s (.base a) v = .ok { heap := s.heap.set a.id (.value ty v') (Heap.lookup_lt hl) } :=
  @GoLean.GoCore.Equations.storeLoc_root

theorem Pin.Heap.lookup_set_self : ∀ {h : Heap} {i : Nat} {c : HeapCell} {hi : i < h.size},
    Heap.lookup (h.set i c hi) (.base ⟨i⟩) = some c :=
  @GoLean.GoCore.Equations.Heap.lookup_set_self

theorem Pin.Heap.lookup_push_self : ∀ {h : Heap} {c : HeapCell},
    Heap.lookup (h.push c) (.base ⟨h.size⟩) = some c :=
  @GoLean.GoCore.Equations.Heap.lookup_push_self

theorem Pin.exec_seqn : ∀ {ctx : ProgramCtx} (s : Store) (ss : Array Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.seqn ss) env k) ch = .ok (.next (seqCont ss.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_seqn

theorem Pin.exec_ifThenElse : ∀ {ctx : ProgramCtx} (s : Store) (c : Expr) (t e : Stmt) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.ifThenElse c t e) env k) ch = .ok (.evalE c env (.ifK t e env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_ifThenElse

theorem Pin.exec_while : ∀ {ctx : ProgramCtx} (s : Store) (c : Expr) (b : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.while c b) env k) ch = .ok (.evalE c env (.whileK c b env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_while

theorem Pin.exec_returnStmt : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec .returnStmt env k) ch = .ok (.signal .ret k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_returnStmt

theorem Pin.exec_breakStmt : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec .breakStmt env k) ch = .ok (.signal .brk k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_breakStmt

theorem Pin.exec_continueStmt : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec .continueStmt env k) ch = .ok (.signal .cont k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_continueStmt

theorem Pin.exec_inertLabel : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.inertLabel name) env k) ch = .ok (.next k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_inertLabel

theorem Pin.exec_labeled : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (b : Stmt) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.labeled name b) env k) ch = .ok (.exec b env (.labelK name k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_labeled

theorem Pin.exec_breakTo : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.breakTo name) env k) ch = .ok (.signal (.brkTo name) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_breakTo

theorem Pin.exec_continueTo : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.continueTo name) env k) ch = .ok (.signal (.contTo name) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_continueTo

theorem Pin.exec_breakable : ∀ {ctx : ProgramCtx} (s : Store) (b : Stmt) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.breakable b) env k) ch = .ok (.exec b env (.breakableK k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_breakable

theorem Pin.exec_unsupported : ∀ {ctx : ProgramCtx} (s : Store) (feature : String) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.unsupported feature) env k) ch = .error (.unsupported feature) :=
  @GoLean.GoCore.Equations.exec_unsupported

theorem Pin.exec_call_args : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {plans : List (TargetShape × List Expr)} {a : Expr} {rest : List Expr} (env : LocalEnv)
    (k : Cont) (ch : Choices) (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = a :: rest),
    stepFn ctx s (.exec (.call targets fid args) env k) ch
      = .ok (.evalE a env (.callArgsK fid plans [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_call_args

theorem Pin.exec_call_nullary : ∀ {ctx : ProgramCtx} {s s' : Store} {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace} (env : LocalEnv)
    (k : Cont) (ch : Choices) (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = [])
    (_he : enterFrame ctx s fid [] = .ok (e, s', tr)),
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .ok (e.callConfig plans env k, s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.exec_call_nullary

theorem Pin.exec_call_nullary_panic : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = [])
    (_he : enterFrame ctx s fid [] = .error (.panic msg)),
    stepFn ctx s (.exec (.call targets fid args) env k) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid [] msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).1)] k, s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid [])
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid []) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.exec_call_nullary_panic

theorem Pin.exec_call_unsupported : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} (env : LocalEnv) (k : Cont) (ch : Choices) (_hp : targetsPlan targets.toList = none),
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .error (.unsupported "unsupported call target assignee") :=
  @GoLean.GoCore.Equations.exec_call_unsupported

theorem Pin.exec_callValue : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {callee : Expr}
    {args : Array Expr} {plans : List (TargetShape × List Expr)} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hp : targetsPlan targets.toList = some plans),
    stepFn ctx s (.exec (.callValue targets callee args) env k) ch
      = .ok (.evalE callee env (.callValCalleeK plans args.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_callValue

theorem Pin.exec_callValue_unsupported : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee}
    {callee : Expr} {args : Array Expr} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hp : targetsPlan targets.toList = none),
    stepFn ctx s (.exec (.callValue targets callee args) env k) ch
      = .error (.unsupported "unsupported value-call target assignee") :=
  @GoLean.GoCore.Equations.exec_callValue_unsupported

theorem Pin.retV_callArgsK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (fid : FuncId)
    (plans : List (TargetShape × List Expr)) (vals : List GoValue) (a : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.callArgsK fid plans vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.callArgsK fid plans (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callArgsK_more

theorem Pin.retV_callArgsK_enter : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {fid : FuncId}
    {plans : List (TargetShape × List Expr)} {vals : List GoValue} {e : Entry} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_he : enterFrame ctx s fid (vals ++ [v]) = .ok (e, s', tr)),
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callArgsK_enter

theorem Pin.retV_callArgsK_enter_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId}
    {plans : List (TargetShape × List Expr)} {vals : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_he : enterFrame ctx s fid (vals ++ [v]) = .error (.panic msg)),
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (vals ++ [v]) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v]))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (vals ++ [v])) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.retV_callArgsK_enter_panic

theorem Pin.retV_callValCalleeK_enter : ∀ {ctx : ProgramCtx} {s s' : Store} {fid : FuncId}
    {captured : List GoValue} {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_he : enterFrame ctx s fid captured = .ok (e, s', tr)),
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_enter

theorem Pin.retV_callValCalleeK_enter_panic : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId}
    {captured : List GoValue} {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_he : enterFrame ctx s fid captured = .error (.panic msg)),
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid captured msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid captured)
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid captured) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_enter_panic

theorem Pin.retV_callValCalleeK_nil : ∀ {ctx : ProgramCtx} (s : Store) (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV .nil (.callValCalleeK plans [] env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_nil

theorem Pin.retV_callValCalleeK_args : ∀ {ctx : ProgramCtx} {s : Store} {cv : GoValue}
    (plans : List (TargetShape × List Expr)) (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hd : deferrableCallee cv = true),
    stepFn ctx s (.retV cv (.callValCalleeK plans (a :: rest) env k')) ch
      = .ok (.evalE a env (.callValArgsK cv plans [] rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_args

theorem Pin.retV_callValArgsK_more : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue)
    (plans : List (TargetShape × List Expr)) (vals : List GoValue) (a : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.callValArgsK cv plans vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.callValArgsK cv plans (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_more

theorem Pin.retV_callValArgsK_enter : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {fid : FuncId}
    {captured vals : List GoValue} {plans : List (TargetShape × List Expr)} {e : Entry} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .ok (e, s', tr)),
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch
      = .ok (e.callConfig plans env k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_enter

theorem Pin.retV_callValArgsK_enter_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId}
    {captured vals : List GoValue} {plans : List (TargetShape × List Expr)} {msg : String} (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .error (.panic msg)),
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (captured ++ vals ++ [v]) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).1)] k', s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v]))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ vals ++ [v])) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_enter_panic

theorem Pin.retV_callValArgsK_nil : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue)
    (plans : List (TargetShape × List Expr)) (vals : List GoValue) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.callValArgsK .nil plans vals [] env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_callValArgsK_nil

theorem Pin.exec_deferCall : ∀ {ctx : ProgramCtx} (s : Store) (callee : Expr) (args : Array Expr)
    (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.deferCall callee args) env k) ch
      = .ok (.evalE callee env (.deferCalleeK args.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_deferCall

theorem Pin.retV_deferCalleeK_args : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (a : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.deferCalleeK (a :: rest) env k')) ch
      = .ok (.evalE a env (.deferArgsK v [] rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_args

theorem Pin.retV_deferCalleeK_push : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {k' k'' : Cont}
    (env : LocalEnv) (ch : Choices) (_hd : deferrableCallee v = true) (_hp : pushDefer (v, []) k' = some k''),
    stepFn ctx s (.retV v (.deferCalleeK [] env k')) ch = .ok (.next k'', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_push

theorem Pin.retV_deferCalleeK_push_frame : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (env : LocalEnv)
    (ch : Choices) (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k'' : Cont) (fr : FuncId) (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.deferCalleeK [] env (.frame t te r ds k'' fr))) ch
      = .ok (.next (.frame t te r ((v, []) :: ds) k'' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_push_frame

theorem Pin.retV_deferCalleeK_outside : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {k' : Cont}
    (env : LocalEnv) (ch : Choices) (_hd : deferrableCallee v = true) (_hp : pushDefer (v, []) k' = none),
    stepFn ctx s (.retV v (.deferCalleeK [] env k')) ch = .error (.stuck "defer outside a call frame") :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_outside

theorem Pin.retV_deferArgsK_more : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue)
    (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.deferArgsK cv vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.deferArgsK cv (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferArgsK_more

theorem Pin.retV_deferArgsK_push : ∀ {ctx : ProgramCtx} {s : Store} {v cv : GoValue} {vals : List GoValue}
    {k' k'' : Cont} (env : LocalEnv) (ch : Choices) (_hp : pushDefer (cv, vals ++ [v]) k' = some k''),
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env k')) ch = .ok (.next k'', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferArgsK_push

theorem Pin.retV_deferArgsK_push_frame : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue)
    (env : LocalEnv) (ch : Choices) (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k'' : Cont) (fr : FuncId),
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env (.frame t te r ds k'' fr))) ch
      = .ok (.next (.frame t te r ((cv, vals ++ [v]) :: ds) k'' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_deferArgsK_push_frame

theorem Pin.retV_deferArgsK_outside : ∀ {ctx : ProgramCtx} {s : Store} {v cv : GoValue} {vals : List GoValue}
    {k' : Cont} (env : LocalEnv) (ch : Choices) (_hp : pushDefer (cv, vals ++ [v]) k' = none),
    stepFn ctx s (.retV v (.deferArgsK cv vals [] env k')) ch = .error (.stuck "defer outside a call frame") :=
  @GoLean.GoCore.Equations.retV_deferArgsK_outside

theorem Pin.exec_panicStmt : ∀ {ctx : ProgramCtx} (s : Store) (e : Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.panicStmt e) env k) ch = .ok (.evalE e env (.panicArgK k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_panicStmt

theorem Pin.retV_panicArgK : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.panicArgK k')) ch
      = .ok (.panicking [panicEntryOf ctx (panicPayload v)] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_panicArgK

theorem Pin.evalE_recoverCall : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE .recoverCall env k) ch
      = .ok (.retV (recoverResult k).1 (recoverResult k).2, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_recoverCall

theorem Pin.panicking_frame_empty : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry)
    (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFn ctx s (.panicking chain (.frame t te r [] k' fr)) ch = .ok (.panicking chain k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_empty

theorem Pin.panicking_frame_defer : ∀ {ctx : ProgramCtx} {s s' : Store} {chain : List PanicEntry} {fid : FuncId}
    {captured args : List GoValue} {e : Entry} {tr : AccessTrace} (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .ok (e, s', tr)),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (e.drainConfig (.panicResumeK chain (.frame t te r ds k' fr))
              (fun cv => .panicking chain (.frame t te r ((cv, []) :: ds) k' fr)), s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer

theorem Pin.panicking_frame_defer_run : ∀ {ctx : ProgramCtx} {s s' : Store} {chain : List PanicEntry}
    {fid : FuncId} {captured args : List GoValue} {func : Func} {fenv : LocalEnv} {rl : List Loc}
    {tr : AccessTrace} (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .ok (.run func fenv rl, s', tr)),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (.exec func.body fenv (.frame [] [] [] [] (.panicResumeK chain (.frame t te r ds k' fr)) func.id),
            s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer_run

theorem Pin.panicking_frame_defer_panic : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry}
    {fid : FuncId} {captured args : List GoValue} {msg : String} (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error (.panic msg)),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch
      = .ok (.panicking (chain ++ [panicEntry (entryPanicText ctx fid (captured ++ args) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1)])
              (.frame t te r ds k' fr), s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer_panic

theorem Pin.panicking_frame_defer_nil : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry)
    (args : List GoValue) (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFn ctx s (.panicking chain (.frame t te r ((.nil, args) :: ds) k' fr)) ch
      = .ok (.panicking (chain ++ [panicEntry nilDerefPanicText]) (.frame t te r ds k' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_frame_defer_nil

theorem Pin.panicking_panicResumeK : ∀ {ctx : ProgramCtx} (s : Store) (chain suspended : List PanicEntry)
    (k' : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.panicResumeK suspended k')) ch
      = .ok (.panicking (suspended ++ chain) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_panicResumeK

theorem Pin.next_panicResumeK_unrecovered : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry}
    (k' : Cont) (ch : Choices) (_h : chainNewestRecovered chain = false),
    stepFn ctx s (.next (.panicResumeK chain k')) ch = .ok (.panicking chain k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_panicResumeK_unrecovered

theorem Pin.next_panicResumeK_recovered : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} (k' : Cont)
    (ch : Choices) (_h : chainNewestRecovered chain = true),
    stepFn ctx s (.next (.panicResumeK chain k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_panicResumeK_recovered

theorem Pin.panicking_glue : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry} {g : Frame} (k : Cont)
    (ch : Choices) (_hg : g.class = .stmtGlue ∨ g.class = .exprGlue),
    stepFn ctx s (.panicking chain (g :: k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_glue

theorem Pin.panicking_seq : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (rest : List Stmt)
    (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.seq rest env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_seq

theorem Pin.panicking_loop : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (c : Expr) (b : Stmt)
    (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.loop c b env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_loop

theorem Pin.panicking_breakableK : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.panicking chain (.breakableK k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_breakableK

theorem Pin.panicking_labelK : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (name : String)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.labelK name k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_labelK

theorem Pin.panicking_strictK : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (op : StrictOp)
    (done : List GoValue) (pending : List Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.strictK op done pending env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_strictK

theorem Pin.panicking_storeK : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry)
    (refs : List TargetRef) (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.storeK refs vals body env k)) ch = .ok (.panicking chain k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.panicking_storeK

theorem Pin.panicking_probeK : ∀ {ctx : ProgramCtx} (s : Store) (chain : List PanicEntry) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.panicking chain (.probeK k')) ch
      = .ok (if (Choices.consumeAtE .unseqPanic 2 ch).1 = 0 then .next k' else .panicking chain k', s,
            (Choices.consumeAtE .unseqPanic 2 ch).2.1, ⟨[], (Choices.consumeAtE .unseqPanic 2 ch).2.2, []⟩) :=
  @GoLean.GoCore.Equations.panicking_probeK

theorem Pin.panicking_stop_settled : ∀ {ctx : ProgramCtx} {s : Store} {first : PanicEntry}
    {rest : List PanicEntry} (ch : Choices) (_hs : splitNewestPending? (first :: rest) = none),
    stepFn ctx s (.panicking (first :: rest) .stop) ch
      = (do let msg ← abortMsg ctx first rest (abortConsult first rest ch).1; throw (.panic msg)) :=
  @GoLean.GoCore.Equations.panicking_stop_settled

theorem Pin.panicking_stop_pending : ∀ {ctx : ProgramCtx} {s : Store} {first : PanicEntry}
    {rest older : List PanicEntry} {entry : PanicEntry} {newer : List PanicEntry} (ch : Choices)
    (_hs : splitNewestPending? (first :: rest) = some (older, entry, newer)),
    stepFn ctx s (.panicking (first :: rest) .stop) ch
      = .ok (if preprintCollide older entry && (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).1 = 0
              then .panicking (preprintDrop older newer) .stop
              else .next (.preprintK older entry newer .stop), s,
            (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).2.1,
            ⟨[], (Choices.consumeAtE .repanicCollapse (preprintWidth older entry) ch).2.2, []⟩) :=
  @GoLean.GoCore.Equations.panicking_stop_pending

theorem Pin.panicking_nil_stop : ∀ {ctx : ProgramCtx} (s : Store) (ch : Choices),
    stepFn ctx s (.panicking [] .stop) ch = .error (.internal "empty panic chain at stop") :=
  @GoLean.GoCore.Equations.panicking_nil_stop

theorem Pin.next_preprintK : ∀ {ctx : ProgramCtx} {s : Store} {older : List PanicEntry} {entry : PanicEntry}
    {newer : List PanicEntry} {fid : FuncId} {recv : GoValue} {tr : AccessTrace} (k' : Cont) (ch : Choices)
    (_h : preprintDispatch ctx s entry = .ok (fid, recv, tr)),
    stepFn ctx s (.next (.preprintK older entry newer k')) ch
      = .ok (.retV (.funcVal fid [recv]) (.callValCalleeK [] [] [] (.preprintK older entry newer k')), s, ch,
            ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.next_preprintK

theorem Pin.next_preprintK_panic : ∀ {ctx : ProgramCtx} {s : Store} {older : List PanicEntry}
    {entry : PanicEntry} {newer : List PanicEntry} {msg : String} (k' : Cont) (ch : Choices)
    (_h : preprintDispatch ctx s entry = .error (.panic msg)),
    stepFn ctx s (.next (.preprintK older entry newer k')) ch
      = .ok (.panicking [panicEntry msg] (.preprintK older entry newer k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_preprintK_panic

theorem Pin.retV_preprintK_string : ∀ {ctx : ProgramCtx} (s : Store) (text : GoString) (older : List PanicEntry)
    (entry : PanicEntry) (newer : List PanicEntry) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV (.string text) (.preprintK older entry newer k')) ch
      = .ok (.panicking (older ++ { entry with rewrite := .done text } :: newer) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_preprintK_string

theorem Pin.panicking_preprintK : ∀ {ctx : ProgramCtx} (s : Store) (chain older : List PanicEntry)
    (entry : PanicEntry) (newer : List PanicEntry) (k' : Cont) (ch : Choices),
    stepFn ctx s (.panicking chain (.preprintK older entry newer k')) ch = .error (preprintFatalStop ctx chain) :=
  @GoLean.GoCore.Equations.panicking_preprintK

theorem Pin.next_frame : ∀ {ctx : ProgramCtx} (s : Store) (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId)
    (ch : Choices),
    stepFn ctx s (.next (.frame targets tenv results ds k' fr)) ch
      = stepFrameExit ctx s targets tenv results ds k' fr ch :=
  @GoLean.GoCore.Equations.next_frame

theorem Pin.signal_ret_frame : ∀ {ctx : ProgramCtx} (s : Store) (targets : List (TargetShape × List Expr))
    (tenv : LocalEnv) (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId)
    (ch : Choices),
    stepFn ctx s (.signal .ret (.frame targets tenv results ds k' fr)) ch
      = stepFrameExit ctx s targets tenv results ds k' fr ch :=
  @GoLean.GoCore.Equations.signal_ret_frame

theorem Pin.frameExit_nil : ∀ {ctx : ProgramCtx} (s : Store) (tenv : LocalEnv) (k' : Cont) (fr : FuncId)
    (ch : Choices),
    stepFrameExit ctx s [] tenv [] [] k' fr ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_nil

theorem Pin.frameExit_targets : ∀ {ctx : ProgramCtx} {s : Store} {results : List Loc} {vs : List GoValue}
    {tr : AccessTrace} (sh : TargetShape) (e : Expr) (ops : List Expr) (rest : List (TargetShape × List Expr))
    (tenv : LocalEnv) (k' : Cont) (fr : FuncId) (ch : Choices) (_hl : loadResults ctx s results = .ok (vs, tr)),
    stepFrameExit ctx s ((sh, e :: ops) :: rest) tenv results [] k' fr ch
      = .ok (.evalE e tenv (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_targets

theorem Pin.frameExit_defer : ∀ {ctx : ProgramCtx} {s s' : Store} {fid : FuncId} {captured args : List GoValue}
    {e : Entry} {tr : AccessTrace} (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .ok (e, s', tr)),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (e.drainConfig (.frame targets tenv results ds k' fr)
              (fun cv => .next (.frame targets tenv results ((cv, []) :: ds) k' fr)), s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer

theorem Pin.frameExit_defer_run : ∀ {ctx : ProgramCtx} {s s' : Store} {fid : FuncId}
    {captured args : List GoValue} {func : Func} {fenv : LocalEnv} {rl : List Loc} {tr : AccessTrace}
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .ok (.run func fenv rl, s', tr)),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (.exec func.body fenv (.frame [] [] [] [] (.frame targets tenv results ds k' fr) func.id), s', ch,
            ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer_run

theorem Pin.frameExit_defer_panic : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId}
    {captured args : List GoValue} {msg : String} (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error (.panic msg)),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch
      = .ok (.panicking [panicEntry (entryPanicText ctx fid (captured ++ args) msg
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1)]
              (.frame targets tenv results ds k' fr), s,
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).2,
            ⟨[], PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args))
              (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid (captured ++ args)) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer_panic

theorem Pin.frameExit_defer_nil : ∀ {ctx : ProgramCtx} (s : Store) (args : List GoValue)
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFrameExit ctx s targets tenv results ((.nil, args) :: ds) k' fr ch
      = .ok (.panicking [panicEntry nilDerefPanicText] (.frame targets tenv results ds k' fr), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_defer_nil

theorem Pin.frameExit_preprint : ∀ {ctx : ProgramCtx} {s : Store} {rl : Loc} {v : GoValue} (tenv : LocalEnv)
    (older : List PanicEntry) (entry : PanicEntry) (newer : List PanicEntry) (k'' : Cont) (fr : FuncId)
    (ch : Choices) (_hl : loadRoot ctx s rl = .ok v),
    stepFrameExit ctx s [] tenv [rl] [] (.preprintK older entry newer k'') fr ch
      = .ok (.retV v (.preprintK older entry newer k''), s, ch, ⟨[.access .read (.data rl.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.frameExit_preprint

theorem Pin.frameExit_extra_results : ∀ {ctx : ProgramCtx} {s : Store} {rl : Loc} {rls : List Loc}
    {vs : List GoValue} {tr : AccessTrace} (tenv : LocalEnv) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_hl : loadResults ctx s (rl :: rls) = .ok (vs, tr))
    (_hk : ∀ older entry newer k'', k' = .preprintK older entry newer k'' → rls ≠ []),
    stepFrameExit ctx s [] tenv (rl :: rls) [] k' fr ch = .error (.stuck "extra GoCore assignment value") :=
  @GoLean.GoCore.Equations.frameExit_extra_results

theorem Pin.frameExit_malformed : ∀ {ctx : ProgramCtx} (s : Store) (sh : TargetShape)
    (rest : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc) (k' : Cont) (fr : FuncId)
    (ch : Choices),
    stepFrameExit ctx s ((sh, []) :: rest) tenv results [] k' fr ch = .error (.internal "malformed call target plan") :=
  @GoLean.GoCore.Equations.frameExit_malformed

theorem Pin.loadResults_nil : ∀ {ctx : ProgramCtx} (s : Store),
    loadResults ctx s [] = .ok ([], []) :=
  @GoLean.GoCore.Equations.loadResults_nil

theorem Pin.loadResults_cons : ∀ {ctx : ProgramCtx} {s : Store} {l : Loc} {ls : List Loc} {v : GoValue}
    {vs : List GoValue} {tr : AccessTrace} (_hl : loadRoot ctx s l = .ok v)
    (_hs : loadResults ctx s ls = .ok (vs, tr)),
    loadResults ctx s (l :: ls) = .ok (v :: vs, [.access .read (.data l.canon)] ++ tr) :=
  @GoLean.GoCore.Equations.loadResults_cons

theorem Pin.signal_table : ∀ {ctx : ProgramCtx} {s : Store} {sg : Signal} {k : Cont} {c' : Config}
    (ch : Choices) (_h : signalStep sg k = some c'),
    stepFn ctx s (.signal sg k) ch = .ok (c', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.signal_table

theorem Pin.signal_stop : ∀ {ctx : ProgramCtx} (s : Store) (sg : Signal) (ch : Choices),
    stepFn ctx s (.signal sg .stop) ch = .error (signalRefusal sg .stop) :=
  @GoLean.GoCore.Equations.signal_stop

theorem Pin.signal_frame_escape : ∀ {ctx : ProgramCtx} {s : Store} {sg : Signal}
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices) (_hsg : sg ≠ .ret),
    stepFn ctx s (.signal sg (.frame targets tenv results ds k' fr)) ch
      = .error (signalRefusal sg (.frame targets tenv results ds k' fr)) :=
  @GoLean.GoCore.Equations.signal_frame_escape

theorem Pin.signalStep_seq : ∀ (sg : Signal) (rest : List Stmt) (env : LocalEnv) (k' : Cont),
    signalStep sg (.seq rest env k') = some (.signal sg k') :=
  @GoLean.GoCore.Equations.signalStep_seq

theorem Pin.signalStep_breakableK_brk : ∀ (k' : Cont),
    signalStep .brk (.breakableK k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_brk

theorem Pin.signalStep_breakableK_ret : ∀ (k' : Cont),
    signalStep .ret (.breakableK k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_ret

theorem Pin.signalStep_breakableK_cont : ∀ (k' : Cont),
    signalStep .cont (.breakableK k') = some (.signal .cont k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_cont

theorem Pin.signalStep_loop_brk : ∀ (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep .brk (.loop c b env k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_loop_brk

theorem Pin.signalStep_loop_cont : ∀ (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep .cont (.loop c b env k') = some (.exec (.while c b) env k') :=
  @GoLean.GoCore.Equations.signalStep_loop_cont

theorem Pin.signalStep_loop_ret : ∀ (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep .ret (.loop c b env k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_loop_ret

theorem Pin.signalStep_labelK_ret : ∀ (name : String) (k' : Cont),
    signalStep .ret (.labelK name k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_ret

theorem Pin.signalStep_labelK_brkTo_self : ∀ (name : String) (k' : Cont),
    signalStep (.brkTo name) (.labelK name k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_brkTo_self

theorem Pin.next_stop : ∀ {ctx : ProgramCtx} (s : Store) (ch : Choices),
    stepFn ctx s (.next .stop) ch = .error (.internal "step on terminal configuration") :=
  @GoLean.GoCore.Equations.next_stop

theorem Pin.next_seq_cons : ∀ {ctx : ProgramCtx} (s : Store) (t : Stmt) (rest : List Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.seq (t :: rest) env k')) ch = .ok (.exec t env (.seq rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_seq_cons

theorem Pin.next_seq_nil : ∀ {ctx : ProgramCtx} (s : Store) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.seq [] env k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_seq_nil

theorem Pin.next_loop : ∀ {ctx : ProgramCtx} (s : Store) (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.next (.loop c b env k')) ch = .ok (.exec (.while c b) env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_loop

theorem Pin.next_breakableK : ∀ {ctx : ProgramCtx} (s : Store) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.breakableK k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_breakableK

theorem Pin.next_labelK : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.labelK name k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_labelK

theorem Pin.next_strictK : ∀ {ctx : ProgramCtx} (s : Store) (op : StrictOp) (done : List GoValue)
    (pending : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.strictK op done pending env k')) ch
      = .error (.internal "completion delivered to expression continuation") :=
  @GoLean.GoCore.Equations.next_strictK

theorem Pin.next_ifK : ∀ {ctx : ProgramCtx} (s : Store) (t e : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.ifK t e env k')) ch = .error (.internal "completion delivered to expression continuation") :=
  @GoLean.GoCore.Equations.next_ifK

theorem Pin.next_callArgsK : ∀ {ctx : ProgramCtx} (s : Store) (fid : FuncId)
    (plans : List (TargetShape × List Expr)) (vals : List GoValue) (pending : List Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.callArgsK fid plans vals pending env k')) ch
      = .error (.internal "completion delivered to expression continuation") :=
  @GoLean.GoCore.Equations.next_callArgsK

theorem Pin.retV_seq : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (rest : List Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.seq rest env k')) ch = .error (.internal "value delivered to statement continuation") :=
  @GoLean.GoCore.Equations.retV_seq

theorem Pin.retV_frame : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue)
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices),
    stepFn ctx s (.retV v (.frame targets tenv results ds k' fr)) ch
      = .error (.internal "value delivered to statement continuation") :=
  @GoLean.GoCore.Equations.retV_frame

theorem Pin.retV_storeK : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (refs : List TargetRef)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.storeK refs vals body env k')) ch
      = .error (.internal "value delivered to statement continuation") :=
  @GoLean.GoCore.Equations.retV_storeK

theorem Pin.retV_stop : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (ch : Choices),
    stepFn ctx s (.retV v .stop) ch = .error (.internal "value delivered to empty continuation") :=
  @GoLean.GoCore.Equations.retV_stop

theorem Pin.evalE_var : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} {loc : Loc} {v : GoValue} (env : LocalEnv)
    (k : Cont) (ch : Choices) (_hl : LocalEnv.lookup env id = some loc) (_hv : loadRoot ctx s loc = .ok v),
    stepFn ctx s (.evalE (.var id) env k) ch
      = .ok (.retV v k, s, ch, ⟨[.access .read (.data (projChainTarget ctx s k loc).canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_var

theorem Pin.evalE_var_unbound : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hl : LocalEnv.lookup env id = none),
    stepFn ctx s (.evalE (.var id) env k) ch = .error (.stuck s!"unbound GoCore variable address: {id}") :=
  @GoLean.GoCore.Equations.evalE_var_unbound

theorem Pin.evalE_ref : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} {loc : Loc} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hl : LocalEnv.lookup env id = some loc),
    stepFn ctx s (.evalE (.ref id) env k) ch = .ok (.retV (.addr loc) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_ref

theorem Pin.evalE_ref_unbound : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hl : LocalEnv.lookup env id = none),
    stepFn ctx s (.evalE (.ref id) env k) ch = .error (.stuck s!"unbound GoCore variable address: {id}") :=
  @GoLean.GoCore.Equations.evalE_ref_unbound

theorem Pin.evalE_global : ∀ {ctx : ProgramCtx} {s : Store} {gid : Nat} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_h : gid < s.heap.size),
    stepFn ctx s (.evalE (.global gid) env k) ch = .ok (.retV (.addr (.base ⟨gid⟩)) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_global

theorem Pin.evalE_global_oob : ∀ {ctx : ProgramCtx} {s : Store} {gid : Nat} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_h : ¬ gid < s.heap.size),
    stepFn ctx s (.evalE (.global gid) env k) ch
      = .error (.stuck s!"global {gid} out of range: the heap has {s.heap.size} cell(s)") :=
  @GoLean.GoCore.Equations.evalE_global_oob

theorem Pin.exec_assign : ∀ {ctx : ProgramCtx} {s : Store} {lhs : Assignee} {sh : TargetShape} {e : Expr}
    {ops : List Expr} (rhs : Expr) (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : targetPlan lhs = some (sh, e :: ops)),
    stepFn ctx s (.exec (.assign lhs rhs) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_assign

theorem Pin.exec_assign_var : ∀ {ctx : ProgramCtx} (s : Store) (id : VarId) (rhs : Expr) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.assign (.var id) rhs) env k) ch
      = .ok (.evalE (.ref id) env (.tgtOpK (.chain []) [] [] [] [] .vals [rhs] [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_assign_var

theorem Pin.exec_assign_unsupported : ∀ {ctx : ProgramCtx} (s : Store) (feature : String) (rhs : Expr)
    (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.assign (.unsupported feature) rhs) env k) ch = .error (.unsupported feature) :=
  @GoLean.GoCore.Equations.exec_assign_unsupported

theorem Pin.retV_tgtOpK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (sh : TargetShape)
    (ops : List GoValue) (e : Expr) (rest : List Expr) (refs : List TargetRef)
    (targets : List (TargetShape × List Expr)) (rop : RhsOp) (rhs : List Expr) (vals : List GoValue)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.tgtOpK sh ops (e :: rest) refs targets rop rhs vals body env k')) ch
      = .ok (.evalE e env (.tgtOpK sh (v :: ops) rest refs targets rop rhs vals body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_more

theorem Pin.retV_tgtOpK_next_target : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape}
    {ops : List GoValue} {r : TargetRef} (refs : List TargetRef) (sh' : TargetShape) (e : Expr)
    (ops' : List Expr) (rest : List (TargetShape × List Expr)) (rop : RhsOp) (rhs : List Expr)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hc : completeTargetRef sh (v :: ops).reverse = some r),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs ((sh', e :: ops') :: rest) rop rhs vals body env k')) ch
      = .ok (.evalE e env (.tgtOpK sh' [] ops' (refs ++ [r]) rest rop rhs vals body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_next_target

theorem Pin.retV_tgtOpK_rhs : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape}
    {ops : List GoValue} {r : TargetRef} (refs : List TargetRef) (rop : RhsOp) (e : Expr) (rest : List Expr)
    (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hc : completeTargetRef sh (v :: ops).reverse = some r),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs [] rop (e :: rest) vals body env k')) ch
      = .ok (.evalE e env (.rhsK rop (refs ++ [r]) [] rest body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_rhs

theorem Pin.retV_tgtOpK_store : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape}
    {ops : List GoValue} {r : TargetRef} (refs : List TargetRef) (rop : RhsOp) (vals : List GoValue)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hc : completeTargetRef sh (v :: ops).reverse = some r),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs [] rop [] vals body env k')) ch
      = .ok (.next (.storeK (refs ++ [r]) vals body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_tgtOpK_store

theorem Pin.retV_tgtOpK_malformed : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {sh : TargetShape}
    {ops : List GoValue} (refs : List TargetRef) (targets : List (TargetShape × List Expr)) (rop : RhsOp)
    (rhs : List Expr) (vals : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hc : completeTargetRef sh (v :: ops).reverse = none),
    stepFn ctx s (.retV v (.tgtOpK sh ops [] refs targets rop rhs vals body env k')) ch
      = .error (.internal "malformed receive target operands") :=
  @GoLean.GoCore.Equations.retV_tgtOpK_malformed

theorem Pin.retV_rhsK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (rop : RhsOp)
    (refs : List TargetRef) (done : List GoValue) (e : Expr) (rest : List Expr) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.rhsK rop refs done (e :: rest) body env k')) ch
      = .ok (.evalE e env (.rhsK rop refs (v :: done) rest body env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_rhsK_more

theorem Pin.retV_rhsK_apply : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {rop : RhsOp}
    {done vals : List GoValue} {tr : AccessTrace} (refs : List TargetRef) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_h : applyRhsOp ctx s rop (v :: done).reverse = .ok (vals, tr)),
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch
      = .ok (.next (.storeK refs vals body env k'), s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_rhsK_apply

theorem Pin.retV_rhsK_apply_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {rop : RhsOp}
    {done : List GoValue} {msg : String} (refs : List TargetRef) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_h : applyRhsOp ctx s rop (v :: done).reverse = .error (.panic msg)),
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_rhsK_apply_panic

theorem Pin.next_storeK_store : ∀ {ctx : ProgramCtx} {s s' : Store} {ref : TargetRef} {val : GoValue}
    {tr : AccessTrace} (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_h : storeTarget ctx s ref val = .ok (s', tr)),
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_store

theorem Pin.next_storeK_chain : ∀ {ctx : ProgramCtx} {s s' : Store} {anchor : GoValue} {idxs : List GoValue}
    {steps : List TargetStep} {val av : GoValue} {loc : Loc} (rs : List TargetRef) (vrest : List GoValue)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hres : resolveChain ctx s anchor steps idxs = .ok av) (_hloc : valueAsLoc av = .ok loc)
    (_hst : storeLoc ctx s loc val = .ok s'),
    stepFn ctx s (.next (.storeK (.chain anchor idxs steps :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_chain

theorem Pin.next_storeK_var : ∀ {ctx : ProgramCtx} {s s' : Store} {loc : Loc} {val : GoValue}
    (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hst : storeLoc ctx s loc val = .ok s'),
    stepFn ctx s (.next (.storeK (.chain (.addr loc) [] [] :: rs) (val :: vrest) body env k')) ch
      = .ok (.next (.storeK rs vrest body env k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_var

theorem Pin.next_storeK_panic : ∀ {ctx : ProgramCtx} {s : Store} {ref : TargetRef} {val : GoValue}
    {msg : String} (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_h : storeTarget ctx s ref val = .error (.panic msg)),
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_panic

theorem Pin.next_storeK_done : ∀ {ctx : ProgramCtx} (s : Store) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.next (.storeK [] [] body env k')) ch = .ok (.exec body env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.next_storeK_done

theorem Pin.exec_block : ∀ {ctx : ProgramCtx} {s s' : Store} {decls : Array Param} {env env' : LocalEnv}
    (ss : Array Stmt) (k : Cont) (ch : Choices)
    (_h : allocDecls ctx env.pushScope s decls.toList = .ok (env', s')),
    stepFn ctx s (.exec (.block decls ss) env k) ch = .ok (.next (.seq ss.toList env' k), s', ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_block

theorem Pin.allocDecls_nil : ∀ {ctx : ProgramCtx} (env : LocalEnv) (s : Store),
    allocDecls ctx env s [] = .ok (env, s) :=
  @GoLean.GoCore.Equations.allocDecls_nil

theorem Pin.allocDecls_cons : ∀ {ctx : ProgramCtx} {env : LocalEnv} {s s₁ : Store} {p : Param} {v : GoValue}
    {loc : Loc} (rest : List Param) (_hd : defaultValue ctx p.typ = .ok v)
    (_ha : Store.alloc ctx s v p.typ = .ok (loc, s₁)),
    allocDecls ctx env s (p :: rest) = allocDecls ctx (env.declare p.id loc) s₁ rest :=
  @GoLean.GoCore.Equations.allocDecls_cons

theorem Pin.bindParams_nil : ∀ {ctx : ProgramCtx} (env : LocalEnv) (s : Store),
    bindParams ctx env s [] [] = .ok (env, s) :=
  @GoLean.GoCore.Equations.bindParams_nil

theorem Pin.bindParams_cons : ∀ {ctx : ProgramCtx} {env : LocalEnv} {s s₁ : Store} {p : Param} {v v' : GoValue}
    {loc : Loc} (ps : List Param) (vs : List GoValue) (_hn : normalizeValueForTy ctx p.typ v = .ok v')
    (_ha : Store.alloc ctx s v' p.typ = .ok (loc, s₁)),
    bindParams ctx env s (p :: ps) (v :: vs) = bindParams ctx (env.declare p.id loc) s₁ ps vs :=
  @GoLean.GoCore.Equations.bindParams_cons

theorem Pin.retV_ifK_true : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (t e : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.ifK t e env k')) ch = .ok (.exec t env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_ifK_true

theorem Pin.retV_ifK_false : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (t e : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.ifK t e env k')) ch = .ok (.exec e env k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_ifK_false

theorem Pin.retV_whileK_true : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (c : Expr) (b : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .ok (.exec b env (.loop c b env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_whileK_true

theorem Pin.retV_whileK_false : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (c : Expr) (b : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_whileK_false

theorem Pin.evalE_and : ∀ {ctx : ProgramCtx} (s : Store) (l r : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.and l r) env k) ch = .ok (.evalE l env (.andK r env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_and

theorem Pin.evalE_or : ∀ {ctx : ProgramCtx} (s : Store) (l r : Expr) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.or l r) env k) ch = .ok (.evalE l env (.orK r env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_or

theorem Pin.retV_andK_true : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.andK r env k')) ch = .ok (.evalE r env (.boolK k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_andK_true

theorem Pin.retV_andK_false : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.andK r env k')) ch = .ok (.retV (.bool false) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_andK_false

theorem Pin.retV_orK_true : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok true),
    stepFn ctx s (.retV v (.orK r env k')) ch = .ok (.retV (.bool true) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_orK_true

theorem Pin.retV_orK_false : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (r : Expr) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .ok false),
    stepFn ctx s (.retV v (.orK r env k')) ch = .ok (.evalE r env (.boolK k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_orK_false

theorem Pin.retV_boolK : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {b : Bool} (k' : Cont) (ch : Choices)
    (_hv : valueAsBool v = .ok b),
    stepFn ctx s (.retV v (.boolK k')) ch = .ok (.retV (.bool b) k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_boolK

theorem Pin.evalE_intLit : ∀ {ctx : ProgramCtx} (s : Store) (value : Int) (kind : IntKind) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.evalE (.intLit value kind) env k) ch = .ok (.retV (.int (kind.normalize value) kind) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_intLit

theorem Pin.evalE_boolLit : ∀ {ctx : ProgramCtx} (s : Store) (value : Bool) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.evalE (.boolLit value) env k) ch = .ok (.retV (.bool value) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_boolLit

theorem Pin.evalE_stringLit : ∀ {ctx : ProgramCtx} (s : Store) (value : GoString) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.evalE (.stringLit value) env k) ch = .ok (.retV (.string value) k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_stringLit

theorem Pin.evalE_unsupported : ∀ {ctx : ProgramCtx} (s : Store) (feature : String) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.evalE (.unsupported feature) env k) ch = .error (.unsupported feature) :=
  @GoLean.GoCore.Equations.evalE_unsupported

theorem Pin.evalE_strict_more : ∀ {ctx : ProgramCtx} {s : Store} {e e₁ : Expr} {op : StrictOp}
    {rest : List Expr} (env : LocalEnv) (k : Cont) (ch : Choices) (_h : strictPlan e = some (op, e₁ :: rest)),
    stepFn ctx s (.evalE e env k) ch = .ok (.evalE e₁ env (.strictK op [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_strict_more

theorem Pin.evalE_strict_nullary : ∀ {ctx : ProgramCtx} {s s' : Store} {e : Expr} {op : StrictOp} {v : GoValue}
    {tr : AccessTrace} (env : LocalEnv) (k : Cont) (ch : Choices) (_h : strictPlan e = some (op, []))
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k) op [] = .ok (v, s', tr)),
    stepFn ctx s (.evalE e env k) ch = .ok (.retV v k, s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.evalE_strict_nullary

theorem Pin.retV_strictK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : StrictOp)
    (done : List GoValue) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.strictK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.strictK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_more

theorem Pin.retV_strictK_apply : ∀ {ctx : ProgramCtx} {s s' : Store} {v out : GoValue} {op : StrictOp}
    {done : List GoValue} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices) (_hk : op.convKind? = none)
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .ok (out, s', tr)),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .ok (.retV out k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_apply

theorem Pin.retV_strictK_apply_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StrictOp}
    {done : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices) (_hk : op.convKind? = none)
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .error (.panic msg)),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_apply_panic

theorem Pin.retV_strictK_apply_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StrictOp}
    {done : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices) (_hk : op.convKind? = none)
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k') op (v :: done).reverse = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_strictK_apply_error

theorem Pin.retV_strictK_conv : ∀ {ctx : ProgramCtx} {s s' : Store} {v out : GoValue} {op : StrictOp}
    {done : List GoValue} {kind : ConvKind} {literal : Bool} {value : GoString} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hk : op.convKind? = some (kind, literal)) (_hv : convOperand? (v :: done).reverse = some value)
    (_ha : convCapApplyAt ctx s kind literal value
      (Choices.consumeAt .convCap (convCapWidth kind literal value) ch).1 = .ok (out, s', tr)),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch
      = .ok (.retV out k', s', (Choices.consumeAt .convCap (convCapWidth kind literal value) ch).2,
          ⟨tr, PickRecord.ofPick .convCap (convCapWidth kind literal value)
            (Choices.consumeAt .convCap (convCapWidth kind literal value) ch).1, []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_conv

theorem Pin.retV_strictK_conv_nopop : ∀ {ctx : ProgramCtx} {s s' : Store} {v out : GoValue} {op : StrictOp}
    {done : List GoValue} {kind : ConvKind} {literal : Bool} {value : GoString} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hk : op.convKind? = some (kind, literal)) (_hv : convOperand? (v :: done).reverse = some value)
    (_hw : convCapWidth kind literal value ≤ 1)
    (_ha : convCapApplyAt ctx s kind literal value 0 = .ok (out, s', tr)),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .ok (.retV out k', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_strictK_conv_nopop

theorem Pin.retV_strictK_conv_refuse : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StrictOp}
    {done : List GoValue} {kind : ConvKind} {literal : Bool} {e : Stop}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hk : op.convKind? = some (kind, literal)) (_hv : convOperand? (v :: done).reverse = none)
    (_hr : convRefuse kind (v :: done).reverse = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.strictK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_strictK_conv_refuse

theorem Pin.exec_wide : ∀ {ctx : ProgramCtx} {s : Store} {stmt : Stmt} {op : StmtOp} {nt : Nat} {e : Expr}
    {rest : List Expr} (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : stmtPlan stmt = some (op, nt, e :: rest)),
    stepFn ctx s (.exec stmt env k) ch = .ok (.evalE e env (.stmtOpK op nt [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_wide

theorem Pin.exec_allocNew : ∀ {ctx : ProgramCtx} {s : Store} {target : Assignee} {te : Expr} (value : Expr)
    (typ : Ty) (env : LocalEnv) (k : Cont) (ch : Choices) (_ht : assigneeExpr target = some te),
    stepFn ctx s (.exec (.allocNew target value typ) env k) ch
      = .ok (.evalE te env (.stmtOpK (.allocNew typ) 1 [] [value] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_allocNew

theorem Pin.exec_mapAssign : ∀ {ctx : ProgramCtx} (s : Store) (base index value : Expr) (keyTy valueTy : Ty)
    (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.mapAssign base index value keyTy valueTy) env k) ch
      = .ok (.evalE base env (.stmtOpK (.mapAssign keyTy valueTy) 0 [] [index, value] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_mapAssign

theorem Pin.exec_appendSlice : ∀ {ctx : ProgramCtx} {s : Store} {target : Assignee} {te : Expr} (elem : Ty)
    (slice elems : Expr) (env : LocalEnv) (k : Cont) (ch : Choices) (_ht : assigneeExpr target = some te),
    stepFn ctx s (.exec (.appendSlice target elem slice elems) env k) ch
      = .ok (.evalE te env (.stmtOpK (.appendSlice elem) 1 [] [slice, elems] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_appendSlice

theorem Pin.exec_print : ∀ {ctx : ProgramCtx} {s : Store} {args : Array Expr} {e : Expr} {rest : List Expr}
    (newline : Bool) (env : LocalEnv) (k : Cont) (ch : Choices) (_hargs : args.toList = e :: rest),
    stepFn ctx s (.exec (.print newline args) env k) ch
      = .ok (.evalE e env (.stmtOpK (.print newline) 0 [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_print

theorem Pin.retV_stmtOpK_more_target : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {loc : Loc} {nt : Nat}
    {done : List GoValue} (op : StmtOp) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hlt : done.length < nt) (_hloc : valueAsLoc v = .ok loc),
    stepFn ctx s (.retV v (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_more_target

theorem Pin.retV_stmtOpK_more_target_nil : ∀ {ctx : ProgramCtx} {s : Store} {nt : Nat} {done : List GoValue}
    (op : StmtOp) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_hlt : done.length < nt),
    stepFn ctx s (.retV .nil (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.panicking [panicEntry nilDerefPanicText] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_more_target_nil

theorem Pin.retV_stmtOpK_more_operand : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {nt : Nat}
    {done : List GoValue} (op : StmtOp) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hge : ¬ done.length < nt),
    stepFn ctx s (.retV v (.stmtOpK op nt done (e :: rest) env k')) ch
      = .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_more_operand

theorem Pin.retV_stmtOpK_apply : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : StmtOp} {nt : Nat}
    {done : List GoValue} {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_h : applyStmtOp ctx s ch op nt (v :: done).reverse = .ok (s', ch', ps, tr)),
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch
      = .ok (.next k', s', ch', ⟨tr, ps, stmtOpOut op (v :: done).reverse⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_apply

theorem Pin.retV_stmtOpK_apply_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StmtOp} {nt : Nat}
    {done : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyStmtOp ctx s ch op nt (v :: done).reverse = .error (.panic msg)),
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_stmtOpK_apply_panic

theorem Pin.exec_mapRange : ∀ {ctx : ProgramCtx} (s : Store) (keyVar valVar : Option VarId) (mapExpr : Expr)
    (keyTy valTy : Ty) (body : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k) ch
      = .ok (.evalE mapExpr env (.mapRangeK keyVar valVar keyTy valTy body env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_mapRange

theorem Pin.retV_mapRangeK : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {base : Option Loc}
    {start : Array Nat} {tr : AccessTrace} (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_h : mapRangeStartSets s v = .ok (base, start, tr)),
    stepFn ctx s (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k')) ch
      = .ok (.next (.mapIterK keyVar valVar keyTy valTy body base #[] start env k'), s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_mapRangeK

theorem Pin.next_mapIterK_done : ∀ {ctx : ProgramCtx} {s : Store} {keyTy valTy : Ty} {base : Option Loc}
    {produced : Array Nat} {tr : AccessTrace} (keyVar valVar : Option VarId) (body : Stmt) (start : Array Nat)
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : mapIterCandidates ctx s keyTy valTy base produced = .ok (#[], tr)),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.next k', s, ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.next_mapIterK_done

theorem Pin.next_mapIterK_pick : ∀ {ctx : ProgramCtx} {s s' : Store} {keyTy valTy : Ty} {base : Option Loc}
    {produced start : Array Nat} {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace} {width idx : Nat}
    {ch' : Choices} {ps : List PickRecord} {id : Nat} {key value : GoValue} {env env' : LocalEnv}
    (keyVar valVar : Option VarId) (body : Stmt) (k' : Cont) (ch : Choices)
    (_h : mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr)) (_hne : cands.isEmpty = false)
    (_hw : width = cands.size + (if mapIterMandatoryRemains cands start then 0 else 1))
    (_hc : Choices.consumeAtE .mapIter width ch = (idx, ch', ps)) (_hget : cands[idx]? = some (id, key, value))
    (_hb : bindIterVars ctx env.pushScope s keyVar valVar keyTy valTy key value = .ok (env', s')),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.exec body env' (.mapIterK keyVar valVar keyTy valTy body base (produced.push id) start env k'), s', ch',
            ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.next_mapIterK_pick

theorem Pin.next_mapIterK_stop : ∀ {ctx : ProgramCtx} {s : Store} {keyTy valTy : Ty} {base : Option Loc}
    {produced start : Array Nat} {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace} {width idx : Nat}
    {ch' : Choices} {ps : List PickRecord} (keyVar valVar : Option VarId) (body : Stmt) (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_h : mapIterCandidates ctx s keyTy valTy base produced = .ok (cands, tr))
    (_hne : cands.isEmpty = false)
    (_hw : width = cands.size + (if mapIterMandatoryRemains cands start then 0 else 1))
    (_hc : Choices.consumeAtE .mapIter width ch = (idx, ch', ps)) (_hget : cands[idx]? = none),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch
      = .ok (.next k', s, ch', ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.next_mapIterK_stop

theorem Pin.exec_mapLookup : ∀ {ctx : ProgramCtx} {s : Store} {t okT : Assignee} {sh : TargetShape} {e : Expr}
    {ops : List Expr} {rest : List (TargetShape × List Expr)} (base index : Expr) (keyTy valueTy : Ty)
    (env : LocalEnv) (k : Cont) (ch : Choices) (_h : targetsPlan [t, okT] = some ((sh, e :: ops) :: rest)),
    stepFn ctx s (.exec (.mapLookup t okT base index keyTy valueTy) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy) [base, index] [] (.seqn #[]) env k), s, ch,
            ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_mapLookup

theorem Pin.exec_typeAssert : ∀ {ctx : ProgramCtx} {s : Store} {t okT : Assignee} {sh : TargetShape} {e : Expr}
    {ops : List Expr} {rest : List (TargetShape × List Expr)} (expr : Expr) (targetTy : Ty) (env : LocalEnv)
    (k : Cont) (ch : Choices) (_h : targetsPlan [t, okT] = some ((sh, e :: ops) :: rest)),
    stepFn ctx s (.exec (.typeAssert t okT expr targetTy) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest (.typeAssert targetTy) [expr] [] (.seqn #[]) env k), s, ch,
            ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_typeAssert

theorem Pin.exec_assignMany : ∀ {ctx : ProgramCtx} {s : Store} {left : Array Assignee} {right : Array Expr}
    {sh : TargetShape} {e : Expr} {ops : List Expr} {rest : List (TargetShape × List Expr)} (env : LocalEnv)
    (k : Cont) (ch : Choices) (_hsz : left.size = right.size)
    (_h : targetsPlan left.toList = some ((sh, e :: ops) :: rest)),
    stepFn ctx s (.exec (.assignMany left right) env k) ch
      = .ok (.evalE e env (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_assignMany

theorem Pin.exec_assignMany_arity : ∀ {ctx : ProgramCtx} {s : Store} {left : Array Assignee}
    {right : Array Expr} (env : LocalEnv) (k : Cont) (ch : Choices) (_hsz : left.size ≠ right.size),
    stepFn ctx s (.exec (.assignMany left right) env k) ch
      = .error (.stuck s!"multi-assignment expected {left.size} value(s), got {right.size}") :=
  @GoLean.GoCore.Equations.exec_assignMany_arity

theorem Pin.exec_chanSend : ∀ {ctx : ProgramCtx} (s : Store) (chE value : Expr) (elem : Ty) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.chanSend chE value elem) env k) ch
      = .ok (.evalE chE env (.chanStK (.send elem) [] [value] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_chanSend

theorem Pin.exec_closeChan : ∀ {ctx : ProgramCtx} (s : Store) (chE : Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.closeChan chE) env k) ch = .ok (.evalE chE env (.chanStK .close [] [] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_closeChan

theorem Pin.exec_chanRecv : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee}
    {plans : List (TargetShape × List Expr)} (chE : Expr) (elem : Ty) (env : LocalEnv) (k : Cont) (ch : Choices)
    (_hsz : ¬ targets.size > 2) (_hp : targetsPlan targets.toList = some plans),
    stepFn ctx s (.exec (.chanRecv targets chE elem) env k) ch
      = .ok (.evalE chE env (.chanStK (.recv targets.toList elem) [] [] env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_chanRecv

theorem Pin.retV_chanStK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : ChanStOp)
    (done : List GoValue) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.chanStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.chanStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_chanStK_more

theorem Pin.retV_chanStK_apply : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : ChanStOp}
    {done : List GoValue} {c' : Config} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyChanOp ctx s op (v :: done).reverse env k' = .ok (c', s', tr)),
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .ok (c', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_chanStK_apply

theorem Pin.retV_chanStK_apply_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : ChanStOp}
    {done : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyChanOp ctx s op (v :: done).reverse env k' = .error (.panic msg)),
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_chanStK_apply_panic

theorem Pin.exec_selectStmt : ∀ {ctx : ProgramCtx} {s : Store} {clauses : Array (SelectClauseHead × Stmt)}
    {e : Expr} {rest : List Expr} (default? : Option Stmt) (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : selectOperands clauses.toList = e :: rest),
    stepFn ctx s (.exec (.selectStmt clauses default?) env k) ch
      = .ok (.evalE e env (.selectOpsK clauses.toList default? [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_selectStmt

theorem Pin.exec_selectStmt_default : ∀ {ctx : ProgramCtx} {s : Store}
    {clauses : Array (SelectClauseHead × Stmt)} (d : Stmt) (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : selectOperands clauses.toList = []),
    stepFn ctx s (.exec (.selectStmt clauses (some d)) env k) ch = .ok (.exec d env k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_selectStmt_default

theorem Pin.exec_selectStmt_block : ∀ {ctx : ProgramCtx} {s : Store} {clauses : Array (SelectClauseHead × Stmt)}
    (env : LocalEnv) (k : Cont) (ch : Choices) (_h : selectOperands clauses.toList = []),
    stepFn ctx s (.exec (.selectStmt clauses none) env k) ch = .ok (.blockedSelect [] env k, s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_selectStmt_block

theorem Pin.retV_selectOpsK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue)
    (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt) (done : List GoValue) (e : Expr)
    (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done (e :: rest) env k')) ch
      = .ok (.evalE e env (.selectOpsK clauses default? (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_selectOpsK_more

theorem Pin.retV_selectOpsK_apply : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt} {done : List GoValue} {c' : Config}
    {ch' : Choices} {ps : List PickRecord} {cl? : Option EvClause} {tr : AccessTrace} (env : LocalEnv)
    (k' : Cont) (ch : Choices)
    (_h : applySelect ctx s clauses default? (v :: done).reverse env k' ch = .ok (c', s', ch', ps, cl?, tr)),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done [] env k')) ch = .ok (c', s', ch', ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.retV_selectOpsK_apply

theorem Pin.exec_goStmt : ∀ {ctx : ProgramCtx} (s : Store) (callee : Expr) (args : Array Expr) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.goStmt callee args) env k) ch
      = .ok (.evalE callee env (.goCalleeK args.toList env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_goStmt

theorem Pin.retV_goCalleeK_args : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (a : Expr) (rest : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.goCalleeK (a :: rest) env k')) ch
      = .ok (.evalE a env (.goArgsK v [] rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_goCalleeK_args

theorem Pin.retV_goCalleeK_spawn : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hd : deferrableCallee v = true),
    stepFn ctx s (.retV v (.goCalleeK [] env k')) ch
      = .error (.unsupported
          "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)") :=
  @GoLean.GoCore.Equations.retV_goCalleeK_spawn

theorem Pin.retV_goArgsK_more : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue)
    (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.goArgsK cv vals (a :: rest) env k')) ch
      = .ok (.evalE a env (.goArgsK cv (vals ++ [v]) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_goArgsK_more

theorem Pin.retV_goArgsK_spawn : ∀ {ctx : ProgramCtx} (s : Store) (v cv : GoValue) (vals : List GoValue)
    (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.goArgsK cv vals [] env k')) ch
      = .error (.unsupported
          "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)") :=
  @GoLean.GoCore.Equations.retV_goArgsK_spawn

theorem Pin.exec_syncStmt : ∀ {ctx : ProgramCtx} {s : Store} {op : SyncStmtOp} {args : Array Expr}
    {targets : Array Assignee} {sop : SyncOp} {e : Expr} {rest : List Expr} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_h : syncPlan (.syncStmt op args targets) = some (sop, e :: rest)),
    stepFn ctx s (.exec (.syncStmt op args targets) env k) ch
      = .ok (.evalE e env (.syncStK sop [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_syncStmt

theorem Pin.exec_atomicStmt : ∀ {ctx : ProgramCtx} {s : Store} {op : AtomicStmtOp} {kind : IntKind}
    {args : Array Expr} {targets : Array Assignee} {aop : AtomicOp} {e : Expr} {rest : List Expr}
    (env : LocalEnv) (k : Cont) (ch : Choices)
    (_h : atomicPlan (.atomicStmt op kind args targets) = some (aop, e :: rest)),
    stepFn ctx s (.exec (.atomicStmt op kind args targets) env k) ch
      = .ok (.evalE e env (.atomicStK aop [] rest env k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_atomicStmt

theorem Pin.retV_syncStK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : SyncOp)
    (done : List GoValue) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.syncStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.syncStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_syncStK_more

theorem Pin.retV_syncStK_apply : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : SyncOp}
    {done : List GoValue} {c' : Config} {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySyncOp ctx s ch op (v :: done).reverse env k' = .ok (c', s', ch', ps, tr)),
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .ok (c', s', ch', ⟨tr, ps, []⟩) :=
  @GoLean.GoCore.Equations.retV_syncStK_apply

theorem Pin.retV_syncStK_apply_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : SyncOp}
    {done : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySyncOp ctx s ch op (v :: done).reverse env k' = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_syncStK_apply_error

theorem Pin.retV_atomicStK_more : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (op : AtomicOp)
    (done : List GoValue) (e : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.atomicStK op done (e :: rest) env k')) ch
      = .ok (.evalE e env (.atomicStK op (v :: done) rest env k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_atomicStK_more

theorem Pin.retV_atomicStK_apply : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {op : AtomicOp}
    {done : List GoValue} {c' : Config} {tr : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyAtomicOp ctx s op (v :: done).reverse env k' = .ok (c', s', tr)),
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .ok (c', s', ch, ⟨tr, [], []⟩) :=
  @GoLean.GoCore.Equations.retV_atomicStK_apply

theorem Pin.retV_atomicStK_apply_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : AtomicOp}
    {done : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyAtomicOp ctx s op (v :: done).reverse env k' = .error (.panic msg)),
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_atomicStK_apply_panic

theorem Pin.blockedSend : ∀ {ctx : ProgramCtx} (s : Store) (chl : Option Loc) (v : GoValue) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.blockedSend chl v k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedSend

theorem Pin.blockedRecv : ∀ {ctx : ProgramCtx} (s : Store) (chl : Option Loc) (targets : List Assignee)
    (elem : Ty) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.blockedRecv chl targets elem env k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedRecv

theorem Pin.blockedSelect : ∀ {ctx : ProgramCtx} (s : Store) (clauses : List EvClause) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.blockedSelect clauses env k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedSelect

theorem Pin.blockedSync : ∀ {ctx : ProgramCtx} (s : Store) (op : SyncOp) (loc : Loc) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.blockedSync op loc env k) ch = .error .deadlock :=
  @GoLean.GoCore.Equations.blockedSync

theorem Pin.exec_unseqProbe : ∀ {ctx : ProgramCtx} (s : Store) (e : Expr) (env : LocalEnv) (k : Cont)
    (ch : Choices),
    stepFn ctx s (.exec (.unseqProbe e) env k) ch = .ok (.evalE e env (.probeK k), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.exec_unseqProbe

theorem Pin.retV_probeK : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (k' : Cont) (ch : Choices),
    stepFn ctx s (.retV v (.probeK k')) ch = .ok (.next k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_probeK

theorem Pin.exec_unseq : ∀ {ctx : ProgramCtx} (s : Store) (g : UnseqGraph) (thenB : Stmt) (env : LocalEnv)
    (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.unseq g thenB) env k) ch = stepUnseqEnter ctx s g thenB env k ch :=
  @GoLean.GoCore.Equations.exec_unseq

theorem Pin.next_unseqK : ∀ {ctx : ProgramCtx} (s : Store) (g : UnseqGraph) (thenB : Stmt)
    (st : List UnseqStatus) (tg : List (VarId × TargetRef)) (env : LocalEnv) (ph : UnseqPhase) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.next (.unseqK g thenB st tg env ph k')) ch = stepUnseqNext ctx s g thenB st tg env ph k' ch :=
  @GoLean.GoCore.Equations.next_unseqK

theorem Pin.retV_unseqK : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (g : UnseqGraph) (thenB : Stmt)
    (st : List UnseqStatus) (tg : List (VarId × TargetRef)) (env : LocalEnv) (ph : UnseqPhase) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.retV v (.unseqK g thenB st tg env ph k')) ch = stepUnseqValue ctx s v g thenB st tg env ph k' ch :=
  @GoLean.GoCore.Equations.retV_unseqK

theorem Pin.unseqEnter : ∀ {ctx : ProgramCtx} {s s' : Store} {g : UnseqGraph} {env env' : LocalEnv}
    (thenB : Stmt) (rest : List Stmt) (k' : Cont) (ch : Choices) (_hwf : g.wellFormed? = none)
    (_hen : unseqEntryCheck? g env = none) (_ha : allocDecls ctx env.pushScope s g.cells = .ok (env', s')),
    stepFn ctx s (.exec (.unseq g thenB) env (.seq rest env k')) ch
      = .ok (.next (.unseqK g thenB g.initStatus [] env' .pick (.seq rest env k')), s', ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqEnter

theorem Pin.unseqValue : ∀ {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {g : UnseqGraph} {i : Nat}
    {o : UnseqOcc} {bind : VarId} {head : Expr} {loc : Loc} (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o)
    (_hbody : o.body = .eval bind head) (_hloc : unseqCellLoc env bind = .ok loc)
    (_hst : storeLoc ctx s loc v = .ok s'),
    stepFn ctx s (.retV v (.unseqK g thenB st tg env (.wait i) k')) ch
      = .ok (.next (.unseqK g thenB (st.set i .done) tg env .pick k'), s', ch, ⟨[.access .write (.data loc.canon)], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqValue

theorem Pin.unseqRun_eval : ∀ {ctx : ProgramCtx} {s : Store} {g : UnseqGraph} {i : Nat} {o : UnseqOcc}
    {bind : VarId} {head : Expr} (thenB : Stmt) (st : List UnseqStatus) (tg : List (VarId × TargetRef))
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o)
    (_hbody : o.body = .eval bind head),
    stepFn ctx s (.next (.unseqK g thenB st tg env (.run i) k')) ch
      = .ok (.evalE head env (.unseqK g thenB st tg env (.wait i) k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqRun_eval

theorem Pin.unseqWait_invoke : ∀ {ctx : ProgramCtx} {s : Store} {g : UnseqGraph} {i : Nat} {o : UnseqOcc}
    {binds : List VarId} {callee : Expr} {args : List Expr} (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o)
    (_hbody : o.body = .invoke binds callee args),
    stepFn ctx s (.next (.unseqK g thenB st tg env (.wait i) k')) ch
      = .ok (.next (.unseqK g thenB (st.set i .done) tg env .pick k'), s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.unseqWait_invoke

theorem Pin.stateWf_empty : ∀ {ctx : ProgramCtx},
    StateWf ctx ({} : Store) :=
  @GoLean.GoCore.Equations.stateWf_empty

theorem Pin.seedGlobals_nil : ∀ {ctx : ProgramCtx},
    seedGlobals ctx ({} : Store) #[] = .ok {} :=
  @GoLean.GoCore.Equations.seedGlobals_nil

theorem Pin.runPkgInitM_none : ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {ch : Choices}
    (_h : findFunctionIn? ctx.functions pkgInitFuncId = none),
    runPkgInitM ctx fuel s ch = .ok (s, ch) :=
  @GoLean.GoCore.Equations.runPkgInitM_none

theorem Pin.runProgramSetup_noInit : ∀ {fuel : Nat} {program : Program} {name : String} {args : Array GoValue}
    {choices : Choices} {func : Func} {env frameEnv : LocalEnv} {s₂ s₃ : Store} {resultLocs : List Loc}
    (_hf : findFunctionIn? program.funcs ⟨name⟩ = some func) (_harity : func.args.size = args.size)
    (_hres : program.typeDefs.hasReservedPrefix = true) (_hglob : program.globals = #[])
    (_hinit : findFunctionIn? program.funcs pkgInitFuncId = none)
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs),
    runProgramSetupM fuel program name args choices
      = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs, choices) :=
  @GoLean.GoCore.Equations.runProgramSetup_noInit

theorem Pin.pinResultLocs_eq_of_lookup :
    ∀ (env : LocalEnv) (ps : List Param) (f : Nat → Loc),
      (∀ (j : Nat) (hj : j < ps.length), LocalEnv.lookup env ps[j].id = some (f j)) →
      pinResultLocs env ps = .ok ((List.range ps.length).map f) :=
  @GoLean.GoCore.Equations.pinResultLocs_eq_of_lookup

theorem Pin.setup_lookup_arg : ∀ {program : Program} {func : Func} {args : Array GoValue}
    {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true) (i : Nat)
    (_hi : i < func.args.size),
    LocalEnv.lookup frameEnv func.args[i].id = some (.base ⟨i⟩) :=
  @GoLean.GoCore.Equations.setup_lookup_arg

theorem Pin.setup_lookup_result : ∀ {program : Program} {func : Func} {args : Array GoValue}
    {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true) (j : Nat)
    (_hj : j < func.results.size),
    LocalEnv.lookup frameEnv func.results[j].id = some (.base ⟨func.args.size + j⟩) :=
  @GoLean.GoCore.Equations.setup_lookup_result

theorem Pin.setup_resultLocs : ∀ {program : Program} {func : Func} {args : Array GoValue}
    {env frameEnv : LocalEnv} {s₂ s₃ : Store} {resultLocs : List Loc}
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (_hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (_hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs),
    resultLocs = (List.range func.results.size).map (fun j => Loc.base ⟨func.args.size + j⟩) :=
  @GoLean.GoCore.Equations.setup_resultLocs

theorem Pin.setup_heap_size : ∀ {program : Program} {func : Func} {args : Array GoValue}
    {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (_hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (_ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃)),
    s₃.heap.size = func.args.size + func.results.size :=
  @GoLean.GoCore.Equations.setup_heap_size

theorem Pin.bind_eq_error : ∀ {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {e : ε}
    (_h : x >>= f = .error e),
    x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e :=
  @GoLean.GoCore.Equations.bind_eq_error

theorem Pin.runCommit_error : ∀ {α : Type} {c : Commit α} {s : Store} {e : Stop} (_hcs : c s = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    runCommit c s = .error e :=
  @GoLean.GoCore.Equations.runCommit_error

theorem Pin.enterFramePickV_of_plan_error : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId}
    {args : List GoValue} {e : Stop} (ch : Choices) (_h : enterFrame.plan ctx s fid args = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    enterFramePickV ctx s fid args ch = .error e :=
  @GoLean.GoCore.Equations.enterFramePickV_of_plan_error

theorem Pin.enterFrame_inv_error : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId} {args : List GoValue}
    {e : Stop} (_h : enterFrame ctx s fid args = .error e),
    enterFrame.plan ctx s fid args = .error e ∨ ∃ c, enterFrame.plan ctx s fid args = .ok c ∧ c s = .error e :=
  @GoLean.GoCore.Equations.enterFrame_inv_error

theorem Pin.retV_syncStK_apply_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : SyncOp}
    {done : List GoValue} {msg : String} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySyncOp ctx s ch op (v :: done).reverse env k' = .error (.panic msg)),
    stepFn ctx s (.retV v (.syncStK op done [] env k')) ch = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_syncStK_apply_panic

theorem Pin.evalE_strict_nullary_error : ∀ {ctx : ProgramCtx} {s : Store} {e : Expr} {op : StrictOp} {st : Stop}
    (env : LocalEnv) (k : Cont) (ch : Choices) (_h : strictPlan e = some (op, []))
    (_ha : applyStrictOp ctx s (projChainTarget ctx s k) op [] = .error st) (_hne : ∀ msg, st ≠ .panic msg),
    stepFn ctx s (.evalE e env k) ch = .error st :=
  @GoLean.GoCore.Equations.evalE_strict_nullary_error

theorem Pin.retV_chanStK_apply_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : ChanStOp}
    {done : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyChanOp ctx s op (v :: done).reverse env k' = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.chanStK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_chanStK_apply_error

theorem Pin.retV_selectOpsK_apply_panic : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt} {done : List GoValue} {msg : String}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySelect ctx s clauses default? (v :: done).reverse env k' ch = .error (.panic msg)),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done [] env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) :=
  @GoLean.GoCore.Equations.retV_selectOpsK_apply_panic

theorem Pin.retV_selectOpsK_apply_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt} {done : List GoValue} {e : Stop}
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applySelect ctx s clauses default? (v :: done).reverse env k' ch = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.selectOpsK clauses default? done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_selectOpsK_apply_error

theorem Pin.retV_rhsK_apply_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {rop : RhsOp}
    {done : List GoValue} {e : Stop} (refs : List TargetRef) (body : Stmt) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_h : applyRhsOp ctx s rop (v :: done).reverse = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.rhsK rop refs done [] body env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_rhsK_apply_error

theorem Pin.retV_atomicStK_apply_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : AtomicOp}
    {done : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyAtomicOp ctx s op (v :: done).reverse env k' = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.atomicStK op done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_atomicStK_apply_error

theorem Pin.next_preprintK_error : ∀ {ctx : ProgramCtx} {s : Store} {older : List PanicEntry}
    {entry : PanicEntry} {newer : List PanicEntry} {e : Stop} (k' : Cont) (ch : Choices)
    (_h : preprintDispatch ctx s entry = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.next (.preprintK older entry newer k')) ch = .error e :=
  @GoLean.GoCore.Equations.next_preprintK_error

theorem Pin.retV_stmtOpK_apply_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {op : StmtOp} {nt : Nat}
    {done : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : applyStmtOp ctx s ch op nt (v :: done).reverse = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_stmtOpK_apply_error

theorem Pin.next_storeK_error : ∀ {ctx : ProgramCtx} {s : Store} {ref : TargetRef} {val : GoValue} {e : Stop}
    (rs : List TargetRef) (vrest : List GoValue) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : storeTarget ctx s ref val = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.next (.storeK (ref :: rs) (val :: vrest) body env k')) ch = .error e :=
  @GoLean.GoCore.Equations.next_storeK_error

theorem Pin.exec_call_nullary_error : ∀ {ctx : ProgramCtx} {s : Store} {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {plans : List (TargetShape × List Expr)} {e : Stop} (env : LocalEnv) (k : Cont)
    (ch : Choices) (_hp : targetsPlan targets.toList = some plans) (_hargs : args.toList = [])
    (_he : enterFrame ctx s fid [] = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.exec (.call targets fid args) env k) ch = .error e :=
  @GoLean.GoCore.Equations.exec_call_nullary_error

theorem Pin.retV_callArgsK_enter_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId}
    {plans : List (TargetShape × List Expr)} {vals : List GoValue} {e : Stop} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_he : enterFrame ctx s fid (vals ++ [v]) = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.callArgsK fid plans vals [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_callArgsK_enter_error

theorem Pin.retV_callValCalleeK_enter_error : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId}
    {captured : List GoValue} {plans : List (TargetShape × List Expr)} {e : Stop} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_he : enterFrame ctx s fid captured = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_enter_error

theorem Pin.retV_callValArgsK_enter_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {fid : FuncId}
    {captured vals : List GoValue} {plans : List (TargetShape × List Expr)} {e : Stop} (env : LocalEnv)
    (k' : Cont) (ch : Choices) (_he : enterFrame ctx s fid (captured ++ vals ++ [v]) = .error e)
    (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.retV v (.callValArgsK (.funcVal fid captured) plans vals [] env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_callValArgsK_enter_error

theorem Pin.panicking_frame_defer_error : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry}
    {fid : FuncId} {captured args : List GoValue} {e : Stop} (t : List (TargetShape × List Expr))
    (te : LocalEnv) (r : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFn ctx s (.panicking chain (.frame t te r ((.funcVal fid captured, args) :: ds) k' fr)) ch = .error e :=
  @GoLean.GoCore.Equations.panicking_frame_defer_error

theorem Pin.frameExit_defer_error : ∀ {ctx : ProgramCtx} {s : Store} {fid : FuncId}
    {captured args : List GoValue} {e : Stop} (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_he : enterFrame ctx s fid (captured ++ args) = .error e) (_hne : ∀ msg, e ≠ .panic msg),
    stepFrameExit ctx s targets tenv results ((.funcVal fid captured, args) :: ds) k' fr ch = .error e :=
  @GoLean.GoCore.Equations.frameExit_defer_error

theorem Pin.exec_block_error : ∀ {ctx : ProgramCtx} {s : Store} {decls : Array Param} {env : LocalEnv}
    {e : Stop} (ss : Array Stmt) (k : Cont) (ch : Choices)
    (_h : allocDecls ctx env.pushScope s decls.toList = .error e),
    stepFn ctx s (.exec (.block decls ss) env k) ch = .error e :=
  @GoLean.GoCore.Equations.exec_block_error

theorem Pin.evalE_var_error : ∀ {ctx : ProgramCtx} {s : Store} {id : VarId} {loc : Loc} {e : Stop}
    (env : LocalEnv) (k : Cont) (ch : Choices) (_hl : LocalEnv.lookup env id = some loc)
    (_hv : loadRoot ctx s loc = .error e),
    stepFn ctx s (.evalE (.var id) env k) ch = .error e :=
  @GoLean.GoCore.Equations.evalE_var_error

theorem Pin.retV_mapRangeK_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop}
    (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : mapRangeStartSets s v = .error e),
    stepFn ctx s (.retV v (.mapRangeK keyVar valVar keyTy valTy body env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_mapRangeK_error

theorem Pin.next_mapIterK_error : ∀ {ctx : ProgramCtx} {s : Store} {keyTy valTy : Ty} {base : Option Loc}
    {produced : Array Nat} {e : Stop} (keyVar valVar : Option VarId) (body : Stmt) (start : Array Nat)
    (env : LocalEnv) (k' : Cont) (ch : Choices)
    (_h : mapIterCandidates ctx s keyTy valTy base produced = .error e),
    stepFn ctx s (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) ch = .error e :=
  @GoLean.GoCore.Equations.next_mapIterK_error

theorem Pin.frameExit_targets_error : ∀ {ctx : ProgramCtx} {s : Store} {results : List Loc} {e : Stop}
    (sh : TargetShape) (ex : Expr) (ops : List Expr) (rest : List (TargetShape × List Expr)) (tenv : LocalEnv)
    (k' : Cont) (fr : FuncId) (ch : Choices) (_hl : loadResults ctx s results = .error e),
    stepFrameExit ctx s ((sh, ex :: ops) :: rest) tenv results [] k' fr ch = .error e :=
  @GoLean.GoCore.Equations.frameExit_targets_error

theorem Pin.frameExit_preprint_error : ∀ {ctx : ProgramCtx} {s : Store} {rl : Loc} {e : Stop} (tenv : LocalEnv)
    (older : List PanicEntry) (entry : PanicEntry) (newer : List PanicEntry) (k'' : Cont) (fr : FuncId)
    (ch : Choices) (_hl : loadRoot ctx s rl = .error e),
    stepFrameExit ctx s [] tenv [rl] [] (.preprintK older entry newer k'') fr ch = .error e :=
  @GoLean.GoCore.Equations.frameExit_preprint_error

theorem Pin.unseqEnter_error : ∀ {ctx : ProgramCtx} {s : Store} {g : UnseqGraph} {env : LocalEnv} {e : Stop}
    (thenB : Stmt) (rest : List Stmt) (k' : Cont) (ch : Choices) (_hwf : g.wellFormed? = none)
    (_hen : unseqEntryCheck? g env = none) (_ha : allocDecls ctx env.pushScope s g.cells = .error e),
    stepFn ctx s (.exec (.unseq g thenB) env (.seq rest env k')) ch = .error e :=
  @GoLean.GoCore.Equations.unseqEnter_error

theorem Pin.unseqValue_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {g : UnseqGraph} {i : Nat}
    {o : UnseqOcc} {bind : VarId} {head : Expr} {loc : Loc} {e : Stop} (thenB : Stmt) (st : List UnseqStatus)
    (tg : List (VarId × TargetRef)) (env : LocalEnv) (k' : Cont) (ch : Choices) (_hget : g.occs[i]? = some o)
    (_hbody : o.body = .eval bind head) (_hloc : unseqCellLoc env bind = .ok loc)
    (_hst : storeLoc ctx s loc v = .error e),
    stepFn ctx s (.retV v (.unseqK g thenB st tg env (.wait i) k')) ch = .error e :=
  @GoLean.GoCore.Equations.unseqValue_error

theorem Pin.retV_ifK_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (t el : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.ifK t el env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_ifK_error

theorem Pin.retV_whileK_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (c : Expr) (b : Stmt)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.whileK c b env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_whileK_error

theorem Pin.retV_andK_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (r : Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.andK r env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_andK_error

theorem Pin.retV_orK_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (r : Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.orK r env k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_orK_error

theorem Pin.retV_boolK_error : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} {e : Stop} (k' : Cont)
    (ch : Choices) (_hv : valueAsBool v = .error e),
    stepFn ctx s (.retV v (.boolK k')) ch = .error e :=
  @GoLean.GoCore.Equations.retV_boolK_error

theorem Pin.valueAsBool_nonbool : ∀ {v : GoValue} (_h : ∀ b, v ≠ .bool b),
    valueAsBool v = .error (.stuck s!"expected bool value, got {repr v}") :=
  @GoLean.GoCore.Equations.valueAsBool_nonbool

theorem Pin.retV_callValCalleeK_args_notfunc : ∀ {ctx : ProgramCtx} {s : Store} {cv : GoValue}
    (plans : List (TargetShape × List Expr)) (a : Expr) (rest : List Expr) (env : LocalEnv) (k' : Cont)
    (ch : Choices) (_hd : deferrableCallee cv = false),
    stepFn ctx s (.retV cv (.callValCalleeK plans (a :: rest) env k')) ch
      = .error (.stuck s!"expected function value, got {repr cv}") :=
  @GoLean.GoCore.Equations.retV_callValCalleeK_args_notfunc

theorem Pin.retV_deferCalleeK_notfunc : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (args : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hd : deferrableCallee v = false),
    stepFn ctx s (.retV v (.deferCalleeK args env k')) ch = .error (.stuck s!"expected function value in defer, got {repr v}") :=
  @GoLean.GoCore.Equations.retV_deferCalleeK_notfunc

theorem Pin.retV_goCalleeK_notfunc : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (args : List Expr)
    (env : LocalEnv) (k' : Cont) (ch : Choices) (_hd : deferrableCallee v = false),
    stepFn ctx s (.retV v (.goCalleeK args env k')) ch = .error (.stuck s!"expected function value in go statement, got {repr v}") :=
  @GoLean.GoCore.Equations.retV_goCalleeK_notfunc

theorem Pin.deferrableCallee_false : ∀ {cv : GoValue} (_hf : ∀ fid c, cv ≠ .funcVal fid c) (_hn : cv ≠ .nil),
    deferrableCallee cv = false :=
  @GoLean.GoCore.Equations.deferrableCallee_false

theorem Pin.panicking_frame_defer_notfunc : ∀ {ctx : ProgramCtx} {s : Store} {chain : List PanicEntry}
    {cv : GoValue} (args : List GoValue) (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_hf : ∀ fid c, cv ≠ .funcVal fid c) (_hn : cv ≠ .nil),
    stepFn ctx s (.panicking chain (.frame t te r ((cv, args) :: ds) k' fr)) ch
      = .error (.stuck s!"deferred callee is not a function value: {repr cv}") :=
  @GoLean.GoCore.Equations.panicking_frame_defer_notfunc

theorem Pin.frameExit_defer_notfunc : ∀ {ctx : ProgramCtx} {s : Store} {cv : GoValue} (args : List GoValue)
    (targets : List (TargetShape × List Expr)) (tenv : LocalEnv) (results : List Loc)
    (ds : List (GoValue × List GoValue)) (k' : Cont) (fr : FuncId) (ch : Choices)
    (_hf : ∀ fid c, cv ≠ .funcVal fid c) (_hn : cv ≠ .nil),
    stepFrameExit ctx s targets tenv results ((cv, args) :: ds) k' fr ch
      = .error (.stuck s!"deferred callee is not a function value: {repr cv}") :=
  @GoLean.GoCore.Equations.frameExit_defer_notfunc

theorem Pin.retV_preprintK_nonstring : ∀ {ctx : ProgramCtx} {s : Store} {v : GoValue} (older : List PanicEntry)
    (entry : PanicEntry) (newer : List PanicEntry) (k' : Cont) (ch : Choices) (_hs : ∀ t, v ≠ .string t),
    stepFn ctx s (.retV v (.preprintK older entry newer k')) ch
      = .error (.stuck s!"preprint: the payload method returned a non-string result {repr v}") :=
  @GoLean.GoCore.Equations.retV_preprintK_nonstring

theorem Pin.next_storeK_arity_refs : ∀ {ctx : ProgramCtx} (s : Store) (r : TargetRef) (rs : List TargetRef)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.storeK (r :: rs) [] body env k')) ch
      = .error (.internal "storeK value/target arity mismatch (the shared phase-2 spine: receive delivery, assignment, comma-ok, call write-back)") :=
  @GoLean.GoCore.Equations.next_storeK_arity_refs

theorem Pin.next_storeK_arity_vals : ∀ {ctx : ProgramCtx} (s : Store) (v : GoValue) (vs : List GoValue)
    (body : Stmt) (env : LocalEnv) (k' : Cont) (ch : Choices),
    stepFn ctx s (.next (.storeK [] (v :: vs) body env k')) ch
      = .error (.internal "storeK value/target arity mismatch (the shared phase-2 spine: receive delivery, assignment, comma-ok, call write-back)") :=
  @GoLean.GoCore.Equations.next_storeK_arity_vals

theorem Pin.contHeadLabel_labelK : ∀ (name : String) (k : Cont),
    contHeadLabel (.labelK name k) = some name :=
  @GoLean.GoCore.Equations.contHeadLabel_labelK

theorem Pin.contHeadLabel_stop :
    contHeadLabel .stop = none :=
  @GoLean.GoCore.Equations.contHeadLabel_stop

theorem Pin.contHeadLabel_frame : ∀ (t : List (TargetShape × List Expr)) (te : LocalEnv) (r : List Loc)
    (ds : List (GoValue × List GoValue)) (k : Cont) (fr : FuncId),
    contHeadLabel (.frame t te r ds k fr) = none :=
  @GoLean.GoCore.Equations.contHeadLabel_frame

theorem Pin.signalStep_breakableK_brkTo : ∀ (L : String) (k' : Cont),
    signalStep (.brkTo L) (.breakableK k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_brkTo

theorem Pin.signalStep_breakableK_contTo : ∀ (L : String) (k' : Cont),
    signalStep (.contTo L) (.breakableK k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_breakableK_contTo

theorem Pin.signalStep_labelK_brk : ∀ (name : String) (k' : Cont),
    signalStep .brk (.labelK name k') = some (.signal .brk k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_brk

theorem Pin.signalStep_labelK_cont : ∀ (name : String) (k' : Cont),
    signalStep .cont (.labelK name k') = some (.signal .cont k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_cont

theorem Pin.signalStep_labelK_brkTo_ne : ∀ {name L : String} (k' : Cont) (_h : name ≠ L),
    signalStep (.brkTo L) (.labelK name k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_brkTo_ne

theorem Pin.signalStep_labelK_contTo_self : ∀ (name : String) (k' : Cont),
    signalStep (.contTo name) (.labelK name k') = none :=
  @GoLean.GoCore.Equations.signalStep_labelK_contTo_self

theorem Pin.signalStep_labelK_contTo_ne : ∀ {name L : String} (k' : Cont) (_h : name ≠ L),
    signalStep (.contTo L) (.labelK name k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_labelK_contTo_ne

theorem Pin.signalStep_loop_brkTo : ∀ (L : String) (c : Expr) (b : Stmt) (env : LocalEnv) (k' : Cont),
    signalStep (.brkTo L) (.loop c b env k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_loop_brkTo

theorem Pin.signalStep_loop_contTo_self : ∀ {L : String} (c : Expr) (b : Stmt) (env : LocalEnv) {k' : Cont}
    (_h : contHeadLabel k' = some L),
    signalStep (.contTo L) (.loop c b env k') = some (.exec (.while c b) env k') :=
  @GoLean.GoCore.Equations.signalStep_loop_contTo_self

theorem Pin.signalStep_loop_contTo_ne : ∀ {L : String} (c : Expr) (b : Stmt) (env : LocalEnv) {k' : Cont}
    (_h : contHeadLabel k' ≠ some L),
    signalStep (.contTo L) (.loop c b env k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_loop_contTo_ne

theorem Pin.signalStep_mapIterK_brk : ∀ (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt)
    (base : Option Loc) (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep .brk (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.next k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_brk

theorem Pin.signalStep_mapIterK_cont : ∀ (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt)
    (base : Option Loc) (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep .cont (.mapIterK keyVar valVar keyTy valTy body base produced start env k')
      = some (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_cont

theorem Pin.signalStep_mapIterK_ret : ∀ (keyVar valVar : Option VarId) (keyTy valTy : Ty) (body : Stmt)
    (base : Option Loc) (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep .ret (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.signal .ret k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_ret

theorem Pin.signalStep_mapIterK_brkTo : ∀ (L : String) (keyVar valVar : Option VarId) (keyTy valTy : Ty)
    (body : Stmt) (base : Option Loc) (produced start : Array Nat) (env : LocalEnv) (k' : Cont),
    signalStep (.brkTo L) (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.signal (.brkTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_brkTo

theorem Pin.signalStep_mapIterK_contTo_self : ∀ {L : String} (keyVar valVar : Option VarId) (keyTy valTy : Ty)
    (body : Stmt) (base : Option Loc) (produced start : Array Nat) (env : LocalEnv) {k' : Cont}
    (_h : contHeadLabel k' = some L),
    signalStep (.contTo L) (.mapIterK keyVar valVar keyTy valTy body base produced start env k')
      = some (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k')) :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_contTo_self

theorem Pin.signalStep_mapIterK_contTo_ne : ∀ {L : String} (keyVar valVar : Option VarId) (keyTy valTy : Ty)
    (body : Stmt) (base : Option Loc) (produced start : Array Nat) (env : LocalEnv) {k' : Cont}
    (_h : contHeadLabel k' ≠ some L),
    signalStep (.contTo L) (.mapIterK keyVar valVar keyTy valTy body base produced start env k') = some (.signal (.contTo L) k') :=
  @GoLean.GoCore.Equations.signalStep_mapIterK_contTo_ne

theorem Pin.signal_labelK_contTo_self : ∀ {ctx : ProgramCtx} (s : Store) (name : String) (k' : Cont)
    (ch : Choices),
    stepFn ctx s (.signal (.contTo name) (.labelK name k')) ch = .error (.stuck s!"continue to non-loop label {name}") :=
  @GoLean.GoCore.Equations.signal_labelK_contTo_self
-- PINS-END
end Pins

/-! ## The enrollment and NO-UNFOLD check (pre-landing round, audit F2: a Lean-level proof-term check; the
window review's F2: over the proof-dependency CLOSURE of the client's own declarations) -/

open Lean in
/-- Every `theorem` of the namespace `GoLean.GoCore.Equations` (auxiliary and internal names
excluded). -/
def equationTheorems (env : Environment) : List Name :=
  env.constants.fold (init := []) fun acc n ci =>
    if (`GoLean.GoCore.Equations).isPrefixOf n && !n.isInternal then
      match ci with
      | .thmInfo _ => n :: acc
      | _ => acc
    else acc

open Lean in
/-- The facts of §A (`Tests.EquationClient.fact_*`). -/
def factTheorems (env : Environment) : List Name :=
  env.constants.fold (init := []) fun acc n ci =>
    if n.getPrefix == `Tests.EquationClient && (n.getString!.startsWith "fact_") && !n.isInternal then
      match ci with
      | .thmInfo _ => n :: acc
      | _ => acc
    else acc

open Lean in
/-- THE PUBLISHED API — the modules whose constants are the BOUNDARY of the closure check (cited, never traversed):
the equation set and its attribute, the prefix algebra and the execution statements it refines, the pool projections,
the pinned bridge set. A fact may use what these modules state; a lemma from ANY other module (the interpreter's own
`rfl`-theorems in `StepFn`/`Machine`/`MachineSound`, a test-support module) is a HELPER and is checked like one
(the audit's re-verification R1: an imported `rfl`-theorem over `stepFn` is an unfolding of `stepFn`). -/
def apiModules : List Name :=
  [`GoLean.GoCore.Equations, `GoLean.GoCore.EquationsAttr, `GoLean.GoCore.Prefix, `GoLean.GoCore.ExecutionStatement,
   `GoLean.GoCore.PoolProjection, `GoLean.GoCore.BridgeSet]

open Lean in
/-- The IMPORT WHITELIST of this module: the toolchain roots and the API modules — every DIRECT import of the client
must be one of these (`checkEnrollment` reads the environment's header; the gate pre-filters the `import` lines). What
they transitively bring (the interpreter, `Init`/`Std`/`Lean`) comes along and is classified below. -/
def importWhitelist : List Name := [`Init, `Std, `Lean] ++ apiModules

open Lean in
/-- A TOOLCHAIN module (`Init`/`Std`/`Lean`/`Lake`): compiled before `stepFn` exists, so none of its constants can
reach `stepFn` by unfolding — a boundary by construction. -/
def toolchainModule (m : Name) : Bool :=
  [`Init, `Std, `Lean, `Lake].any fun r => r == m || r.isPrefixOf m

/-- What the closure check does with a constant, by its module. -/
inductive Owner where
  /-- this module, or a foreign non-`GoLean` module (a test-support module): EVERY value is traversed -/
  | client
  /-- a non-API `GoLean` module (the semantic core: `StepFn`, `Machine`, `Ops`, …): its THEOREMS and Prop-typed
  constants are traversed (a `rfl`-theorem over `stepFn` there is an unfolding); its DEFINITIONS are the SUBJECT —
  what a proof may or may not unfold, which check (3) measures at the use site — and are not traversed (`stepFn`
  itself first of all; the core's own gates — the escape-hatch scans, no evaluation-by-kernel closers — exclude a
  proof hidden in a core definition) -/
  | core
  /-- an API module or a toolchain module: the boundary -/
  | boundary
  deriving Repr, DecidableEq

open Lean in
/-- The owner of a constant: by the module that declares it (`none` = this module). -/
def ownerOf (env : Environment) (c : Name) : Owner :=
  match env.getModuleIdxFor? c with
  | none => .client
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if apiModules.contains m || toolchainModule m then .boundary
      else if (`GoLean).isPrefixOf m then .core
      else .client

open Lean in
/-- Does DEFINITIONAL UNFOLDING from the constant `c` reach `stepFn`? — `c` is `stepFn`, or the VALUE of `c` (a
definition's body, a theorem's proof, an opaque's value) names a constant that does; an inductive, a
constructor, a recursor, an axiom has no value and reaches nothing. Memoized. This is the test that lets the
no-unfold check SKIP a defeq obligation neither side of which names such a constant: the kernel's check of
that obligation can only unfold what its two sides name, so it never meets `stepFn` — re-running it would
prove nothing about `stepFn` and may be arbitrarily expensive (the inhabitation's `abortMsg … = .ok "boom"`,
well-founded UTF-8 decoding, is such an obligation). Every obligation that CAN reach `stepFn` is re-run with
`stepFn` irreducible. -/
partial def reachesStepFn (env : Environment) (stepFnN : Name) (c : Name) : StateM (NameMap Bool) Bool := do
  if c == stepFnN then return true
  if let some b := (← get).find? c then return b
  modify fun m => m.insert c false  -- the cycle guard (mutual blocks)
  let r ← match env.find? c with
    | some ci =>
        match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants.anyM fun d => reachesStepFn env stepFnN d
        | none => pure false
    | none => pure false
  modify fun m => m.insert c r
  return r

open Lean Meta in
/-- May a defeq check of `e` unfold `stepFn`? — a constant of `e` (let-bound locals zeta-expanded; the types
of its free locals included, conservatively) reaches `stepFn`. -/
def mayUnfoldStepFn (env : Environment) (stepFnN : Name) (memo : IO.Ref (NameMap Bool)) (e : Lean.Expr) :
    MetaM Bool := do
  let e ← zetaReduce (← instantiateMVars e)
  let mut cs := e.getUsedConstants
  for fv in (collectFVars {} e).fvarIds do
    cs := cs ++ (← fv.getDecl).type.getUsedConstants
  let (r, m') := (cs.anyM fun c => reachesStepFn env stepFnN c).run (← memo.get)
  memo.set m'
  return r

open Lean Meta in
/-- THE NO-UNFOLD CHECK of a proof term, Lean-level. A proof «by the equation set only» (1) names no constant
under `GoLean.GoCore.Machine.stepFn.` (the interpreter's equation lemmas `eq_def`/`eq_N`, its matchers
`match_N` — what `unfold`/`rw [stepFn]`/`delta stepFn` leave), (2) closes no `stepFn`-headed equation by
`Eq.refl`/`rfl`, and (3) TYPE-CHECKS WITH `stepFn` IRREDUCIBLE: every defeq obligation of the term (each
application's argument against its binder, each `let`, and the term's type against the statement) THAT CAN
UNFOLD `stepFn` (`mayUnfoldStepFn` on either side) is re-checked at default transparency with `stepFn` marked
irreducible — what a `simp`/`simp_all`/`simpa` call given `stepFn` itself, `simp only` of it followed by
`rfl`, and `delta` hide in a cast (`@id`, `Eq.mpr`) fails here, while a proof by the equations
(propositional rewrites, `defn_eq`) and by the `Prefix`/`Finish` constructors needs no unfolding of `stepFn`.
The traversal is `Meta.check`'s shape at a controlled transparency (`Meta.check` itself runs at `.all`, which
unfolds irreducibles). (4) Axioms: the classical trio at most. -/
partial def checkNoUnfold (stepFnN : Name) (may : Lean.Expr → MetaM Bool) : Lean.Expr → MetaM Unit
  | e@(.app ..) => do
    let f := e.getAppFn
    let args := e.getAppArgs
    checkNoUnfold stepFnN may f
    let mut fType ← inferType f
    for a in args do
      checkNoUnfold stepFnN may a
      fType ← whnf fType
      let .forallE _ dom body _ := fType
        | throwError "no-unfold check: {f} applied beyond its arity"
      let aType ← inferType a
      if (← may aType) || (← may dom) then
        unless ← isDefEq aType dom do
          throwError "a defeq obligation needs `stepFn` unfolded: argument {a} : {aType} against {dom}"
      fType := body.instantiate1 a
  | .lam n d b bi => do
    checkNoUnfold stepFnN may d
    withLocalDecl n bi d fun x => checkNoUnfold stepFnN may (b.instantiate1 x)
  | .forallE n d b bi => do
    checkNoUnfold stepFnN may d
    withLocalDecl n bi d fun x => checkNoUnfold stepFnN may (b.instantiate1 x)
  | .letE n t v b _ => do
    checkNoUnfold stepFnN may t
    checkNoUnfold stepFnN may v
    let vt ← inferType v
    if (← may vt) || (← may t) then
      unless ← isDefEq vt t do
        throwError "a `let` obligation needs `stepFn` unfolded: {v} : {t}"
    withLetDecl n t v fun x => checkNoUnfold stepFnN may (b.instantiate1 x)
  | .mdata _ b => checkNoUnfold stepFnN may b
  | .proj _ _ b => checkNoUnfold stepFnN may b
  | _ => pure ()

open Lean Meta in
/-- Fail-closed: a non-whitelisted IMPORT; a fact whose proof — or the proof/value of any declaration its proof depends
on, transitively, up to the published API (`apiModules`; the window review's F2 and the audit's R1: a helper proved by
`rfl` on `stepFn`, whether private to this file, in the interpreter's own modules or in a foreign module) — unfolds
`stepFn` by any of the four readings above; an equation without a pin; a pin whose type is not the equation's (up to
alpha-equivalence); a fact count that drifted from `factCount`: each is an elaboration error. The closure follows
`getUsedConstants` of the values; `ownerOf` settles per constant: `.client` traversed whole, `.core` traversed for its
theorems and Prop-typed constants (never `stepFn` itself), `.boundary` cited and stopped at. The facts are checked
FIRST, so a mutant client reports the refused fact before any enrollment issue; a refusal names the fact and, when the
unfolding is in a helper, the helper. -/
def checkEnrollment : CoreM Unit := do
  let env ← getEnv
  let stepFnN := `GoLean.GoCore.Machine.stepFn
  -- (0) the import whitelist: every DIRECT import of this module
  for imp in env.header.imports do
    unless importWhitelist.contains imp.module do
      throwError "Equation client: import {imp.module} is NOT WHITELISTED — the client may import only {importWhitelist}"
  let facts := factTheorems env
  if facts.isEmpty then
    throwError "Equation client: NO fact_* theorems found (fail closed)"
  let memo ← IO.mkRef ({} : NameMap Bool)
  let userName (c : Name) : Name := if isPrivateName c then privateToUserName c else c
  -- is the constant traversed? (by owner and kind)
  let traverse (c : Name) (ci : ConstantInfo) : MetaM Bool := do
    if c == stepFnN then return false
    match ownerOf env c with
    | .boundary => return false
    | .client => return true
    | .core =>
        match ci with
        | .thmInfo _ => return true
        | _ => isProp ci.type
  -- (1)–(4) per fact and per traversed declaration its proof reaches, with `stepFn` irreducible for the duration of (3)
  let st0 ← getReducibilityStatus stepFnN
  setIrreducibleAttribute stepFnN
  let mut checked : NameSet := {}
  let mut nHelpers := 0
  try
    for root in facts do
      let mut work : List Name := [root]
      while !work.isEmpty do
        let c := work.head!
        work := work.tail
        if checked.contains c then continue
        checked := checked.insert c
        let some ci := env.find? c | throwError "Equation client: {c} vanished"
        unless c == root || (← MetaM.run' (traverse c ci)) do continue
        let some value := ci.value? (allowOpaque := true) | continue  -- an inductive/constructor/recursor: no proof
        let who := if c == root then s!"fact {root} REFUSED — its proof unfolds stepFn"
          else s!"fact {root} REFUSED — its proof unfolds stepFn in its helper {userName c}"
        if c != root then nHelpers := nHelpers + 1
        -- (1) the interpreter's own equation lemmas (`eq_N`, `eq_def`, …); its matchers `match_N` are not an unfolding
        -- (a reused matcher cannot reduce `stepFn`; a proof through one still meets check (3))
        let used := value.foldConsts (init := ([] : List Name)) fun d acc =>
          if stepFnN.isPrefixOf d && d != stepFnN && !(d.getString!.startsWith "match_") then d :: acc else acc
        unless used.isEmpty do
          throwError "Equation client: {who} (it names {used.head!})"
        -- (2) reflexivity on a `stepFn`-headed term
        if let some sub := value.find? fun sub =>
            (sub.isAppOfArity ``Eq.refl 2 || sub.isAppOfArity ``rfl 2) && sub.appArg!.getAppFn.isConstOf stepFnN then
          throwError "Equation client: {who} (it closes {sub} by reflexivity)"
        -- (3) the term type-checks against its statement with `stepFn` irreducible
        let may := mayUnfoldStepFn env stepFnN memo
        let ok ← MetaM.run' do
          try
            withTransparency .default do
              checkNoUnfold stepFnN may value
              let ty ← inferType value
              if (← may ty) || (← may ci.type) then
                unless ← isDefEq ty ci.type do
                  throwError "the proof's type {ty} is not the statement without unfolding stepFn"
            pure (none : Option String)
          catch ex => pure (some (← ex.toMessageData.toString))
        if let some why := ok then
          throwError "Equation client: {who} ({why})"
        -- the closure: every constant the value names (its owner settles whether it is traversed, above)
        for d in value.getUsedConstants do
          if !checked.contains d then
            work := d :: work
      -- (4) axioms (transitive already)
      let axioms ← collectAxioms root
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Equation client: fact {root} REFUSED — it depends on the axiom {ax}"
  finally
    setReducibilityStatus stepFnN st0
  unless facts.length == factCount do
    throwError "Equation client: factCount = {factCount} but {facts.length} fact_* theorems are present"
  -- the exhaustive enrollment
  let eqns := equationTheorems env
  if eqns.isEmpty then
    throwError "Equation client: NO equation theorems found in GoLean.GoCore.Equations (fail closed)"
  let mut pinned := 0
  for n in eqns do
    -- the pin's name is the theorem's name under the namespace `Pin` (dotted names included:
    -- `Equations.Heap.lookup_set_self` ↦ `Pin.Heap.lookup_set_self`)
    let pin := (`Tests.EquationClient.Pin).append (n.replacePrefix `GoLean.GoCore.Equations .anonymous)
    match env.find? pin with
    | some (.thmInfo pi) =>
        let some ci := env.find? n | throwError "Equation client: {n} vanished"
        unless ci.type == pi.type do
          throwError "Equation client: pin {pin} does not state {n} (its type differs from the theorem's)"
        pinned := pinned + 1
    | some _ => throwError "Equation client: {pin} exists but is not a theorem"
    | none => throwError "Equation client: UNENROLLED equation {n} — no pin {pin} in Tests/EquationClient.lean"
  logInfo s!"Equation client: enrollment complete — {pinned} equation theorems pinned, {facts.length} facts and {nHelpers} traversed helpers up to the published API, none unfolds stepFn"

#eval checkEnrollment

end Tests.EquationClient

/-- The PASS line `scripts/check-equations` greps for (reached only if every declaration above —
the facts, the pins and the enrollment `#eval` — elaborated). -/
def main (_args : List String) : IO Unit := do
  IO.println s!"Equation client: PASS — {Tests.EquationClient.factCount} facts by the equation set and the published API"
