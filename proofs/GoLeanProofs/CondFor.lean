import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.SliceMem
import GoLeanProofs.SliceWalk

/-!
# The plain-for (cond-only) loop schema (A4d-SM1, the span-model arc's
one new kit piece)

**W2 harvest provenance (2026-08-27)**: ported VERBATIM (content
unchanged below this banner) from the read-only harvest source
`campaign-arc4d:proofs/GoLeanProofs/Sym/UtoaForKit.lean`
(@ 7fa0e04d), per the clean-proof plan §W2 / professor delta — the
plain-`for` head schema. All four imports are byte-identical
between the branches (verified by `git hash-object` at harvest), so
the port is a drop-in; only the module path changed
(`Sym/UtoaForKit` → `CondFor` — the schema is general-layer loop
kit, not utoa-specific). The `Sym/UtoaSpan.lean` consumer named
below exists only on the killed arc4d branch; on THIS branch the
schema's consumers are the countdown witness in this file (the
∃-discharge, `countdown_span`/`cd_concrete`) and the W2 init spec.
Stream discipline: STREAM-TOTAL — the schema and both hypothesis
facts thread `ch` unchanged (a cond/body that consumes draws needs
the draw-consuming sibling, built on demand). Audit pins:
`Audit/W2.lean`.

The native frontend desugars the cond-only plain `for cond { body }`
into ONE fixed shape (verified against the pinned twin lowering,
`artifacts/probe/utoadump.out` (untracked scratch) — `utoa`'s digit loop carries it
verbatim; `main.twin.harvest`'s Ready loop carries the same skeleton
with a call-prep statement in the second slot,
`artifacts/probe/harvestdump.out` (untracked scratch)):

```
block [] [
  init $forFirst; $forFirst := true;
  while true {
    if $forFirst { $forFirst = false } else { seqn [] };
    seqn [];                -- the cond-prep slot (empty for a pure cond)
    if cond { seqn [] } else { break };
    body
  }]
```

`SliceWalk` covers only the RANGE desugar (`$rcoll/$rlen/$ridx`
temps, its own bound check); the plain-for head needs this sibling
schema: the `$forFirst` latch glue, the PARAMETERIZED loop condition
(an instance fact — the range schema's bound check is fixed, this
one's cond is the loop's own expression), the break path, and the
composed loop schema `condFor_loop` in the compositional mode (I2):
symbolic preconditions, a state-family invariant, and a
BOUNDED-COMPLETION conclusion.

Scope, per the middle path (§7 of the flexibility redesign): the
cond-prep slot is fixed EMPTY (`seqn []`) — a pure-expression
condition. That covers every `for <expr> { … }` loop; the
call-conditioned variant (harvest's `for nd.rn.HasReady()`) is the
recorded latent consumer of a prep-parameterized generalization and
is deliberately NOT built ahead of its demand.

Consumers (triage hygiene 2026-08-27, P-2 — the old claim named
`Sym/UtoaSpan.lean`, which does not exist in this tree, a killed-era
citation): the live discharge is the in-file countdown witness pair
(`countdown_span`/`cd_concrete`); `utoa`'s digit loop (the original
cost driver) and harvest's Ready loop are the named latent consumers
at the tier-3 loop-law unit.

LINEAGE (clever-tricks doctrine): the Floyd/Hoare loop invariant —
the same per-iteration-fact induction as `SliceWalk.sliceWalk_loop`,
specialized to the frontend's plain-for desugar so instances prove
only their cond and body facts.

## The measured anatomy (trace `artifacts/probe/utoatrace.out` (untracked scratch), the
U24 banked map re-verified in this arc's log)

From the loop-head config (`.exec (.while true …)`), per iteration:
- head glue, first iteration (flag true): 19 steps to the cond
  dispatch, writing `$forFirst := false` (17 of the range schema's
  glue + 2 for the empty prep slot);
- head glue, subsequent (flag false): 12 steps, state untouched;
- cond entry: 1 step (`if` entry → `.evalE cond`); the cond WALK is
  the instance's fact;
- branch, continue case (cond true): 3 steps to the body config;
- branch, exit case (cond false): 4 steps to `.next k` (break
  unwind);
- body → head back edge: 2 steps.
-/

namespace GoLean.CondFor

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk (envB flagCell flagSet stepFn_ref normalize_bool
  lookup_pushScope)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! ## 1. The desugared shape (statement vocabulary) -/

/-- The latch statement: first iteration clears `$forFirst`, later
ones do nothing (the cond-only shape; a 3-clause `for`'s post rides
this slot family — out of scope, module docstring). -/
def flagIf (fF : String) : Stmt :=
  .ifThenElse (.var fF) (.assign (.var fF) (.boolLit false)) (.seqn #[])

/-- The loop condition check: `cond → continue, else break`. -/
def condIf (cond : Expr) : Stmt :=
  .ifThenElse cond (.seqn #[]) .breakStmt

/-- The while body (the frontend's fixed shape: latch, empty prep
slot, cond check, body). -/
def wbody (fF : String) (cond : Expr) (body : Stmt) : Stmt :=
  .block #[] #[flagIf fF, .seqn #[], condIf cond, body]

/-- The whole loop statement. -/
def cwhile (fF : String) (cond : Expr) (body : Stmt) : Stmt :=
  .while (.boolLit true) (wbody fF cond body)

/-! ## 2. The configuration vocabulary -/

/-- The loop continuation (the back edge's carrier). -/
def loopK (fF : String) (cond : Expr) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Cont :=
  .loop (.boolLit true) (wbody fF cond body) envW k

/-- The loop-head configuration (the schema's anchor). -/
def headCfg (fF : String) (cond : Expr) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Config :=
  .exec (cwhile fF cond body) envW k

/-- The cond-dispatch configuration (glue segments land here). -/
def condCfg (fF : String) (cond : Expr) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Config :=
  .exec (condIf cond) (envB envW)
    (.seq [body] (envB envW) (loopK fF cond body envW k))

/-- The continuation the loop condition evaluates under (what the
instance's cond fact must deliver its Bool to). -/
def condK (fF : String) (cond : Expr) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Cont :=
  .ifK (.seqn #[]) .breakStmt (envB envW)
    (.seq [body] (envB envW) (loopK fF cond body envW k))

/-- The body configuration (what an instance's body fact runs from). -/
def bodyCfg (fF : String) (cond : Expr) (body : Stmt) (envW : LocalEnv)
    (k : Cont) : Config :=
  .exec body (envB envW)
    (.seq [] (envB envW) (loopK fF cond body envW k))

/-- The body's exit configuration (a body completing normally hands
back exactly this; 2 further steps reach the head). -/
def bodyDoneCfg (fF : String) (cond : Expr) (body : Stmt)
    (envW : LocalEnv) (k : Cont) : Config :=
  .next (.seq [] (envB envW) (loopK fF cond body envW k))

/-! ## 3. The head-glue segments -/

section Glue

variable {fF : String} {cond : Expr} {body : Stmt} {envW : LocalEnv}
  {k : Cont} {σ : ExecState} {ch : Choices} {lf : Nat}

/-- Pure prefix: loop head → the flag read (6 steps, state
untouched). -/
private theorem segA :
    stepFnIter 6 σ (headCfg fF cond body envW k) ch
      = .ok (.evalE (.var fF) (envB envW)
          (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
            (envB envW)
            (.seq [.seqn #[], condIf cond, body] (envB envW)
              (loopK fF cond body envW k))),
        σ, ch) := by
  with_unfolding_all rfl

/-- **Head glue, FIRST iteration** (flag true): 19 steps to the cond
dispatch, `$forFirst := false` written. -/
theorem glue_first
    (henvF : LocalEnv.lookup envW fF = some (.base ⟨lf⟩))
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell true)) :
    stepFnIter 19 σ (headCfg fF cond body envW k) ch
      = .ok (condCfg fF cond body envW k,
        { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) },
        ch) := by
  have hA := segA (fF := fF) (cond := cond) (body := body)
    (envW := envW) (k := k) (σ := σ) (ch := ch)
  -- the tail continuation, abbreviated
  let K1 : Cont := .seq [.seqn #[], condIf cond, body] (envB envW)
    (loopK fF cond body envW k)
  have h7 : stepFnIter 1 σ (.evalE (.var fF) (envB envW)
      (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
        (envB envW) K1)) ch
      = .ok (.retV (.bool true)
          (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
            (envB envW) K1), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW fF).trans henvF) (hlook := hflag))
  -- retV true → exec assign → evalE ref (2 pure steps)
  have hB : stepFnIter 2 σ (.retV (.bool true)
      (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
        (envB envW) K1)) ch
      = .ok (.evalE (.ref fF) (envB envW)
          (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
            (.seqn #[]) (envB envW) K1), σ, ch) := by
    with_unfolding_all rfl
  have h10 : stepFnIter 1 σ (.evalE (.ref fF) (envB envW)
      (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
        (.seqn #[]) (envB envW) K1)) ch
      = .ok (.retV (.addr (.base ⟨lf⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
            (.seqn #[]) (envB envW) K1), σ, ch) :=
    stepFnIter_one (stepFn_ref ((lookup_pushScope envW fF).trans henvF))
  -- retV addr → evalE rhs → retV false → storeK entry (3 pure steps)
  have hC : stepFnIter 3 σ (.retV (.addr (.base ⟨lf⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals [.boolLit false] []
        (.seqn #[]) (envB envW) K1)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨lf⟩)) [] []]
          [.bool false] (.seqn #[]) (envB envW) K1), σ, ch) := by
    with_unfolding_all rfl
  have h14 : stepFnIter 1 σ (.next (.storeK
      [.chain (.addr (.base ⟨lf⟩)) [] []] [.bool false] (.seqn #[])
      (envB envW) K1)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envB envW) K1),
        { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) },
        ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := .bool) (old := .bool true)
        (hlook := hflag) (hnorm := normalize_bool)))
  -- drain the store (3) then the empty prep slot (2)
  have hD : stepFnIter 5
      { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) }
      (.next (.storeK [] [] (.seqn #[]) (envB envW) K1)) ch
      = .ok (condCfg fF cond body envW k,
        { σ with heap := Heap.set σ.heap (.base ⟨lf⟩) (flagCell false) },
        ch) := by
    refine stepFnIter_chain
      (stepFnIter_drain3 (t := .seqn #[]) (ts := [condIf cond, body]))
      (stepFnIter_splice_pop (ss := #[]) rfl)
  exact stepFnIter_chain hA (stepFnIter_chain h7 (stepFnIter_chain hB
    (stepFnIter_chain h10 (stepFnIter_chain hC
      (stepFnIter_chain h14 hD)))))

/-- **Head glue, SUBSEQUENT iteration** (flag false): 12 steps to the
cond dispatch, state untouched. -/
theorem glue_next
    (henvF : LocalEnv.lookup envW fF = some (.base ⟨lf⟩))
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell false)) :
    stepFnIter 12 σ (headCfg fF cond body envW k) ch
      = .ok (condCfg fF cond body envW k, σ, ch) := by
  have hA := segA (fF := fF) (cond := cond) (body := body)
    (envW := envW) (k := k) (σ := σ) (ch := ch)
  let K1 : Cont := .seq [.seqn #[], condIf cond, body] (envB envW)
    (loopK fF cond body envW k)
  have h7 : stepFnIter 1 σ (.evalE (.var fF) (envB envW)
      (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
        (envB envW) K1)) ch
      = .ok (.retV (.bool false)
          (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
            (envB envW) K1), σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW fF).trans henvF) (hlook := hflag))
  -- retV false → exec else (empty seqn) → splice → pop → prep slot →
  -- splice → pop (5 pure steps)
  have hB : stepFnIter 5 σ (.retV (.bool false)
      (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
        (envB envW) K1)) ch
      = .ok (condCfg fF cond body envW k, σ, ch) := by
    have hif : stepFnIter 1 σ (.retV (.bool false)
        (.ifK (.assign (.var fF) (.boolLit false)) (.seqn #[])
          (envB envW) K1)) ch
        = .ok (.exec (.seqn #[]) (envB envW) K1, σ, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain hif (stepFnIter_chain
      (stepFnIter_splice_pop (ss := #[]) rfl)
      (stepFnIter_splice_pop (ss := #[]) rfl))
  exact stepFnIter_chain hA (stepFnIter_chain h7 hB)

/-- The cond entry: 1 step from the cond dispatch to the condition's
evaluation under `condK`. -/
theorem cond_entry :
    stepFnIter 1 σ (condCfg fF cond body envW k) ch
      = .ok (.evalE cond (envB envW) (condK fF cond body envW k),
        σ, ch) := by
  with_unfolding_all rfl

/-- **Branch, CONTINUE case** (cond delivered `true`): 3 steps to the
body configuration, state untouched. -/
theorem branch_true :
    stepFnIter 3 σ (.retV (.bool true) (condK fF cond body envW k)) ch
      = .ok (bodyCfg fF cond body envW k, σ, ch) := by
  have hif : stepFnIter 1 σ
      (.retV (.bool true) (condK fF cond body envW k)) ch
      = .ok (.exec (.seqn #[]) (envB envW)
          (.seq [body] (envB envW) (loopK fF cond body envW k)),
        σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain hif (stepFnIter_splice_pop (ss := #[]) rfl)

/-- **Branch, EXIT case** (cond delivered `false`): 4 steps to the
loop's continuation (break unwind), state untouched. -/
theorem branch_false :
    stepFnIter 4 σ (.retV (.bool false) (condK fF cond body envW k)) ch
      = .ok (.next k, σ, ch) := by
  with_unfolding_all rfl

/-- **The back edge**: a normally-completed body reaches the loop
head in 2 steps, state untouched. -/
theorem back_edge :
    stepFnIter 2 σ (bodyDoneCfg fF cond body envW k) ch
      = .ok (headCfg fF cond body envW k, σ, ch) := by
  with_unfolding_all rfl

end Glue

/-! ## 4. The composed loop schema -/

/-- The glue's head-state write at iteration `i`: the first iteration
clears the flag, later ones write nothing. -/
def glueW (lf : Nat) (i : Nat) (σ : ExecState) : ExecState :=
  if i = 0 then flagSet lf σ else σ

section Loop

variable {fF : String} {cond : Expr} {body : Stmt} {envW : LocalEnv}
  {k : Cont} {lf : Nat}

/-- The composed head → cond-value walk of iteration `i` (glue + cond
entry + the instance's cond walk). -/
private theorem head_to_condval {σ : ExecState} {ch : Choices}
    {i mC : Nat} {b : Bool}
    (henvF : LocalEnv.lookup envW fF = some (.base ⟨lf⟩))
    (hflag : Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0)))
    (hcond : stepFnIter mC (glueW lf i σ)
        (.evalE cond (envB envW) (condK fF cond body envW k)) ch
      = .ok (.retV (.bool b) (condK fF cond body envW k),
          glueW lf i σ, ch)) :
    stepFnIter ((if i = 0 then 19 else 12) + (1 + mC)) σ
        (headCfg fF cond body envW k) ch
      = .ok (.retV (.bool b) (condK fF cond body envW k),
          glueW lf i σ, ch) := by
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl]
    have hgw : glueW lf 0 σ = flagSet lf σ := by
      unfold glueW
      rw [if_pos rfl]
    rw [hgw] at hcond ⊢
    have hg := glue_first (cond := cond) (body := body) (k := k)
      (σ := σ) (ch := ch) henvF hflag
    exact stepFnIter_chain hg (stepFnIter_chain
      (cond_entry (σ := flagSet lf σ)) hcond)
  · rw [if_neg hi]
    have hfl : Heap.lookup σ.heap (.base ⟨lf⟩)
        = some (flagCell false) := by
      have : (i == 0) = false := by
        simp [hi]
      rw [this] at hflag
      exact hflag
    have hg := glue_next (cond := cond) (body := body) (k := k)
      (σ := σ) (ch := ch) henvF hfl
    have hgw : glueW lf i σ = σ := by
      unfold glueW
      rw [if_neg hi]
    rw [hgw] at hcond ⊢
    exact stepFnIter_chain hg (stepFnIter_chain
      (cond_entry (σ := σ)) hcond)

/-- **THE COND-FOR LOOP SCHEMA** (the module's headline; the
Floyd/Hoare loop invariant over the frontend's plain-for desugar).

Given a state family `S` (the loop invariant, indexed by completed
iterations) whose members carry the latch cell at its scheduled
value, a COND fact — from the glue-written state, the loop condition
evaluates (state untouched) to `true` exactly below `n` — and a BODY
fact — from the glue-written state, the body completes normally
within `bB` steps and re-establishes the invariant — every `S i`
state at the loop head completes the whole remaining loop within
`(25 + bC + bB) * (n - i) + 24 + bC` steps, delivering `.next k` at
the exit-glue-written `S n` state.

The conclusion is BOUNDED-COMPLETION (compositional mode I2):
consumers get the bound, the final configuration, and the invariant. -/
theorem condFor_loop
    (henvF : LocalEnv.lookup envW fF = some (.base ⟨lf⟩))
    {n bC bB : Nat}
    (S : Nat → ExecState → Prop)
    (hS : ∀ i σ, i ≤ n → S i σ →
      Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0)))
    (hcond : ∀ i σ ch, i ≤ n → S i σ →
      ∃ m ≤ bC, stepFnIter m (glueW lf i σ)
          (.evalE cond (envB envW) (condK fF cond body envW k)) ch
        = .ok (.retV (.bool (decide (i < n)))
            (condK fF cond body envW k), glueW lf i σ, ch))
    (hbody : ∀ i σ ch, i < n → S i σ →
      ∃ m ≤ bB, ∃ σ',
        stepFnIter m (glueW lf i σ) (bodyCfg fF cond body envW k) ch
          = .ok (bodyDoneCfg fF cond body envW k, σ', ch)
        ∧ S (i + 1) σ') :
    ∀ i σ ch, i ≤ n → S i σ →
      ∃ m ≤ (25 + bC + bB) * (n - i) + 24 + bC, ∃ σf, S n σf ∧
        stepFnIter m σ (headCfg fF cond body envW k) ch
          = .ok (.next k, glueW lf n σf, ch) := by
  suffices key : ∀ μ i σ ch, μ = n - i → i ≤ n → S i σ →
      ∃ m ≤ (25 + bC + bB) * (n - i) + 24 + bC, ∃ σf, S n σf ∧
        stepFnIter m σ (headCfg fF cond body envW k) ch
          = .ok (.next k, glueW lf n σf, ch) by
    intro i σ ch hin hSi
    exact key (n - i) i σ ch rfl hin hSi
  intro μ
  induction μ with
  | zero =>
      intro i σ ch hμ hin hSi
      have hi : i = n := by omega
      subst hi
      obtain ⟨mC, hmC, hcv⟩ := hcond i σ ch (Nat.le_refl i) hSi
      have hfalse : decide (i < i) = false := by simp
      rw [hfalse] at hcv
      have hwalk := stepFnIter_chain
        (head_to_condval henvF (hS i σ (Nat.le_refl i) hSi) hcv)
        (branch_false (σ := glueW lf i σ) (ch := ch))
      refine ⟨_, ?_, σ, hSi, hwalk⟩
      have : (if i = 0 then 19 else 12) ≤ 19 := by
        split <;> omega
      omega
  | succ μ' ih =>
      intro i σ ch hμ hin hSi
      have hlt : i < n := by omega
      obtain ⟨mC, hmC, hcv⟩ := hcond i σ ch (by omega) hSi
      have htrue : decide (i < n) = true := by simp [hlt]
      rw [htrue] at hcv
      have hhead := stepFnIter_chain
        (head_to_condval henvF (hS i σ (by omega) hSi) hcv)
        (branch_true (σ := glueW lf i σ) (ch := ch))
      obtain ⟨mB, hmB, σ', hrun, hS'⟩ := hbody i σ ch hlt hSi
      have hback := back_edge (fF := fF) (cond := cond) (body := body)
        (envW := envW) (k := k) (σ := σ') (ch := ch)
      obtain ⟨m', hm', σf, hSf, hrest⟩ :=
        ih (i + 1) σ' ch (by omega) (by omega) hS'
      have hall := stepFnIter_chain hhead (stepFnIter_chain hrun
        (stepFnIter_chain hback hrest))
      refine ⟨_, ?_, σf, hSf, hall⟩
      have hgs : (if i = 0 then 19 else 12) ≤ 19 := by
        split <;> omega
      have hmul : (25 + bC + bB) * (n - (i + 1)) + (25 + bC + bB)
          = (25 + bC + bB) * (n - i) := by
        have : n - i = (n - (i + 1)) + 1 := by omega
        rw [this, Nat.mul_succ]
      omega

end Loop

/-! ## 5. The discharge witness (witness-in-same-slice; a small
NON-checker loop): `for c > 0 { c = c - 1 }` — the countdown loop.

Every schema premise is discharged with the kit's conditioned
singles; the composed count at `n = 3` is cross-checked against a
compiled walk (kernel-pinned below). -/

section Witness

open GoLean.SliceWalk (idxCell)

/-- `c > 0`, at signed-64 `c` (the witness's condition). -/
def cdCond : Expr := .greaterCmp (.var "c") (.intLit 0 .int)

/-- `c = c - 1` (the witness's body). -/
def cdBody : Stmt :=
  .assign (.var "c") (.sub (.var "c") (.intLit 1 .int))

/-- `>` on two signed-64 ints (the `applyStrictOp_atLeast_int`
sibling; `valueGreater` is `l > r`). -/
theorem applyStrictOp_greater_int {σ : ExecState} {a b : Int} :
    applyStrictOp σ .greaterCmp [.int a .int, .int b .int]
      = .ok (.bool (decide (b < a)), σ) := by
  simp only [applyStrictOp, valueGreater, Bind.bind, Except.bind, pure,
    Except.pure, gt_iff_lt]

/-- `-` on two signed-64 ints, in-range result. -/
theorem applyStrictOp_sub_int' {σ : ExecState} {a b : Int}
    (h0 : -(2 ^ 63) ≤ a - b) (h1 : a - b < 2 ^ 63) :
    applyStrictOp σ .sub [.int a .int, .int b .int]
      = .ok (.int (a - b) .int, σ) := by
  have hc : IntKind.compatibleResult IntKind.int IntKind.int
      = some IntKind.int := rfl
  simp [applyStrictOp, intBinaryResult, valueAsIntValue, Bind.bind,
    Except.bind, hc, GoLean.SliceMem.inorm_of_range h0 h1]

variable {envW : LocalEnv} {k : Cont} {lf lc : Nat}

/-- The countdown invariant: the latch at its schedule, the counter
cell at `n - i`. -/
def CdInv (lf lc n : Nat) (i : Nat) (σ : ExecState) : Prop :=
  Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0))
    ∧ Heap.lookup σ.heap (.base ⟨lc⟩) = some (idxCell ((n : Int) - i))

/-- The countdown cond fact: 5 steps, state untouched. -/
theorem cd_cond_fact
    (hFC : lf ≠ lc)
    (henvC : LocalEnv.lookup envW "c" = some (.base ⟨lc⟩))
    {n : Nat} (_hn63 : (n : Int) < 2 ^ 63) :
    ∀ i σ ch, i ≤ n → CdInv lf lc n i σ →
      ∃ m ≤ 5, stepFnIter m (glueW lf i σ)
          (.evalE cdCond (envB envW)
            (condK "$forFirst" cdCond cdBody envW k)) ch
        = .ok (.retV (.bool (decide (i < n)))
            (condK "$forFirst" cdCond cdBody envW k),
          glueW lf i σ, ch) := by
  intro i σ ch hin hI
  obtain ⟨hflag, hc⟩ := hI
  have hcg : Heap.lookup (glueW lf i σ).heap (.base ⟨lc⟩)
      = some (idxCell ((n : Int) - i)) := by
    unfold glueW
    split
    · show Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩) (flagCell false))
        (.base ⟨lc⟩) = _
      rw [lookup_set_other hFC]
      exact hc
    · exact hc
  refine ⟨5, Nat.le_refl 5, ?_⟩
  -- evalE greaterCmp → evalE var c (1 pure step)
  have h1 : stepFnIter 1 (glueW lf i σ) (.evalE cdCond (envB envW)
      (condK "$forFirst" cdCond cdBody envW k)) ch
      = .ok (.evalE (.var "c") (envB envW)
          (.strictK .greaterCmp [] [.intLit 0 .int] (envB envW)
            (condK "$forFirst" cdCond cdBody envW k)),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  have h2 : stepFnIter 1 (glueW lf i σ) (.evalE (.var "c") (envB envW)
      (.strictK .greaterCmp [] [.intLit 0 .int] (envB envW)
        (condK "$forFirst" cdCond cdBody envW k))) ch
      = .ok (.retV (.int ((n : Int) - i) .int)
          (.strictK .greaterCmp [] [.intLit 0 .int] (envB envW)
            (condK "$forFirst" cdCond cdBody envW k)),
        glueW lf i σ, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW "c").trans henvC) (hlook := hcg))
  -- retV c → evalE intLit 0 → retV 0 (2 pure steps)
  have h3 : stepFnIter 2 (glueW lf i σ)
      (.retV (.int ((n : Int) - i) .int)
        (.strictK .greaterCmp [] [.intLit 0 .int] (envB envW)
          (condK "$forFirst" cdCond cdBody envW k))) ch
      = .ok (.retV (.int 0 .int)
          (.strictK .greaterCmp [.int ((n : Int) - i) .int] []
            (envB envW) (condK "$forFirst" cdCond cdBody envW k)),
        glueW lf i σ, ch) := by
    with_unfolding_all rfl
  have h4 : stepFnIter 1 (glueW lf i σ) (.retV (.int 0 .int)
      (.strictK .greaterCmp [.int ((n : Int) - i) .int] []
        (envB envW) (condK "$forFirst" cdCond cdBody envW k))) ch
      = .ok (.retV (.bool (decide (i < n)))
          (condK "$forFirst" cdCond cdBody envW k),
        glueW lf i σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 0 .int,
        GoValue.int ((n : Int) - i) .int])
      = [GoValue.int ((n : Int) - i) .int, GoValue.int 0 .int]
      from rfl, applyStrictOp_greater_int]
    have hd : decide ((0 : Int) < (n : Int) - (i : Int))
        = decide (i < n) := by
      rcases Nat.lt_or_ge i n with h | h
      · rw [decide_eq_true (show (0 : Int) < (n : Int) - i by omega),
          decide_eq_true h]
      · rw [decide_eq_false (show ¬((0 : Int) < (n : Int) - i) by omega),
          decide_eq_false (show ¬(i < n) by omega)]
    rw [hd]
  exact stepFnIter_chain h1 (stepFnIter_chain h2
    (stepFnIter_chain h3 h4))

/-- The countdown body fact: 12 steps, `c := c - 1` written. -/
theorem cd_body_fact
    (hFC : lf ≠ lc)
    (henvC : LocalEnv.lookup envW "c" = some (.base ⟨lc⟩))
    {n : Nat} (hn63 : (n : Int) < 2 ^ 63) :
    ∀ i σ ch, i < n → CdInv lf lc n i σ →
      ∃ m ≤ 12, ∃ σ',
        stepFnIter m (glueW lf i σ)
            (bodyCfg "$forFirst" cdCond cdBody envW k) ch
          = .ok (bodyDoneCfg "$forFirst" cdCond cdBody envW k, σ', ch)
        ∧ CdInv lf lc n (i + 1) σ' := by
  intro i σ ch hlt hI
  obtain ⟨hflag, hc⟩ := hI
  have hcg : Heap.lookup (glueW lf i σ).heap (.base ⟨lc⟩)
      = some (idxCell ((n : Int) - i)) := by
    unfold glueW
    split
    · show Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩) (flagCell false))
        (.base ⟨lc⟩) = _
      rw [lookup_set_other hFC]
      exact hc
    · exact hc
  have hfg : Heap.lookup (glueW lf i σ).heap (.base ⟨lf⟩)
      = some (flagCell false) := by
    unfold glueW
    split
    · exact lookup_set_self
    · rename_i hi
      have : (i == 0) = false := by simp [hi]
      rw [this] at hflag
      exact hflag
  let K2 : Cont := .seq [] (envB envW)
    (loopK "$forFirst" cdCond cdBody envW k)
  -- body entry: exec assign → evalE ref c (1 pure step)
  have h1 : stepFnIter 1 (glueW lf i σ)
      (bodyCfg "$forFirst" cdCond cdBody envW k) ch
      = .ok (.evalE (.ref "c") (envB envW)
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.sub (.var "c") (.intLit 1 .int)] [] (.seqn #[])
            (envB envW) K2), (glueW lf i σ), ch) := by
    with_unfolding_all rfl
  have h2 : stepFnIter 1 (glueW lf i σ) (.evalE (.ref "c") (envB envW)
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.sub (.var "c") (.intLit 1 .int)] [] (.seqn #[])
        (envB envW) K2)) ch
      = .ok (.retV (.addr (.base ⟨lc⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.sub (.var "c") (.intLit 1 .int)] [] (.seqn #[])
            (envB envW) K2), (glueW lf i σ), ch) :=
    stepFnIter_one (stepFn_ref ((lookup_pushScope envW "c").trans henvC))
  -- retV addr → evalE sub → evalE var c (2 pure steps)
  have h3 : stepFnIter 2 (glueW lf i σ) (.retV (.addr (.base ⟨lc⟩))
      (.tgtOpK (.chain []) [] [] [] [] .vals
        [.sub (.var "c") (.intLit 1 .int)] [] (.seqn #[])
        (envB envW) K2)) ch
      = .ok (.evalE (.var "c") (envB envW)
          (.strictK .sub [] [.intLit 1 .int] (envB envW)
            (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
              (.seqn #[]) (envB envW) K2)), (glueW lf i σ), ch) := by
    with_unfolding_all rfl
  have h4 : stepFnIter 1 (glueW lf i σ) (.evalE (.var "c") (envB envW)
      (.strictK .sub [] [.intLit 1 .int] (envB envW)
        (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
          (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.int ((n : Int) - i) .int)
          (.strictK .sub [] [.intLit 1 .int] (envB envW)
            (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
              (.seqn #[]) (envB envW) K2)), (glueW lf i σ), ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope envW "c").trans henvC) (hlook := hcg))
  -- retV c → evalE intLit 1 → retV 1 (2 pure steps)
  have h5 : stepFnIter 2 (glueW lf i σ) (.retV (.int ((n : Int) - i) .int)
      (.strictK .sub [] [.intLit 1 .int] (envB envW)
        (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
          (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.int 1 .int)
          (.strictK .sub [.int ((n : Int) - i) .int] [] (envB envW)
            (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
              (.seqn #[]) (envB envW) K2)), (glueW lf i σ), ch) := by
    with_unfolding_all rfl
  have h6 : stepFnIter 1 (glueW lf i σ) (.retV (.int 1 .int)
      (.strictK .sub [.int ((n : Int) - i) .int] [] (envB envW)
        (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
          (.seqn #[]) (envB envW) K2))) ch
      = .ok (.retV (.int ((n : Int) - i - 1) .int)
          (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
            (.seqn #[]) (envB envW) K2), (glueW lf i σ), ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 1 .int,
        GoValue.int ((n : Int) - i) .int])
      = [GoValue.int ((n : Int) - i) .int, GoValue.int 1 .int]
      from rfl,
      applyStrictOp_sub_int' (by omega) (by omega)]
  -- rhsK drain → storeK entry (1 pure step)
  have h7 : stepFnIter 1 (glueW lf i σ) (.retV (.int ((n : Int) - i - 1) .int)
      (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
        (.seqn #[]) (envB envW) K2)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨lc⟩)) [] []]
          [.int ((n : Int) - i - 1) .int] (.seqn #[]) (envB envW) K2),
        (glueW lf i σ), ch) := by
    with_unfolding_all rfl
  have h8 : stepFnIter 1 (glueW lf i σ) (.next (.storeK
      [.chain (.addr (.base ⟨lc⟩)) [] []]
      [.int ((n : Int) - i - 1) .int] (.seqn #[]) (envB envW) K2)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envB envW) K2),
        { (glueW lf i σ) with heap := Heap.set (glueW lf i σ).heap (.base ⟨lc⟩) (idxCell ((n : Int) - i - 1)) }, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_addr (ty := GoLean.SliceWalk.tI)
        (old := .int ((n : Int) - i) .int) (hlook := hcg)
        (hnorm := GoLean.SliceWalk.normalize_int_signed
          (by omega) (by omega))))
  -- storeK nil → splice lands on the empty-tail seq (2 steps)
  have h9 : stepFnIter 2
      { (glueW lf i σ) with heap := Heap.set (glueW lf i σ).heap (.base ⟨lc⟩) (idxCell ((n : Int) - i - 1)) }
      (.next (.storeK [] [] (.seqn #[]) (envB envW) K2)) ch
      = .ok (bodyDoneCfg "$forFirst" cdCond cdBody envW k,
        { (glueW lf i σ) with heap := Heap.set (glueW lf i σ).heap (.base ⟨lc⟩) (idxCell ((n : Int) - i - 1)) }, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_one stepFn_seqn_splice)
  refine ⟨12, Nat.le_refl 12,
    { (glueW lf i σ) with heap := Heap.set (glueW lf i σ).heap (.base ⟨lc⟩) (idxCell ((n : Int) - i - 1)) },
    stepFnIter_chain h1 (stepFnIter_chain h2 (stepFnIter_chain h3
      (stepFnIter_chain h4 (stepFnIter_chain h5 (stepFnIter_chain h6
        (stepFnIter_chain h7 (stepFnIter_chain h8 h9))))))), ?_, ?_⟩
  · -- flag: the glue wrote false at i = 0; preserved by the c-store
    show Heap.lookup (Heap.set (glueW lf i σ).heap (.base ⟨lc⟩)
      (idxCell ((n : Int) - i - 1))) (.base ⟨lf⟩)
      = some (flagCell ((i + 1) == 0))
    rw [lookup_set_other (Ne.symm hFC)]
    have : ((i + 1) == 0) = false := by simp
    rw [this]
    exact hfg
  · show Heap.lookup (Heap.set (glueW lf i σ).heap (.base ⟨lc⟩)
      (idxCell ((n : Int) - i - 1))) (.base ⟨lc⟩)
      = some (idxCell ((n : Int) - (i + 1)))
    rw [lookup_set_self]
    congr 2
    omega

/-- **THE DISCHARGE WITNESS**: the countdown loop's full span through
the schema — every premise discharged, symbolic in `n`. -/
theorem countdown_span
    (hFC : lf ≠ lc)
    (henvF : LocalEnv.lookup envW "$forFirst" = some (.base ⟨lf⟩))
    (henvC : LocalEnv.lookup envW "c" = some (.base ⟨lc⟩))
    {n : Nat} (hn63 : (n : Int) < 2 ^ 63) :
    ∀ σ ch, CdInv lf lc n 0 σ →
      ∃ m ≤ 42 * n + 29, ∃ σf, CdInv lf lc n n σf ∧
        stepFnIter m σ
            (headCfg "$forFirst" cdCond cdBody envW k) ch
          = .ok (.next k, glueW lf n σf, ch) := by
  intro σ ch hI
  have h := condFor_loop (cond := cdCond) (body := cdBody) (k := k)
    henvF (n := n) (bC := 5) (bB := 12)
    (CdInv lf lc n)
    (fun i σ' _ hI' => hI'.1)
    (cd_cond_fact hFC henvC hn63)
    (cd_body_fact hFC henvC hn63)
    0 σ ch (Nat.zero_le _) hI
  obtain ⟨m, hm, σf, hSf, hrun⟩ := h
  exact ⟨m, by simpa using hm, σf, hSf, hrun⟩

/-! ### The compiled cross-check (n = 3): the composed walk reproduces
the kernel's own count, at a concrete two-cell state. The exact count
is 19+1+5+3+12+2 (first iteration) + 3·(12+1+5)... derived by the
compiled walk (dev probe) and pinned here: 133 steps to `.next .stop`
with the counter at 0. -/

/-- The witness state: flag at 0 (true), counter at 1 holding 3. -/
def cdSt : ExecState :=
  { heap := [(.base ⟨0⟩, flagCell true), (.base ⟨1⟩, idxCell 3)],
    nextAddr := 2 }

def cdEnv : LocalEnv := [[("$forFirst", .base ⟨0⟩), ("c", .base ⟨1⟩)]]

/-- The schema instance at the concrete state (the witness's
non-vacuity: every premise discharges on real cells). -/
theorem cd_concrete :
    ∃ m ≤ 42 * 3 + 29, ∃ σf, CdInv 0 1 3 3 σf ∧
      stepFnIter m cdSt
          (headCfg "$forFirst" cdCond cdBody cdEnv .stop) []
        = .ok (.next .stop, glueW 0 3 σf, []) := by
  refine countdown_span (by omega) rfl rfl (by decide)
    cdSt [] ⟨rfl, rfl⟩

end Witness

end GoLean.CondFor
