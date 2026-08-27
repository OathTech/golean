import GoLeanProofs.FuelMeasure

/-!
# The Spec judgment (W1 — the spec former; design note
`docs/2026-08-27_w1-judgment-design.md` §1–2, §5)

The program logic's judgment, in the two forms of
`docs/2026-08-27_proof-structure-explained.md` §1:

* `StmtSpec P c Q` — the statement-span triple: from `.exec c env k`
  to `.next k` with the caller's `k` untouched (termination of the
  span detected by the machine's own frame/continuation discipline),
  ∀-state over the precondition, ∀ env k (continuation-parametric),
  ∀ ch (demonic tape), ∃ n (fuel reified), the consumed tape a
  suffix.
* `CallSpec P fid vals v Q` — the CALL-SPAN triple (resultless
  form): from the drained call configuration
  `.retV v (.callArgsK fid [] vals [] env k)` — the machine's shape
  with argument list `vals ++ [v]` — through the frame arm
  (StepFn.lean:676) to the post-store configuration `.next k`.
  The result-bearing shape (the tgtOpK caller-target walk,
  StepFn.lean:684-694) and the nullary entry are SEALED REFUSALS
  below until a consumer demands them.

`B`-bounded variants (`n ≤ B`, the bound a parameter — never a
subject-run constant in a statement) carry the totality direction.

Composition rules: consequence, the sequence rule
(`StmtSpec.seqn_pair` — at the machine's own `seqCont` splicing,
both the merge and the push shape), and the call rule
(`CallSpec.consume` at drained-call points mid-span;
`stmtSpec_call` at the statement level with a passive
argument-evaluation premise). LINEAGE (design note §1–2): Hoare
triples over a fueled small-step machine; the
continuation-parametric encoding is the evaluation-context/CPS
presentation; ∀ ch is demonic nondeterminism over the reified
tape; the call rule is Hoare's procedure rule with adaptation by
consequence.

Non-vacuity: the judgment's honest instances are the W1 pilot's
(`Specs/RaftPilot/` — Leg A's becomeFollower `CallSpec`, and the tracked
open-tail window examples), stated as pilot instances per the
charter's carve-out. Audit pins: `Audit/W1.lean`.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

namespace GoLean.Spec

/-! ## The judgment -/

/-- **The statement-span triple** `{P} c {Q}`: from `.exec c env k`,
every `P`-state at every continuation and every choice stream reaches
`.next k` (the caller's `k` untouched — the machine's own termination
signal for the span) in some number of steps, ending in a `Q`-state
with the remaining tape a suffix of the input tape.

The precondition is over `(env, σ)`: at statement granularity the
environment is the span's register file (design note §1, recorded
delta from the §1 spelling — which is the env-constant special
case). -/
def StmtSpec (P : LocalEnv → ExecState → Prop) (c : Stmt)
    (Q : LocalEnv → ExecState → Prop) : Prop :=
  ∀ env σ, P env σ → ∀ (k : Cont) (ch : Choices),
    ∃ (n : Nat) (σ' : ExecState) (ch' : Choices),
      stepFnIter n σ (.exec c env k) ch = .ok (.next k, σ', ch')
      ∧ Q env σ' ∧ ch' <:+ ch

/-- **The call-span triple** (resultless form): from the drained call
configuration of `fid` at argument list `vals ++ [v]` to the
post-store configuration `.next k` — continuation-parametric
(∀ env k: the caller's env is inert in a resultless span), demonic in
the tape. -/
def CallSpec (P : ExecState → Prop) (fid : FuncId)
    (vals : List GoValue) (v : GoValue) (Q : ExecState → Prop) : Prop :=
  ∀ σ, P σ → ∀ (env : LocalEnv) (k : Cont) (ch : Choices),
    ∃ (n : Nat) (σ' : ExecState) (ch' : Choices),
      stepFnIter n σ (.retV v (.callArgsK fid [] vals [] env k)) ch
        = .ok (.next k, σ', ch')
      ∧ Q σ' ∧ ch' <:+ ch

/-- **The result-bearing call-span triple** (callee-local form —
W3 U3.1-F, the consumer the sealed refusal below awaited: the
raftLog/unstable/storage read family all return values). The span
runs from the drained call configuration — the caller-target `plans`
riding INERTLY in the continuation — to the RETURN-ARRIVAL
configuration `.returning (.frame plans env rlocs [] k false)`:
one machine step BEFORE the result read (`loadMany`) and the
caller-side `tgtOpK` target-operand walk, so the span stays
callee-local (the sealed tgtOpK-inclusive form stays sealed). The
postcondition speaks the result VALUES through `loadMany` at the
machine's own pinned result locations, delivered as an equation the
call site's next step consumes definitionally.

∀ plans/env/k (target- and continuation-parametric: the span never
inspects them — the open-tail route extends to `plans`), ∀ ch
(demonic), ∃ n. Non-wrapper callees only (`false` pinned in the
frame): every subject library function; wrapper frames are the plug
premises' excluded class.

LINEAGE: Hoare's procedure rule with result substitution, at the
CPS/evaluation-context presentation — the resultless `CallSpec`'s
sibling with the machine's own frame discipline carrying the
results; no new mechanism class. -/
def CallSpecR (P : ExecState → Prop) (fid : FuncId)
    (vals : List GoValue) (v : GoValue)
    (Q : ExecState → List GoValue → Prop) : Prop :=
  ∀ σ, P σ → ∀ (plans : List (TargetShape × List Expr))
      (env : LocalEnv) (k : Cont) (ch : Choices),
    ∃ (n : Nat) (σ' : ExecState) (rlocs : List Loc)
      (vs : List GoValue) (ch' : Choices),
      stepFnIter n σ (.retV v (.callArgsK fid plans vals [] env k)) ch
        = .ok (.returning (.frame plans env rlocs [] k false), σ', ch')
      ∧ loadMany σ' rlocs = .ok vs
      ∧ Q σ' vs ∧ ch' <:+ ch

theorem CallSpecR.conseq {P P' : ExecState → Prop} {fid : FuncId}
    {vals : List GoValue} {v : GoValue}
    {Q Q' : ExecState → List GoValue → Prop}
    (h : CallSpecR P fid vals v Q)
    (hpre : ∀ σ, P' σ → P σ)
    (hpost : ∀ σ vs, Q σ vs → Q' σ vs) : CallSpecR P' fid vals v Q' := by
  intro σ hP plans env k ch
  obtain ⟨n, σ', rlocs, vs, ch', hrun, hload, hQ, hsuf⟩ :=
    h σ (hpre σ hP) plans env k ch
  exact ⟨n, σ', rlocs, vs, ch', hrun, hload, hpost σ' vs hQ, hsuf⟩

/-- The definitional hop at a drained result-bearing call
configuration — the form a caller-site span proof consumes mid-walk
(then crosses the frame-exit step itself with the `loadMany`
equation and its OWN target-operand walk). -/
theorem CallSpecR.consume {P : ExecState → Prop} {fid : FuncId}
    {vals : List GoValue} {v : GoValue}
    {Q : ExecState → List GoValue → Prop} {σ : ExecState}
    (h : CallSpecR P fid vals v Q) (hP : P σ)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    ∃ (n : Nat) (σ' : ExecState) (rlocs : List Loc)
      (vs : List GoValue) (ch' : Choices),
      stepFnIter n σ (.retV v (.callArgsK fid plans vals [] env k)) ch
        = .ok (.returning (.frame plans env rlocs [] k false), σ', ch')
      ∧ loadMany σ' rlocs = .ok vs
      ∧ Q σ' vs ∧ ch' <:+ ch := h σ hP plans env k ch

/-- The bounded statement-span triple (`n ≤ B`; the totality-side
form — `B` is a parameter, never a subject-run constant inside a
statement). -/
def StmtSpecB (P : LocalEnv → ExecState → Prop) (c : Stmt)
    (Q : LocalEnv → ExecState → Prop) (B : Nat) : Prop :=
  ∀ env σ, P env σ → ∀ (k : Cont) (ch : Choices),
    ∃ n ≤ B, ∃ (σ' : ExecState) (ch' : Choices),
      stepFnIter n σ (.exec c env k) ch = .ok (.next k, σ', ch')
      ∧ Q env σ' ∧ ch' <:+ ch

/-- The bounded call-span triple. -/
def CallSpecB (P : ExecState → Prop) (fid : FuncId)
    (vals : List GoValue) (v : GoValue) (Q : ExecState → Prop)
    (B : Nat) : Prop :=
  ∀ σ, P σ → ∀ (env : LocalEnv) (k : Cont) (ch : Choices),
    ∃ n ≤ B, ∃ (σ' : ExecState) (ch' : Choices),
      stepFnIter n σ (.retV v (.callArgsK fid [] vals [] env k)) ch
        = .ok (.next k, σ', ch')
      ∧ Q σ' ∧ ch' <:+ ch

theorem StmtSpecB.toSpec {P Q : LocalEnv → ExecState → Prop} {c : Stmt}
    {B : Nat} (h : StmtSpecB P c Q B) : StmtSpec P c Q := by
  intro env σ hP k ch
  obtain ⟨n, _, σ', ch', hrun, hQ, hsuf⟩ := h env σ hP k ch
  exact ⟨n, σ', ch', hrun, hQ, hsuf⟩

theorem CallSpecB.toSpec {P Q : ExecState → Prop} {fid : FuncId}
    {vals : List GoValue} {v : GoValue} {B : Nat}
    (h : CallSpecB P fid vals v Q B) : CallSpec P fid vals v Q := by
  intro σ hP env k ch
  obtain ⟨n, _, σ', ch', hrun, hQ, hsuf⟩ := h σ hP env k ch
  exact ⟨n, σ', ch', hrun, hQ, hsuf⟩

/-- Bound weakening. -/
theorem StmtSpecB.mono {P Q : LocalEnv → ExecState → Prop} {c : Stmt}
    {B B' : Nat} (hle : B ≤ B') (h : StmtSpecB P c Q B) :
    StmtSpecB P c Q B' := by
  intro env σ hP k ch
  obtain ⟨n, hn, rest⟩ := h env σ hP k ch
  exact ⟨n, Nat.le_trans hn hle, rest⟩

theorem CallSpecB.mono {P Q : ExecState → Prop} {fid : FuncId}
    {vals : List GoValue} {v : GoValue} {B B' : Nat} (hle : B ≤ B')
    (h : CallSpecB P fid vals v Q B) : CallSpecB P fid vals v Q B' := by
  intro σ hP env k ch
  obtain ⟨n, hn, rest⟩ := h σ hP env k ch
  exact ⟨n, Nat.le_trans hn hle, rest⟩

/-! ## Consequence -/

theorem StmtSpec.conseq {P P' Q Q' : LocalEnv → ExecState → Prop}
    {c : Stmt} (h : StmtSpec P c Q)
    (hpre : ∀ env σ, P' env σ → P env σ)
    (hpost : ∀ env σ, Q env σ → Q' env σ) : StmtSpec P' c Q' := by
  intro env σ hP k ch
  obtain ⟨n, σ', ch', hrun, hQ, hsuf⟩ := h env σ (hpre env σ hP) k ch
  exact ⟨n, σ', ch', hrun, hpost env σ' hQ, hsuf⟩

theorem CallSpec.conseq {P P' Q Q' : ExecState → Prop} {fid : FuncId}
    {vals : List GoValue} {v : GoValue} (h : CallSpec P fid vals v Q)
    (hpre : ∀ σ, P' σ → P σ) (hpost : ∀ σ, Q σ → Q' σ) :
    CallSpec P' fid vals v Q' := by
  intro σ hP env k ch
  obtain ⟨n, σ', ch', hrun, hQ, hsuf⟩ := h σ (hpre σ hP) env k ch
  exact ⟨n, σ', ch', hrun, hpost σ' hQ, hsuf⟩

/-! ## The sequence rule -/

/-- The `seqCont` decomposition every sequencing proof runs on: for
ANY continuation `k`, splicing `[c₁, c₂]` yields a two-statement
sequence continuation whose tail finishes to `.next k` in 0 or 1
machine steps (0 when the splice MERGED into a same-env sequence,
1 for the pushed empty-sequence pop). -/
theorem seqCont_pair_decomp (c₁ c₂ : Stmt) (env : LocalEnv) (k : Cont) :
    ∃ (ts : List Stmt) (kt : Cont),
      seqCont [c₁, c₂] env k = .seq (c₁ :: c₂ :: ts) env kt
      ∧ ∀ (σ : ExecState) (ch : Choices), ∃ m ≤ 1,
          stepFnIter m σ (.next (.seq ts env kt)) ch
            = .ok (.next k, σ, ch) := by
  cases k
  case seq rest env' k' =>
    by_cases henv : env' = env
    · subst henv
      exact ⟨rest, k', by simp [seqCont], fun σ ch => ⟨0, Nat.zero_le 1, rfl⟩⟩
    · exact ⟨[], .seq rest env' k', by simp [seqCont, henv],
        fun σ ch => ⟨1, Nat.le_refl 1, stepFnIter_one rfl⟩⟩
  all_goals exact ⟨[], _, rfl, fun σ ch => ⟨1, Nat.le_refl 1,
    stepFnIter_one rfl⟩⟩

/-- **The sequence rule** at the frontend's two-statement `seqn`
shape: `{P} c₁ {R}` and `{R} c₂ {Q}` give `{P} c₁; c₂ {Q}`. Proved at
the machine's own `seqCont` splicing — BOTH the merge shape (the
governing continuation is a same-env sequence) and the push shape.
The n-ary sibling is built when a second consumer demands it (the
promotion ledger's ≥2 rule). -/
theorem StmtSpec.seqn_pair {P R Q : LocalEnv → ExecState → Prop}
    {c₁ c₂ : Stmt} (h₁ : StmtSpec P c₁ R) (h₂ : StmtSpec R c₂ Q) :
    StmtSpec P (.seqn #[c₁, c₂]) Q := by
  intro env σ hP k ch
  obtain ⟨ts, kt, hK, hfin⟩ := seqCont_pair_decomp c₁ c₂ env k
  -- step 1: the seqn splice
  have hstep1 : stepFn σ (.exec (.seqn #[c₁, c₂]) env k) ch
      = .ok (.next (.seq (c₁ :: c₂ :: ts) env kt), σ, ch) := by
    have hraw : stepFn σ (.exec (.seqn #[c₁, c₂]) env k) ch
        = .ok (.next (seqCont [c₁, c₂] env k), σ, ch) := rfl
    rw [hraw, hK]
  -- step 2: pop c₁
  have hstep2 : stepFn σ (.next (.seq (c₁ :: c₂ :: ts) env kt)) ch
      = .ok (.exec c₁ env (.seq (c₂ :: ts) env kt), σ, ch) := rfl
  -- c₁'s span at the spliced continuation
  obtain ⟨n₁, σ₁, ch₁, hrun₁, hR, hsuf₁⟩ :=
    h₁ env σ hP (.seq (c₂ :: ts) env kt) ch
  -- pop c₂
  have hstep3 : stepFn σ₁ (.next (.seq (c₂ :: ts) env kt)) ch₁
      = .ok (.exec c₂ env (.seq ts env kt), σ₁, ch₁) := rfl
  -- c₂'s span
  obtain ⟨n₂, σ₂, ch₂, hrun₂, hQ, hsuf₂⟩ :=
    h₂ env σ₁ hR (.seq ts env kt) ch₁
  -- the finisher
  obtain ⟨m, _, hfin'⟩ := hfin σ₂ ch₂
  refine ⟨1 + 1 + n₁ + 1 + n₂ + m, σ₂, ch₂, ?_, hQ, hsuf₂.trans hsuf₁⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_one hstep1) (stepFnIter_one hstep2)) hrun₁)
    (stepFnIter_one hstep3)) hrun₂) hfin'

/-! ## The call rule -/

/-- The definitional hop at a drained call configuration — the form a
larger span proof consumes mid-walk (design note §2 layer (i)). -/
theorem CallSpec.consume {P Q : ExecState → Prop} {fid : FuncId}
    {vals : List GoValue} {v : GoValue} {σ : ExecState}
    (h : CallSpec P fid vals v Q) (hP : P σ) (env : LocalEnv) (k : Cont)
    (ch : Choices) :
    ∃ (n : Nat) (σ' : ExecState) (ch' : Choices),
      stepFnIter n σ (.retV v (.callArgsK fid [] vals [] env k)) ch
        = .ok (.next k, σ', ch')
      ∧ Q σ' ∧ ch' <:+ ch := h σ hP env k ch

/-- **The statement-level call rule** (resultless call, PASSIVE
arguments): the argument-evaluation premise `hargs` carries the
caller-side segment from the call statement to the drained
configuration — state- and tape-passive, the shape of variable/field
reads (a site with effectful or choice-consuming arguments composes
manually via `stepFnIter_chain` + `CallSpec.consume`; the recorded
escape, design note §5). The callee's `CallSpec` finishes the span. -/
theorem stmtSpec_call {P : LocalEnv → ExecState → Prop}
    {P' Q' : ExecState → Prop} {fid : FuncId} {es : Array Expr}
    {vals : List GoValue} {v : GoValue}
    (hargs : ∀ env σ, P env σ → ∀ (k : Cont) (ch : Choices), ∃ m,
      stepFnIter m σ (.exec (.call #[] fid es) env k) ch
        = .ok (.retV v (.callArgsK fid [] vals [] env k), σ, ch))
    (himp : ∀ env σ, P env σ → P' σ)
    (hcallee : CallSpec P' fid vals v Q') :
    StmtSpec P (.call #[] fid es) (fun _ σ' => Q' σ') := by
  intro env σ hP k ch
  obtain ⟨m, hm⟩ := hargs env σ hP k ch
  obtain ⟨n, σ', ch', hrun, hQ, hsuf⟩ := hcallee σ (himp env σ hP) env k ch
  exact ⟨m + n, σ', ch', stepFnIter_chain hm hrun, hQ, hsuf⟩

/-! ## The tape-suffix algebra -/

/-- A raw tape pop consumes a prefix: the remainder is a suffix. -/
theorem Choices.consume_suffix (ch : Choices) (bound : Nat) :
    (Choices.consume ch bound).2 <:+ ch := by
  cases ch with
  | nil => exact List.suffix_refl _
  | cons c rest => exact ⟨[c], rfl⟩

/-- The censused consumption site's remainder is a suffix. -/
theorem Choices.consumeAt_suffix (site : GoCore.ChoiceSite) (bound : Nat)
    (ch : Choices) : (Choices.consumeAt site bound ch).2 <:+ ch := by
  unfold GoCore.Choices.consumeAt
  split
  · first
      | exact Choices.consume_suffix ch bound
      | exact List.suffix_refl _
  · first
      | exact Choices.consume_suffix ch bound
      | exact List.suffix_refl _

/-! ## Sealed refusals (the BRiCk UNSUPPORTED pattern — design note
§5): semantically `False`, payload names the site; nothing downstream
can consume an uncovered shape silently. The escape ladder: scoped
manual lemma → promoted rule; every escape's interface is the
unchanged judgment. -/

/-- A sealed refusal: `False` with the unsupported site named in the
payload. -/
def Refusal (site : String) : Prop := False ∧ site = site

theorem Refusal.not (site : String) : ¬ Refusal site := fun h => h.1

/-- The tgtOpK-INCLUSIVE result-bearing span (the frame arm's
caller-target walk, StepFn.lean:684-694) remains OUTSIDE the
judgment: the walk evaluates CALLER-side operands, so that span is
not callee-local. The demanded callee-local form landed as
`CallSpecR` (W3 U3.1-F) — it ends at return arrival, one step before
this walk; call sites compose the walk themselves. This seal now
covers only the caller-inclusive form. -/
def refusalResultBearingCallSpan : Prop :=
  Refusal "CallSpec: caller-inclusive result-bearing span (tgtOpK caller-target walk)"

/-- Nullary calls enter the frame from the statement arm directly
(no drained `.retV` shape); the nullary judgment form is sealed until
a consumer demands it (every raft handler carries its receiver). -/
def refusalNullaryCallSpan : Prop :=
  Refusal "CallSpec: nullary call entry"

end GoLean.Spec
