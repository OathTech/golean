# W1 design note: the Spec judgment, its rules, the footprint frame, and the glue (2026-08-27)

Unit: W1 (clean-proof plan §W1, professor-amended). Written BEFORE the
code, per the charter's classics-first rule. Every mechanism below
carries a LINEAGE line. The quantifier-audit line for the whole unit
is at the top of `docs/w1-prover-log.md` (W1 is the machinery wave:
rules, not end-theorem quantifiers).

**W2 addendum notice (2026-08-27, the W2 worker)**: §7–§8 below are
the W2 additions (the plug rule's full design, written before its
code, and a recorded DELTA against §3's side-condition expectation).
The W2 quantifier line is at the top of `docs/w2-prover-log.md`.

## 1. The judgment

The definition follows `docs/2026-08-27_proof-structure-explained.md`
§1 verbatim in content; the Lean spelling makes two engineering
choices, recorded here.

**Statement form** (the sub-judgment spans compose from):

```
StmtSpec P c Q :=
  ∀ env σ, P env σ → ∀ k ch,
    ∃ n σ' ch', stepFnIter n σ (.exec c env k) ch = .ok (.next k, σ', ch')
                ∧ Q env σ' ∧ ch' <:+ ch
```

**Call-span form** (the plan's `Spec P f Q`; function entry through
the frame arm to the post-store configuration, StepFn.lean:676-694):

```
CallSpec P fid vals v Q :=
  ∀ σ, P σ → ∀ env k ch,
    ∃ n σ' ch',
      stepFnIter n σ (.retV v (.callArgsK fid [] vals [] env k)) ch
        = .ok (.next k, σ', ch')
      ∧ Q σ' ∧ ch' <:+ ch
```

`vals ++ [v]` is the argument list (the machine's drained-call shape:
the last argument's value is in `retV` position). Bounded (`≤ B`)
variants `StmtSpecB`/`CallSpecB` carry `n ≤ B` for the totality
sentence; `B` is a parameter (a bound as premise/function — never a
subject-run constant in a statement; the pilot's measured counts live
in proof bodies and this log only).

Choices recorded:

- [AGENT] The statement form's precondition is over `(env, σ)`, not
  `σ` alone as in the §1 spelling. At statement granularity the env
  is the span's register file: a spec of `x := e` must be allowed to
  say where `x` points. The §1 spelling (∀ env with P over σ) is the
  P-env-constant special case; nothing is lost, and W2's loop rules
  need the env-aware form.
- The call-span form quantifies `env`/`k` UNIVERSALLY — this is the
  continuation-parametricity the plan demands, and it is exactly
  what makes the call rule compose (§3). It is honest for the
  RESULTLESS shape (plans `[]`, results `[]` — the frame arm at
  StepFn.lean:676): the caller's env is inert in the span. The
  result-bearing shape (the tgtOpK walk, :684-694) evaluates
  CALLER-side target operands post-call, so its span depends on
  caller code; it is NOT covered by W1's `CallSpec` and gets a
  sealed refusal (`Refusal` prop, §5) until a consumer demands it
  (the raft handlers on the reachable graph are resultless-called;
  library calls with results are consumed inside windows, not
  through `CallSpec`, until then).
- `ch' <:+ ch` (suffix): the tape is consumed monotonically
  (`Choices.consume` pops the head); recording it in the judgment
  makes the two interchange forms (stream-invariant, explicit
  prefix) derivable presentations, per §1.

LINEAGE: Hoare triples over a fueled small-step machine
(Floyd/Hoare; the ∃n conclusion is the classic total-correctness
reading with fuel reified). The continuation-parametric,
run-to-`.next k` encoding is the evaluation-context/CPS presentation
(Felleisen-Hieb contexts; Iris's WP-with-bind over a small-step
language; Appel-Blazy continuation-style program logics). `∀ ch` is
demonic nondeterminism over a reified choice tape (Dijkstra's
demonic reading; the machine is deterministic given the tape).
Divergence from the classics: termination-to-continuation is
detected by SYNTACTIC return of the caller's `k` (the machine's own
frame discipline) rather than by an observation predicate.

## 2. The composition rules

- `conseq` (both forms): weaken P, strengthen Q. Classic rule of
  consequence.
- `seq`: `StmtSpec P c₁ R → StmtSpec R c₂ Q →` the span of the
  sequence. Stated at the machine's own sequencing shape
  (`.seq`-continuation chaining; the `seqn` splice), proved by
  `stepFnIter_chain` + the seq-pop steps.
- **The call rule**: a callee's `CallSpec` consumed at a call site.
  Two layers: (i) `CallSpec.consume` — the definitional hop from the
  drained call configuration, usable mid-span wherever a larger walk
  reaches that configuration (this is how the pilot composes); (ii)
  `stmtSpec_call` — the statement-level rule: an argument-evaluation
  premise (the segment from `.exec (.call …) env k` to the drained
  configuration, state-passive) + the callee's `CallSpec` yield the
  `StmtSpec` of the call statement. LINEAGE: the procedure-call rule
  of Hoare logic with the adaptation left to `conseq`; the
  argument-evaluation premise plays the role of the caller-side
  evaluation lemma in CFML/characteristic-formula treatments.

## 3. THE FOOTPRINT FRAME DESIGN (starred summit) — probe findings

Goal (plan §W1): a Spec carries its footprint; execution from a
Spec-satisfying state leaves cells outside the footprint untouched
AND the Spec transports to states differing only outside it — no
pairwise disjointness enumerations.

**The design**: footprint = the heap domain of a CANONICAL,
low-packed pre-state family (value-symbolic, address-concrete — the
Sym layer's γ-image family); a big state carries the footprint iff it
is a `FrameSim ρ na₀ na fr`-image of a canonical state (Frame/Sim's
landed relation: ρ injective placement, `fr` the frame heap, the
disjointness carried ONCE by ρ-injectivity + `fr_avoid`, never by
per-cell enumeration). The frame theorem's two halves:

- *outside untouched*: the landed `stepFnIter_sim` transports the
  canonical run and its terminal `FrameSim` carries `frame_pres` —
  every frame cell verbatim in the terminal state.
- *Spec transport*: pre/postconditions written in reader vocabulary
  transport through READER-CONGRUENCE lemmas: each reader
  (`absRaftNode`, the AbsTwinV0 components) reads scalar content
  through `Heap.lookup` chains, and scalar content is
  rename-invariant, so `FrameSim ρ … σ σF → absRaftNode σ a =
  absRaftNode σF ⟨ρ a⟩` (built in W1 for `absRaftNode`; the deep twin
  readers are W3's, same pattern).

LINEAGE: the separation-logic frame rule (O'Hearn-Reynolds),
realized as locality-of-action via an explicit renaming simulation
(Calcagno-O'Hearn-Yang local action; Frame/Sim's design of record
2026-08-13). Reader congruence = heap-monotone pure assertions.

**Probe findings (the summit's measured constraints — these gate W3
and are the pilot's most important output):**

1. **The control half is a separate rule.** `FrameSim` transport
   maps a canonical run's configuration through `renameConfig ρ` —
   so the transported span holds only at env/k in ρ's IMAGE. The
   frame region `[na₀-image gap]` is precisely where the CALLER's
   locals live, so a caller's env/k at a real call site is NEVER in
   the image: no choice of ρ, na₀, fixture layout, or canonical
   packing fixes this (measured dead ends recorded in the log:
   identity-ρ violates `fr_avoid`'s geometry; aligned-prefix layouts
   still exclude caller cells allocated pre-call). Conclusion: the
   footprint frame = `FrameSim` (state half) + a PLUG RULE (control
   half): a successful call-span at `tenv = [], k = .stop` commutes
   with replacing the barrier frame's tenv and below-barrier tail —
   env/k-inertness of resultless call-spans as a THEOREM.
   LINEAGE: wp_bind / evaluation-context composition (Iris;
   Felleisen-Hieb): the callee's triple in the empty context lifts
   to every context. Cost datum: the analogous landed arm walk
   (`Frame/StepSim.lean`, the rename commutation) is 795 lines.
   The barrier is syntactically recognizable (the unique frame
   whose tail slot is literally `.stop`), so the replacement
   function is structural and needs no reachability invariant;
   the panic-walk arms (`recoverThroughWrappers` crossing a
   non-wrapper barrier) are excluded by span success + the
   terminal discipline, not by side conditions.
2. **Canonical windows are continuation-parametric FOR FREE** (the
   driver's route, probe `artifacts/w1/ProbeOpenTail.lean`): kernel
   reduction of `symEvalWindow*` never inspects below the barrier on
   a successful span, so window facts evaluate by `rfl` with the
   below-barrier tail and the frame's tenv as OPEN VARIABLES. So the
   plug rule is NOT needed to state or prove canonical `CallSpec`s
   (Leg A); it is needed exactly when a TRANSPORTED (framed) span
   must be consumed at a foreign call site (Leg B's mechanics, all
   of W3's handler-into-driver composition).
3. **`bodies_inv` reserves the global region.** `FrameSim` demands
   ρ-invariant function bodies; lowered bodies pin package-level
   vars at static addresses (the twin has 31 globals), so every
   admissible ρ is the identity on the global region, and every
   canonical fixture that is ever to be transported must keep global
   cells at their true static addresses. The arc4d fixture
   (`uS0`, raft cell at address 0) violates this — fine for Leg A's
   canonical spec, but its transported use requires a re-laid
   fixture (window regeneration at a compliant layout). Recorded as
   a W3 obligation, not silently absorbed.

## 4. The glue family (Leg C — gates both sentences)

Over the landed FuelMeasure/runConfig kit (`runConfig_mono`,
`runConfig_of_stepFnIter`, …): `runProgramM_mono` (two-phase fuel
monotonicity), `runProgramM_readout_of_total` (∃N-total ⇒ the
∀-fuel partial sentence — the designated bridge),
`runConfig_prefix_classify` (a completed run's truncations die at
the fuel check, never at a fault) + its two-phase `runProgramM`
lift (`runProgramM_classify_of_total` — NeverFaults' truncation
half), `runProgramSetupM`/`runPkgInitM` conditioned unfolding
lemmas, and the readback `loadMany` `.ok` lemma. All ∀-quantified,
no subject constants. LINEAGE: fuel monotonicity/determinism
arguments standard for step-indexed executable semantics
(CompCert-style smallstep determinism lemmas). Audit-pinned in
`Audit/Kit.lean` § RunGlue.

## 5. The minimal driver (no Lithium in W1) and refusals

The driver is a PROOF PATTERN, not machinery: (i) canonical span
facts by open-tail window evaluation (`symEvalWindow*_refines'` at
open env/k) chained with the choice-crossing transports
(`stepFn_pick_generic`, spill/branch transports) via
`stepFnIter_chain`; (ii) `CallSpec.consume` at drained-call points;
(iii) reader-congruence readout at span ends. Uncovered arms are
SEALED REFUSALS: `Spec.Refusal (site : String) : Prop := False`
carriers — semantically False, payload names the site (the BRiCk
UNSUPPORTED pattern; deps/brick-wp), so nothing downstream can
consume an uncovered shape silently. The escape ladder (recorded,
per plan): scoped manual lemma (kit-style conditioned step) →
promoted rule (a named theorem in the judgment module); every
escape's interface is the unchanged judgment.

LINEAGE: symbolic execution with certificate replay (King;
computational reflection); the refusal pattern is BRiCk's.

## 6. Non-vacuity

The judgment itself gets ONE honest instance each (stated as such,
the charter's carve-out): a `CallSpec` instance (Leg A's
becomeFollower spec) and a `StmtSpec` instance; the ∃n in every
instance is discharged by exhibiting the run (how existentials are
proved). Interfaces added by W1: none beyond the judgment (no
speculative typeclasses; the footprint predicate is a per-target
def, not an interface).

## 7. THE PLUG RULE (W2 unit 1 — the frame's control half, designed before code)

Goal (§3 finding 1, the W1 summit finding): a `CallSpec` proved at
CANONICAL anchor (caller env `[]`, below-barrier tail `.stop`) —
which is how FrameSim-transported spans arrive, since `renameEnv ρ []
= []` and `renameCont ρ .stop = .stop` — becomes consumable at a
FOREIGN call site with the caller's REAL `env`/`k`, which live at
frame-region addresses outside every admissible ρ's image.

**Statement (target form)**:

```
theorem stepFnIter_plug (env' : LocalEnv) (k' : Cont) (…premises…) :
  stepFnIter n σ c ch = .ok (.next .stop, σ', ch') →
  Config.hasBarrier c = true →
  stepFnIter n σ (plugConfig env' k' c) ch = .ok (.next k', σ', ch')
```

with the `CallSpec`-level corollary (peeling the deterministic frame
entry): a successful span from
`.retV v (.callArgsK fid [] vals [] [] .stop)` to `.next .stop`
yields, at the SAME fuel/state/stream, the span from
`.retV v (.callArgsK fid [] vals [] env' k')` to `.next k'`.

**The replacement function** (`plugCont env' k'`, structural on the
spine — `Cont` is linear: every constructor except `.stop` has
exactly one tail):

- `.frame [] te r ds .stop false ↦ .frame [] env' r ds k' false` —
  THE BARRIER: the unique frame whose tail slot is literally `.stop`
  (uniqueness by spine linearity: exactly one `.stop` per spine, at
  the bottom). Both the caller-env slot (`te`, inert for a resultless
  frame — only the targeted exit arm ever reads it) and the tail are
  replaced, so the plugged frame is EXACTLY the frame a real call at
  `(env', k')` constructs (StepFn's `callArgsK`-drained arm:
  `.frame plans env resultLocs [] k' func.wrapper`).
- `.stop ↦ k'` — reached only OUTSIDE the barrier's protection: the
  exit configuration `.next .stop ↦ .next k'` and the
  panic-crossed configuration `.panicking chain .stop ↦
  .panicking chain k'`. During the span the barrier match fires
  before recursion ever reaches the bare `.stop`, so the
  substitution is applied exactly once. This one clause makes the
  per-step commutation UNIFORM (in-span, exit, and crossed steps all
  read `stepFn σ (plug c) ch = .ok (plug d, σ', ch')`).
- every other constructor: map over the tail.

`Config.hasBarrier` (the induction invariant): the configuration's
continuation spine contains a frame of the barrier shape
(`.frame [] _ _ _ .stop false`); recursing through `opDone`'s inner
configuration; `false` on `.panicked`. Preserved by every in-span
step (frames created during the span sit OVER the current
continuation, whose bottom already carries the barrier, so no new
frame ever has a literal-`.stop` tail).

**The per-step walk** (the `fun_cases stepFn` arm walk,
`Frame/StepSim.lean`'s proof pattern, state-trivially — the plugged
run shares σ/choices verbatim, so no state relation and none of the
rename walk's value/heap lemmas):

```
stepFn_plug : hasBarrier c → (premises) →
  stepFn σ c ch = .ok (d, σ₁, ch₁) →
  stepFn σ (plug c) ch = .ok (plug d, σ₁, ch₁)
  ∧ (hasBarrier d ∨ d = .next .stop ∨ ∃ chain, d = .panicking chain .stop)
```

Iteration closes the three disjuncts: `hasBarrier d` recurses;
`d = .next .stop` forces remaining fuel 0 (`stepFn` throws on the
terminal — StepFn.lean:552 `.next .stop → .internal`), delivering the
conclusion; the crossed disjunct is refuted from span success
(`.panicking chain .stop` steps only to `.panicked`, which steps only
to an error — the terminal discipline — so `.ok (.next .stop, …)` is
unreachable from it, at any fuel).

Helper commutations owed by the walk (each a structural induction or
head-case bash): `seqCont`, `contHeadLabel`, `pushDefer`,
`panicPassthrough`, `recoverThroughWrappers`/`recoverResult`,
`pruneIterFramesKey`/`pruneIterFramesAll`/`contAfterStmtOp`, and the
build-only embedders `applyChanOp`/`applySelect`/`applySyncOp`/
`enterRecvTargets` (these embed `env`/`k` in their result
configurations without inspecting them — one cases-per-outcome lemma
each).

**THE PREMISES — a recorded DELTA against §3 finding 1.** §3 claimed
the panic-walk arms are "excluded by span success + the terminal
discipline, not by side conditions". The W2 machine walk-through
REFUTES that expectation for two arms; both need side conditions on
the PLUG CONTEXT (consumption-site-checkable, so composition-
friendly), and one on the callee. Flagged here, not silently
absorbed:

1. **`recoverThroughWrappers k' = none`** (the recover premise). A
   bare `recover()` at barrier depth in the callee's body — reachable
   through glue and WRAPPER frames only — makes `recoverResult`
   inspect the below-barrier tail on a SUCCESSFUL span
   (StepFn.lean:299-301; Machine.lean:2013-2016: at the first
   non-wrapper frame the walk runs `recoverThroughWrappers` on that
   frame's tail). Canonical tail `.stop` refutes to `none`
   (recover = nil); an adversarial `k'` whose head reaches a
   `panicResumeK` through glue/wrapper frames only would resolve —
   genuine divergence, undetectable from the canonical run. The
   premise is decidable and discharged by `rfl`/`decide` at closed
   consumption sites; it propagates through caller glue (the walk
   refutes at the caller's own non-wrapper frame, so any site under
   a real enclosing frame discharges it structurally). Walks that
   START above a NON-wrapper barrier and descend never pass it
   (`.frame … false ↦ none` — Machine.lean:1950), which is why this
   is the only recover exposure.
2. **`mapIterFree k' = true`** (no in-flight `mapIterK` frame
   anywhere in `k'`). A callee-body `mapDelete`/`clearMap` prunes
   produced/start sets of EVERY in-flight map-range frame in the
   continuation, crossing call frames by design
   (Machine.lean:2085-2086 "The walk crosses every frame (a range
   body may delete through a call)") — including frames BELOW the
   barrier. That is real Go semantics (a callee deleting from a map
   its caller is ranging over), so plugging is genuinely unsound
   there: the plugged run's caller frames get pruned, the canonical
   run cannot see them. The premise is syntactic on `k'`. The
   refined variant (prune-inert: no `mapIterK` in `k'` over any base
   the span deletes) is the recorded escape if a consumer ranges
   over a map while calling a deleting handler; built on demand.
3. **The callee's frame is non-wrapper** (`func.wrapper = false` for
   the entered callee — carried as a premise on the function table
   at the `CallSpec` corollary). A WRAPPER barrier is transparent to
   the recover walk (Machine.lean:1948), so the walk would cross it
   into `k'`; premise 1 alone would not cover the `recoverResult`
   descent (Machine.lean:2017-2019 recurses through wrapper frames).
   Raft handlers are ordinary functions; promotion-wrapper CallSpecs
   are outside the rule until a consumer demands them (sealed-refusal
   posture).

Also inherited from the judgment's scope: the barrier is RESULTLESS
(`targets = []` — the `CallSpec` shape); the barrier's `te` slot is
then machine-inert, which is what licenses replacing it.

LINEAGE: wp_bind / evaluation-context composition (Iris's `wp_bind`
over a small-step language; Felleisen–Hieb evaluation contexts): the
callee's triple proved in the EMPTY context lifts to every context
`K[·]` — here the context is reified as the below-barrier
continuation + the barrier's caller-env slot, and the lift is a
per-step commutation of the context-replacement function with
`stepFn`, i.e., locality of the step relation in the
below-barrier tail. The premises are the non-locality census: the
two machine features that genuinely inspect the context through a
call boundary (Go's recover walk; live map-range pruning) surface as
exactly the rule's side conditions — the fail-closed analogue of
wp_bind's requirement that the context be an evaluation context.
Divergence from the classic: the commutation is proved arm-by-arm on
the executable step function (certificate-replay style) rather than
by a context-composition lemma in a relational semantics, because
the machine's continuations are defunctionalized (no syntactic
`K[e]` decomposition exists to induct on).

**Probe-first plan** (charter requirement — two structurally
different call sites before the general theorem): (P1) the pilot's
passive-argument call statement shape (caller glue = `callArgsK`
argument walk only); (P2) a call under compound caller context
(inside a `seq` under a `loop` with a caller `frame` below — the
driver-shaped context). Each probe: build the plugged span for a
tiny two-function program by the plug function and check the
end-to-end equality concretely (`#eval`-first, then `example … :=
rfl`/`decide`), confirming barrier recognition and the uniform
`.stop ↦ k'` clause behave as designed before the 800-line walk is
paid. Probes land tracked (in-build) beside the rule.

**Cost datum**: the analogous rename walk (`Frame/StepSim.lean`) is
795 lines OVER a state relation; the plug walk shares its `fun_cases`
skeleton with a trivial state story but adds the three premise
threads. Expected same order (600–900 lines incl. helpers); measured
number to be recorded in the W2 log at landing.

## 8. Interface position of the plug rule

The rule ships as `Frame/Plug.lean` (general layer — machine
locality, no target content) with the consumable composition
corollary in the judgment's vocabulary:

```
CallSpec.transport : CallSpec P fid vals v Q →
  (FrameSim premises + plug premises) →
  the framed site's span at (env', k') over σF, with Q read back
  through reader congruence
```

exercised by the W2 gate (Leg-B-as-intended): the pilot's
`becomeFollower_callSpec` consumed at a real caller-site shape at a
FOREIGN placement (FrameSim state half + plug control half + reader
congruence), measured. Non-vacuity: the gate instance itself.

