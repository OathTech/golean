# W1 design note: the Spec judgment, its rules, the footprint frame, and the glue (2026-08-27)

Unit: W1 (clean-proof plan §W1, professor-amended). Written BEFORE the
code, per the charter's classics-first rule. Every mechanism below
carries a LINEAGE line. The quantifier-audit line for the whole unit
is at the top of `docs/w1-prover-log.md` (W1 is the machinery wave:
rules, not end-theorem quantifiers).

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
