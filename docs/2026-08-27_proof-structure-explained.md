# How the proof actually works: GoLean → Verdi-style result, step by step

Deliverable 3 of the replanning round (2026-08-27), written for a
formal-methods reader. Every step is annotated **[HAVE]** (on main @
d0e0d2e8, statement verified by direct read or census with verbatim
quote), **[WRONG-SHAPE]** (exists as stepping-stone material — content
real, form unusable for the quantified theorem), or **[PROPOSED]**
(to be built; its rule named). Evidence: the three code censuses
(2026-08-27) + direct reads of the statement layer, the driver, and
the checker.

## 0. The subject and the sentence

The on-disk program (etcd-io/raft at the recorded pin + the twin
harness) is reflected to a Lean term once:
`twinLowered : Program := goldenWire% "baselines/golden/twin-chdriver.wire.json"`
— the elaborator runs the same fail-closed decoder as every machine
run; `scripts/check-golden` ties the wire bytes to the frontend on
the source. **[HAVE]** Shape pins (kernel `Expr.eqbF`/`Stmt.eqbF`
certificates) tie every piece of syntax the proofs mention to
subfields of this term. **[HAVE]** This pair is the only place the
concrete program enters; nothing else about the proof is literal.

The run: `twinRun fuel ch := runProgramM fuel twinLowered
"twinChoiceVerdict" #[] ch` — seed globals, run `$pkginit`, run the
entry function; the same wiring as the differentially-tested CLI.
`twinChoiceVerdict` (twin-chdriver.go:129) runs the driver and
returns five ints (violations, claims, committed, complete, floor).
**[HAVE]**

The sentences (both shapes; designation yours):

```
Partial:  ∀ fuel ch r,  twinRun fuel ch = .ok r → spec r      [HAVE as Prop]
Total:    ∀ ch, ∃ fuel r, twinRun fuel ch = .ok r ∧ spec r    [PROPOSED Prop]
NeverFaults: ∀ fuel ch, twinRun fuel ch = .ok _ ∨ = .error .fuelOut  [PROPOSED Prop]
```

`spec r` = `r.values[0]? = some (.int 0 .int)` — the violation
counter, incremented at 12 sites (5 checker: S1 election safety, 2×S3
monotonicity, S3 anomaly, S2 agreement; 7 harness guards, all
halting). The `GoError` taxonomy was designed for NeverFaults: the
`fuelOut`/`panic`/`stuck` split exists so "ends `.ok` or `.fuelOut`,
never stuck/panicked" is expressible (its docstring says so). **[HAVE]**

## 1. The program logic (the judgment and its rules)

The de facto judgment already exists as an interchange format that
every landed rule produces and consumes:

```
stepFnIter n σ c ch = .ok (c', σ', ch')        -- explicit prefix, or
∀ ch, stepFnIter n σ c ch = .ok (c', σ', ch)   -- stream-invariant
```

What the rule set provides today, all ∀-shaped, verbatim-verified:

- **The symbolic-execution engine** **[HAVE]**:
  `symEvalWindow_refines : symEvalWindow budget S C = (n, S', C') →
  ∀ ρ σ ch, stepFnIter n (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C', γS ρ σ S', ch)`
  — ∀-valuation, ∀-state (table-generic), ∀-stream, quit-safe (an
  uncovered arm shortens the window, never errs). The `T`/`TB` forms
  add table/function extension by one `SubTable` premise.
- **Choice-site rules** **[HAVE]**: `stepFn_pick_generic` (map
  iteration — conditioned on candidates and the consumed index),
  `stepFn_appendSpill_transport` / `_appendInPlace_` (allocation
  latitude — ∀-draw via the `ch.consume` premise),
  `stepFn_branch_transport` (King-style splitting at `ifK`), and the
  composition spine `stepFnIter_window_pick_window`.
- **Heap/field rules** **[HAVE]**: Lens L1–L4 (focus, store-miss =
  the frame half, store-hit, rename transport), ∀-state with
  executable normalization premises.
- **Frame/renaming** **[HAVE]**: `stepFnIter_sim` / `execStmtLoop_ren`
  / `completesIn_ren` over `FrameSim` — locality at any placement,
  same fuel, same stream.
- **A loop rule** **[HAVE, one shape]**: `sliceWalk_loop` — a genuine
  Floyd/Hoare rule: invariant family `S : Nat → ExecState → Prop`,
  one body obligation, bounded-completion conclusion, stream
  unchanged. Specialized to the frontend's range-desugar shape; the
  map-range sibling exists (MapLoops); the plain-`for` head schema
  exists on the arc4d branch (CondFor). **[PROPOSED]**: the loop-rule
  family completed per desugar shape — mechanical siblings of the
  proven pattern.
- **An Iris WP layer** **[HAVE, different calculus]**: ~80 `wp_*`
  laws over the Prop step relation, `GoTriple`/`GoSpec` (frame-closed,
  ∀-fuel ∀-choices statement vocabulary) and a real adequacy pipe
  (`goSpec_of_wp`). The campaign migrated off it to the direct
  interchange format; both are available. The plan builds the spec
  layer on the interchange format (the working path) and keeps
  `GoTriple`-shaped conclusions so the Iris presentation remains
  reachable.

**[PROPOSED — the one genuinely new piece at this level]**: the
**spec former and composition driver** — a named triple
`Spec P f Q` (precondition/postcondition as predicates over states
via the abstraction readers) with a call rule, assembled from the
rules above by a deterministic driver instead of by hand. This is
organization, not new mathematics: the arc4d span theorems prove
hand-rolled instances of exactly these triples today (§2).

## 2. Function specs (per function, ∀-state — the code visited once)

For each function on the reachable call graph (~15 handlers +
library functions + the checker + init + the driver body): one spec

```
Spec  { states where the abstraction reads P }  f  { abstraction reads Q }
```

quantified over ALL states satisfying the precondition. **[PROPOSED]**,
with strong evidence of feasibility in hand:

- **[WRONG-SHAPE]** `s1_span_computes` / `s23_span_computes` (branch
  campaign-arc4d, unlanded): the checker's spans proved to compute
  the model checker's fold step at SYMBOLIC checker state — the
  content of the checker specs, in hand-Hoare form (20 pairwise
  disjointness premises where the frame rule should be, hand-stated
  frame conjuncts, `∃ m ≤ 18400` bounds). Their abstraction
  functions (`projLOf`/`projBy`/`encGS`) and commutation lemmas
  (`s1_abs_step`/`s23_abs_step`) are the reusable core; the walks
  become the specs' proof bodies under the driver.
- **[WRONG-SHAPE]** the 68 trajectory equations (18k lines): each
  proves one fixture-trajectory of a handler — evidence that every
  handler's span is walkable, none of it in spec form.
- **[HAVE]** `rebuildLoop_span`/`liveCountLoop_span` (DriverNet): the
  driver's per-round glue, already symbolic in net length — genuine
  specs, the exception that proves the pattern.
- **[PROPOSED]** the init spec `Spec ⊤ ($pkginit; setup) I₀` —
  replacing the seed pins (init is code; its spec is proved like any
  other, its loops by the loop rules). This kills the 81k-step
  literal-replay obligation outright.

Latitude inside specs: draw-consuming sites are handled by the
choice-site rules — the spill rule is ∀-draw already; map-iteration
loops get multiset invariants ("the postcondition depends only on
the set produced"), the classic treatment of
iterate-then-canonicalize. CONSEQUENCE (a simplification found in
this replanning): the spec route discharges ∀-stream DIRECTLY — the
choice-erasure quotient is NOT on the critical path; it remains an
optional localization instrument (your "operate erased when
needed"), built on demand.

## 3. The invariant and the loop (where Verdi meets the code)

The driver's main loop is source-bounded (`for round = 0; round <
400`, twin-chdriver.go:48) with a four-branch body
(deliver-the-picked-message / complete-break / propose-with-guard /
honest-halt). **[HAVE — read directly]** The proof at this level:

```
I(σ) := WfTwin σ                                 -- concrete well-formedness
      ∧ ∃ N, absTwinRead σ tl = some (proj N)     -- THE PAIRING
      ∧ ReachRel (EStep voters) N₀ N              -- abstract reachability
```

- `absTwinRead : ExecState → Loc → Option AbsTwinV0` — the total,
  fail-closed round-boundary reader (TypeId-checked, `.nil`-refusing)
  **[HAVE]**; `proj` = the AbsTwinV0 ↔ SNet correspondence
  **[PROPOSED — this is O5b done properly: established once in the
  body spec's postcondition, not per-boundary pins]**.
- The loop theorem: init spec establishes `I`; the body spec
  preserves `I` (its case analysis is over the NET CONTENTS at the
  pick — all deliverable messages — not over histories); `I` at the
  checker's execution points feeds §4's leaves. Partial correctness
  = invariant only; Total adds the variant (the source-bounded
  counter + the body specs' totality; the drain guards' bounds are
  premises the specs discharge). **[PROPOSED — the loop-rule
  instance; the landed `round_induction` is its unrolling-shaped
  ancestor, killed]**

## 4. The abstract layer (the Verdi-descended top — in hand)

All **[HAVE]**, fully ∀-quantified, verbatim-verified; no code
dependency on compat/verdi (citations only — the lattice was the
design template; the mismatched dialect made native re-derivation
over an obligation signature the route):

- `ElectObligations voters step` — seven per-transition obligations
  (term monotone, vote persistence, ghost-vote intro/elim, leader
  entry via quorum victory, victory persistence, leader stability).
- `FullInv.step : ElectObligations → FullInv N → step N N' → FullInv N'`
  — ONE obligation-parametric preservation lemma;
  `native_one_leader_per_term : ∀ voters step, ElectObligations voters
  step → Seed N₀ → ReachRel step N₀ N → oneLeaderPerTerm N` — plus
  the cross-time form the checker's cross-harvest accumulation needs.
- `EStep voters` (the etcd dialect: campaign/recvVote/recvVoteResp
  with ghost rules) and `etcd_discharges : ElectObligations voters
  (EStep voters)` — every obligation proved for the etcd dialect.
  (One modeling premise to know about: `hgen` — response genuineness
  — is a constructor premise of the abstract dialect, discharged in
  the assembly by the pairing, not assumed of etcd code.)
- The S2/S3 side: `HStep`/`HistInv` (ghost history, commit-axis
  obligations as verbatim constructor premises) with
  `s2_of_histInv`/`s3_of_histInv`/`s23_leaf`; T1-scoped by
  construction (fixed leader/term fragment; single history writer —
  structural, from the driver's one pre-loop campaign).
- The checker leaves: `s1_leaf` (via `ClaimTrace` +
  `violationImpliesDelta`), and the PROVED model bridges
  (`s1_viol_delta`, `s23_viol_delta`, `s1_model_silent`,
  `s23_model_silent`) — the model checker (a branch-for-branch
  transcription of twin-lib.go's checker, its four guards
  shape-pinned verbatim against the lowering) is silent on
  violation-free traces.

## 5. The two remaining seams (both [PROPOSED], both spec-shaped)

1. **The pairing + checker correspondence**: the body spec's
   postcondition asserts (i) `absTwinRead σ' = some (proj N')` with
   `EStep N N'` (the simulation square, once, ∀-state), and (ii) the
   checker segment performed exactly `s1Step`/`s23Step` on the
   projected event (the reshaped arc4d content). These jointly
   discharge `ClaimTrace` (the S1 run-correspondence) and `hlog`
   (the appliedLog projection) — the two premises the [HAVE] leaves
   await. This is THE bridge; everything else is assembled around it.
2. **Nothing else.** With specs ∀-stream (§2's consequence), the
   erasure lift is off the critical path. The composition is:

```
init spec  ⟶  I established
body spec  ⟶  I preserved  ∧  abstract step  ∧  checker = model step
loop rule  ⟶  at every checker execution: ClaimTrace/events from an
              abstractly-reachable trace
[HAVE] abstract invariance + leaves  ⟶  the model checker is silent
verdict readout  ⟶  violations = 0                    ⟹  AgreementT1
(+ variant, spec totality)                            ⟹  Total form
(spec conclusions are .ok-shaped)                     ⟹  NeverFaults
```

## 6. What we actually have today, in one table

| layer | status | mass |
|---|---|---|
| Subject reflection + statement layer | HAVE | ~300 lines, trusted |
| Interpreter + differential + FastEval replay | HAVE | trusted base |
| Rule set (sym engine, transports, lens, frame, 1 loop shape, Iris WP) | HAVE | general, ∀-shaped |
| Spec former + driver | PROPOSED | the new organization |
| Function specs (init, handlers, checker, body) | PROPOSED (arc4d = wrong-shape evidence + reusable projections) | the summit work |
| Invariant + loop theorem | PROPOSED | one instance |
| Abstract layer + leaves + model bridges | HAVE | 2,483 lines, fully ∀ |
| The pairing/correspondence seam | PROPOSED | the bridge |
| Trajectory middle (equations, rounds, seeds, literals) | stepping stones — KILL | 1.20M lines |
