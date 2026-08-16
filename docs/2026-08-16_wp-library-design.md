<!-- PROVENANCE: this document is the VERBATIM report of reviewer 5 of the
post-autonomy adversarial audit of the gallery campaign (2026-08-16,
user-supervised phase), written on Fable against worktree tip
`3aac907e`. It is landed unedited except for this header and the
OPERATOR CROSS-CORRECTION NOTE at the end — every correction lives
there, R5's body is untouched.

LINE-CITES ARE HISTORICAL: the report's `g1.md:NNNN` references were
taken at `3aac907e`, and bucket B's edits shifted `g1.md`'s numbering
(+213 lines). The cites no longer resolve; THE CONTENT IS INTACT AT THE
NAMED UNITS — navigate by unit name. Details, and the two `proofs/`
cites that are also off, in the note at the end.

STATUS: DESIGN INPUT for the next arc. No decision is taken here and
nothing in it is chartered. Every proposal it makes lives in the
untrusted-method zone (`docs/2026-08-12_example-spec-form.md` §12b): no
name proposed below may enter a headline statement's closure, and any
lift it argues for still owes the active-abstraction loop — two landed
consumers retrofitted in the lifting commit, measured deltas, P6
deletion as the completion test.

Context for a reader who arrives here first: the campaign itself is
recorded in `docs/2026-08-15_gallery-campaign.md` (charter),
`docs/gallery-campaign-log/` (per-unit log) and
`docs/2026-08-16_gallery-campaign-trip-report.md` (retrospective, whose
addendum records this audit). The findings the audit ACTED on are in
that addendum and in the buckets-A-G commits of 2026-08-16; this file is
the one deliverable that is forward-looking rather than corrective. -->

# Gallery-campaign post-autonomy review — REVIEWER 5 design report: the generic WP/proof library the 24 examples justify (2026-08-16)

Basis: worktree `.claude/worktrees/gallery-campaign` @ `3aac907e`. Data = the 24 COMPLETE examples' proof layers (~107,226 lines under `proofs/GoLeanProofs/Examples/`, incl. generated `*Program` modules), the kit (`StepKit`, `SliceMem`, `MapMem`, `MapLoops`, `FuelMeasure`, `EntryEq`, `Frame/`), the G1 kit-gap ledger (`docs/gallery-campaign-log/g1.md`), the brick-wp mappings (`docs/2026-08-14_phase2-slice2-proof-library.md` §1, `docs/2026-08-15_brick-wp-promotion-wave-mapping.md`), the frozen §5b sketch (`docs/2026-08-12_example-spec-form.md:247-346`), and the elaboration-cost record (matmul withdrawal, g1.md:3567-3669; `EmptyRun`; WordFreq `Scan3`). Corpus-wide idiom counts (grepped, not recalled): `with_unfolding_all rfl` appears **1,517** times in the example tree; `derive_entry_eq` is invoked in **28** files; `stepFnIter_iterate` is consumed in **24** files; `Nat.strongRecOn`-style hand inductions survive in **29** files; `FreshFrom` has **5** program-local copies.

Everything proposed below lives strictly in the untrusted-method zone (form note §12b): no proposed name may enter a headline statement closure, and every proposal follows the active-abstraction loop (§12a: ≥2 landed consumers retrofitted in the lifting commit, measured deltas, P6 deletion as the completion test).

---

## 1. THE REASONING PRINCIPLES

Ten recurring proof structures, ordered roughly by position in a proof (entry → loops → composition → readout). "Coverage" = does a kit form carry the *structure*, not just the steps.

### P-A. The entry equation
Every example opens with: post-prelude state def + start `Config` + the equation `stepFnIter k σ₀ c₀ ch = …` at symbolic args/fuel/choices.
- **Instances:** 24/24 (28 invocation sites incl. multi-harness modules).
- **Coverage: FULL** — `derive_entry_eq` (`proofs/GoLeanProofs/EntryEq.lean:251`), incl. the program-generic form (G0.4). Residual gap: the string result-default quoting arm (`quoteScalarVal`, EntryEq.lean:183) — `strrev` and `wordfreq` hand-wrote the emitted shape (~45 lines each; g1.md:1688-1702). One `| .string ⟨#[]⟩` arm closes it.
- **Generic shape:** already correct. This is the library's existence proof (see §2).

### P-B. The uniform counted loop (setup / copy-in / copy-out / observation)
"Every iteration is exactly `c` steps from `(T i, C i)` to `(T (i+1), C (i+1))`, choice-free."
- **Instances:** every example with a harness loop; `stepFnIter_iterate`/`_exit` (`FuelMeasure.lean:388,420`) consumed in 24 files; it took down-counting `Int`-indexed loops (strrev reverse) and shifted inner-loop miss runs (twosum) unchanged.
- **Coverage: FULL for the induction; PARTIAL for the vocabulary that feeds it.** The family/prefix layer is fragmented: `familyMod` (`SliceMem.lean:443`) covers `seed + i%k` only; landed local re-derivations at `seed+i` (twosum `tsFamily`, dotprod, kadane, stack `stFam`, queue `qFam`), `seed+i/k` (rle, dedup), LCG (`Examples/SortShared.lean:61-71`, shared by both sorts but living in the example tree), signed/Int-seeded (kadane). Copy-OUT of computed data has no form at all (`takePad`, g1.md:2163-2178, selsort `Post.lean` + bubble ×2).
- **Generic shape:** `SliceMem.familyF (f : Nat → Nat) (n seed)` with the six facts (exact statement drafted at g1.md:1891-1906); `familyOf (step : Nat → Nat)` for iterated-step families (LCG becomes an instance); `prefixPadL/takePad (src : List Int) (cap m)` (source-list-generic; `prefixPad` is already family-generic except its `_set` lemma).

### P-C. The two-exit loop (iterate / bail-from-body / exit-at-test)
The loop leaves either at its test or by early `return`/`break` from the body; both exits run to a common anchor (often the driver terminal), loop-local cells existentially quantified.
- **Instances:** 5 among campaign examples — palin `ph_loopP` (the discovery writeup, g1.md:1094-1135), strrev `Palin.lean` (2nd copy of the same strongRecOn-to-terminal), twosum (inner-loop early return), bubble `Outer.lean` (`!swapped`), rle; `dedup`'s keep/skip and legacy binsearch are near relatives.
- **Coverage: NONE.** The exact kit shape was specified in the ledger and never lifted: `FuelMeasure.stepFnIter_iterate_bail (c e b) …` concluding `∃ k ≤ c·μ + max b e` (g1.md:1201-1216); it is also the honest generalization of G0 item (d)'s deferred `stepFnIter_iterate_bounded` (g0.md:198-211). ~55 lines of induction scaffold per consumer today.
- **Generic shape:** as drafted — three hypotheses (one iteration; the bail, available where its condition holds; the exit), body and binder shapes never appearing (the R1-closure lesson: per-iteration content enters as ONE hypothesis).

### P-D. Frame/rebase-at-threshold (loop bodies that re-allocate locals)
Pass proven once at the tight canonical placement; the executable frame theorem transfers it to the garbage-laden placement; retired cells rebased into the frame between passes.
- **Instances:** **5 full hand instantiations**, ~400–470 lines each: isort ×3 (`ρsh` T=4, `InsertionSort/PassFrame.lean:43,198,344`; `ρ11` T=11, `Subject.lean:586,737,886`; `ρ21` T=21, `Count.lean:770,962,1165`), selsort (`ρ16`, `SelectionSort/Frame.lean:44,274,499`), bubble (`ρ16`, `BubbleSort/Frame.lean:30,262,486`). Found independently by both sort lanes — the ledger's own #1 (g1.md:2649-2654).
- **Coverage: PARTIAL.** The core is kit (`Frame/Sim.lean:171` `FrameSim`, `Frame/Transfer.lean:29` `stepFnIter_sim`); the entire threshold-instantiation layer is per-example.
- **Generic shape:** `Frame/Threshold.lean` — `ρT (T d : Nat)`, `shiftSpec_ρT`, bump transport `renameLoc_shiftAt_succ`, `rebaseSimT` parameterized by threshold + retired-cell LIST with the front's per-cell obligations entering as ONE hypothesis dischargeable by `rfl`s, `transfer_segT` (full draft at g1.md:2110-2134 and 2336-2357 — the two drafts agree). The per-example residue is genuinely the fixed-cell enumeration only.

### P-E. Footprint segments over abstract heaps
Segments stated over a fully abstract heap `h` (only reads/writes conditioned as `Heap.lookup` hypotheses / `Heap.set` result terms), whole-heap freshness as `FreshFrom h na`; the idiom for recursion, dynamic allocation, and choice-dependent layouts.
- **Instances:** 5 program-local copies — fibmemo (`FibMemo/Rec.lean:78` `fmSt`, `:86` `FreshFrom`, `:2084` `set_comm`-with-presence), stein (`Stein/Run.lean:96` — a verbatim private re-derivation incl. `.mono/.push/.push3/.set`), sieve (`Sieve/Machine.lean`), wordfreq (`WordFreq/Machine.lean`, post-shim `∃ base cap D na ch'` seam), plus twosum's precursor (`DeadFrom` + dead-region `D` threading, ~120 lines, g1.md:1911-1951). The ledger itself marks the ≥2-consumer lift DUE (g1.md:3302-3308).
- **Coverage: NONE** (StepKit has only `DeadFrom` and the append/set laws).
- **Generic shape:** a StepKit "footprint pack": `FreshFrom` + `mono/push/push2/push3/set`, `lookup_set_other/self`, `set_cons_ne/self`, `set_self_of_lookup`, `set_set`, `set_comm` **with the presence hypothesis** (the version that is false without it — worth shipping precisely because the obvious form is wrong), and the frame-exit fact `stepFn_return_frame` (re-derived in stack, queue, fibmemo, stein). Plus two *signature disciplines* that belong in the module docstring as rules: D-relative lookup hypotheses (never full-heap) and qualified `Loc.base` in big positional arguments — each backed by a measured storm (WordFreq: 502k `BEq.beq` unfoldings, 50 min → 12 s; g1.md:3416-3424).

### P-F. The choice-pick induction (map-range order)
Drain a snapshot one consumed choice + one erased entry per iteration; order-independence phrased as a conservation invariant.
- **Instances:** wordcount, histogram, fibmemo (`for range memo`), wordfreq (re-derived at string keys).
- **Coverage: FULL at `Int` keys** — `MapLoops.mapPickLoop_generic` (`MapLoops.lean:1037`; the per-iteration content is one hypothesis; conservation invariants: `distinct + |remaining| = const`, `max best (maxOf rem) = const`), with `stepFn_pick_bind/_value/_novars` (`MapMem.lean:674-752`) covering every binder shape. **Key-type-specialized**: wordfreq re-derived the whole family at `List UInt8` keys (`WordFreq/Count.lean:37` `toEntriesW`, `:60` `scan_genericW`, `mapPickLoopW`, …).
- **Generic shape:** the pick loop is already `δ`-abstract; what needs parameterizing is `MapMem`'s key axis (below, §3 item 7).

### P-G. The counting-loop layer (`m[k]++` towers)
- **Instances:** wordcount ×3 placements, histogram, fibmemo(-adjacent), wordfreq (string keys).
- **Coverage: FULL at `Int` keys** — `mapCountIter_generic` (53 steps, `MapLoops.lean:106`), `mapCountLoop_generic` (`:404`), and the per-placement discharge pack `mapCountIter_at` (`:555` — nine conditioned discharges proven once; eight are `rfl` at every landed placement). The measured payoff is the campaign's best number: Histogram `CountLoop` 825 → 376 lines, **71 s → 1.2 s**. Same key-type gap as P-F.

### P-H. Call spans / recursion packs
Continuation-parametric call segments: quantify over the return continuation + caller env so a strong induction on the *argument* hands each recursive instantiation the frame the machine pushed.
- **Instances:** fibmemo (`fmCall_base/hit/build`, `FibMemo/Rec.lean:473,942,2110` — the sandwich invariant: memo-cell content + caller target + `FreshFrom`), stein (the 36-step `isEven` span instantiated at 4 sites incl. the provably-not-run short-circuit path), strrev (3 sequential frames), stack/queue (frame exit).
- **Coverage: PARTIAL** — entry half only (`StepKit.stepFn_call_enter`, `StepKit.lean:309`). No frame-exit lemma, no span combinator.
- **Generic shape:** (i) `stepFn_return_frame` (4 consumers, trivial); (ii) a "call-span" schema: given the callee's body theorem at abstract `(h, na, ret-cont, caller-env)`, produce the caller-side span — fibmemo and stein's copies differ only in the callee facts, so the combinator is the composition `enterFrame → body → return_frame` with the three conditioned facts as hypotheses. Two landed consumers exist today.

### P-I. The append/growing-slice envelope
Both arms of `appendSlice` — in-place (no choice) and spill (one choice consumed, capacity an existential in `[newLen, max 32 (2·growth)]`, fresh backing at `nextAddr`) — with downstream state capacity- and address-generic.
- **Instances:** stack (`SliceStack.lean:897,961`), queue (independent re-derivation, `SliceQueue.lean:1342,1442`), rle (`applyStmtOp_append_spill1` + `buildAppendBackingValue_one`, ~200 lines), wordfreq (`[]string` element type — a fourth, at a second element type).
- **Coverage: NONE** — GAP-APPEND, over the §12 bar on arrival (g1.md:3170-3183).
- **Generic shape:** `SliceMem.applyStmtOp_append_inplace/_spill` parameterized over the element kind, spill stated so the consumer never names the realized capacity (the exact draft at g1.md:2519-2532). Note the honest scope line: this closes the *vocabulary* cost, not rle's `n ∈ [4,8]` domain gap — that one is choice-dependent **layout**, §2's hard tier.

### P-J. Composition + readout
`stepFnIter_chain` (~197+ use sites) → `runConfig_of_stepFnIter` → `runConfig_next_stop` → `harness_readout_of_total` (`FuelMeasure.lean:343,245,267,326`), fuel polynomials by `omega`.
- **Instances:** 24/24. **Coverage: FULL.** The only repeated friction is mechanical: chain nesting must match `+`'s left associativity or the failure surfaces as a whnf heartbeat timeout (g1.md:839-846) — a tactic-shaped annoyance, not a lemma gap.

**Cross-cutting principle: the performance disciplines.** The E-form (abstract `σ`, full result type pinned on every `have`), the program-generic form (only `heap`/`nextAddr` concrete; program consultation conditioned on `enterFrame` facts), chain-length limits (≤8 links, WordFreq `Scan3` header), opaque-parameter abstraction for large data (`Scan3`'s substring `f` pinned by `hf`). Coverage: **docstring-only** (StepKit.lean:25-108). Nothing *enforces* any of it; every violation so far was found by paying for it (52 GB at N=16; 50.8 GiB `wc_empty_run`; matmul). This is the strongest argument that the next layer must be *emitting* tooling, not more prose.

---

## 2. THE TACTICS LAYER — golean-wp v2 (direct-method)

**Reassessing §5b against the evidence.** The frozen §5b sketch planned a WP-tactic library (`idance`, env-lookup atoms, `go_loop_invariant`, the `stmt_spec` shape) for the Iris route. §11 froze the shipped method as direct segments + fuel measures, so §5b's *specific* families are dead — but its four *policies* survived intact and are already validated here: consumer-driven growth (the kit-gap ledger IS the friction list §5b.1 asked for), fixture-per-family with audit anchors (§5b.4 → `Audit/Kit.lean`, 116 pins), goal-guarded dispatch as a performance necessity (§5b.3 → the E-form storm rules), and the untrusted-layer posture (§5b.5 → §12b). The one §5b idea worth reviving under the direct method is the *loop opener*: "leave exactly (1) entry, (2) body, (3) exit goals" — that is precisely what `stepFnIter_iterate`/`mapPickLoop_generic`/the proposed `_bail` do as lemmas; the tactic layer's job is instantiation and *emission*, not logic.

**The existence proof.** `derive_entry_eq` demonstrates every capability the rest of the layer needs: it *computes* proof artifacts by evaluating the same executable pieces the interpreter uses (`computeEntryLayout`, EntryEq.lean:105), *quotes* them back as terms, *emits* declarations the elaborator/kernel then check like hand-written ones, *pre-validates* with a compiler-level probe (all-args-1, fuel 100000, `.ok` asserted before comparison) so a mis-derivation fails in milliseconds instead of in the kernel, and *fails closed* on anything outside its quoted fragment. Cost: ~0.6 s per invocation; 6 elaborator iterations end to end to build. The recorded elaborator friction (syntax atoms, `TSyntaxArray` coercion, `open Meta` ambiguity — slice-2 §"where the elaborator pushed back") is annoyance-tier, not risk-tier.

### The proposed tactic/macro set

**T1. `derive_seg` — the segment compiler (the centerpiece).**
*What it automates:* the raw-segment tower — ~700–900 lines and ~40% of proof-writing wall time per example (flagship accounting, g1.md:294-303) — by mechanizing the tracer recipe that every lane already follows by hand: probe the compiled machine for the step/tag stream, then emit segment lemmas.
*Input:* the program pin + a *segment plan* — start configuration (or "continue from segment N"), step count or stop condition (tag change, loop head), and which values are symbolic (the magic-value convention `700001, 700003, …` from the powmod tracer, mechanized: run the probe at magic concrete values, abstract every occurrence of a magic value into a binder).
*Two emission modes:*
 (a) **raw-rfl mode** — short windows between pinned configs, stated over abstract `σ` with only `heap`/`nextAddr` concrete, proved `with_unfolding_all rfl`. The probe supplies the target config; the quoter writes it down. This is what workers do from `repr` dumps today ("12 of 16 segments right first time", "all 23 on the first build" — the mapping from dump to lemma is *already* transcription).
 (b) **conditioned-chain mode** — classify each probed step by its tag: steps that consult heap/program/choices get a conditioned `have` against the matching kit lemma (`stepFn_var`, `stepFn_store_step`, `stepFn_strict_apply`, `stepFn_call_enter`, `stepFn_seqn_splice`, …— the dispatch table is the finite StepKit P1 family, StepKit.lean:129-133); runs of non-consulting steps get one rfl window; chains capped at ≤8 links (the `Scan3` rule) and assembled by `stepFnIter_chain` with left-nested arithmetic (killing the associativity pitfall structurally).
*Why untrusted:* it only emits declarations; a wrong classification or a mis-abstracted address fails at elaboration (`rfl` refuses, a hypothesis doesn't discharge) — never a false theorem. Same single-point-probe caveat as EntryEq, same honest docstring.
*Feasibility:* **mode (a): buildable now, medium engineering (est. 2–4 worker sessions).** All pieces exist: the probe machinery (the `.tmp/Probe.lean` recipe — `deriving Repr for Cont, Config`, prelude reconstruction from the Program module alone), the quoting pattern (EntryEq — though the quoter surface grows from scalar defaults to `Config`/`Cont`/`LocalEnv`, which is mechanical but the largest single work item; note statements can be *referenced* as program subterms rather than re-quoted), the emission pattern. **Mode (b): buildable, harder (est. +3–5 sessions)** — the step classifier can be probe-driven (observe which steps touched the heap by diffing states, rather than symbolically executing `stepFn` at meta level, which would be a research project), and the hypothesis-management (threading `Heap.lookup` facts through a chain) follows the pattern every conditioned tower already exhibits. Grade honestly: no wall visible, but mode (b)'s first version should target the *flat-heap* case (concrete or front+D heaps) and leave fully-footprint emission (P-E) to v2.

**T2. `go_iterate` / `go_iterate_exit` / `go_bail` — loop instantiation.**
*What:* build the `T`/`C` descriptor families and instantiate `stepFnIter_iterate(_exit)` or the (to-be-lifted) `stepFnIter_iterate_bail` from a per-iteration lemma; emit the fuel arithmetic. *Input:* the iteration lemma + trip count + exit segment. *Untrusted:* pure lemma application. *Feasibility:* **high** — this is sugar over lemmas that already have 24 consumers; the `_bail` *lemma* must land first (a ~60-line lift with 5 waiting consumers, no tactic risk at all).

**T3. `go_rebase` — the threshold-frame discharger.**
*What:* after `Frame/Threshold.lean` lands (a lemma lift, not a tactic), discharge the per-cell front obligations — the ~200-line 11/16/21-way case enumeration that is pure `rfl` per cell today — by generated case analysis. *Input:* the threshold, the front, the retired list. *Feasibility:* **high**, contingent on the lemma; the enumeration is exactly the mechanical residue g1.md:2126-2128 identifies.

**T4. `go_run` — assembly + readout.**
*What:* chain the phase lemmas to the driver terminal, apply `runConfig_of_stepFnIter` + `harness_readout_of_total`, produce the D1 readout twin, and *compute* the fuel polynomial (collect per-phase costs, emit the bound + the `omega` obligations). Run assembly is ~230 lines/example of stereotyped composition. *Feasibility:* **high**; nothing here isn't already lemma application + arithmetic.

**T5. `go_storm_lint` — the discipline enforcer.**
*What:* a proofs-tree lint (scripts-level or elab-time in the emitting macros) flagging the four measured storm shapes: a `have` applying a kit lemma to a concrete-front state without a full type ascription; unqualified `.base ⟨…⟩` in positional big-state arguments; full-heap `Heap.lookup` hypotheses in composite-lemma signatures (vs D-relative); `with_unfolding_all rfl` windows above a step threshold over program-embedding states. *Why:* every one of these has a measured pathology (52 GB; 50-minute whnf grind; 50.8 GiB; matmul). *Feasibility:* **high** for a heuristic syntax-level version; the emitting tactics (T1) make the disciplines structural for new code, so the lint's job is hand-written and legacy code.

**T6. `go_pick` / `go_count` — map-loop instantiation.** Sugar over `mapPickLoop_generic` (conservation-invariant plumbing) and `mapCountIter_at` (the nine placement facts, eight of which are `rfl`). *Feasibility:* high; value moderate (the lemmas already collapsed this cost).

### Performance: does GAP-RFL-COST dissolve?

The claim to assess: tactics mechanizing the E-form/program-generic/conditioned disciplines dissolve the class that blocked matmul (291-step `rfl` segments over concrete nested arrays: 61–326 s *per segment* across five reformulations, one 16M-heartbeat whnf ceiling at `MatMul.lean:709`, three whole-file elaborations cut at 57–114 min) and the superlinear-in-heap-size rfl wall generally.

**Assessment: yes for the matmul class — with direct evidence; qualified for the rest.** The evidence that the *shape*, not the *content*, is the cost: `wc_empty_run` 82 s / 50.8 GiB → ~86 s / **1.9 GiB** and program-size-*independent* under the program-generic restatement (`EmptyRun.lean` header; charter discharge note in `docs/2026-08-14_examples-phase2-arc-charter.md:109-117` — "verified reflection was NOT needed"); histogram `CountLoop` 71 s → 1.2 s when the tower became kit instantiation; matmul's own pickup plan (g1.md:3648-3661) names the fix as exactly T1-mode-(b)'s output ("splitting at the store boundaries or replacing raw rfl with a conditioned store lemma stated over a symbolic heap, the way the stack and queue modules do it"). A segment compiler makes that the *default output* rather than a discipline five sequential workers must each hold. **The natural acceptance test is landing matmul from its snapshot** (`refs/snapshots/gc-proofs-a/matmul-machine-layer` — every fact exists; only the segment shape blocks) — a P4-flagship-style, fully measurable DONE for the tactic arc.

Honest qualifications: (i) conditioned chains are not free — wordfreq's hand-built conditioned towers still peak ~2.0 GiB and needed the ≤8-link and opaque-parameter repairs; emission must build those limits in, and the residual cost driver (big concrete state terms at instantiation sites) is bounded by D-relative signatures, not eliminated. (ii) The *choice-dependent layout* class (rle's `n ∈ [4,8]`; any data-dependent allocation count) is NOT dissolved by emission at all — literal-address segments per spill history is the thing being multiplied. That needs the address-shift simulation lemma (g1.md:2549-2558). Grading it: **medium-hard, not research** — `Frame/Sim.lean`'s `FrameSim`/`stepFnIter_sim` is already a rename simulation over `stepFn`, and the needed lemma is a shift-above-a-base instance of the same family; but it is a real kit-lemma project over the whole step relation, and nobody should promise it in the same slice as T1. (iii) Corpus-wide build cost: 1,517 rfl segments already elaborate acceptably (worst modules 137–152 s); T1 changes marginal-example cost and the pathological tail, not the existing tree.

### The "~300-line afternoon" for a bubble-sort-class example

Bubble today: ~3,300 lines, roughly one worker session + integration. After the §4 slice-1 lifts alone (frame layer −430, family/copy −75, swapList −120, bail −55): ~2,600. With T1/T2/T3/T4 emitting the segment tower (~700–900), placements (~330), assembly (~230), and the audit-shard boilerplate: the *hand-written* residue is the Pure spec + invariant (~250–300, irreducibly intellectual — `BubbleInv`, `passL/passB`, the SortShared bridge), the iteration lemmas' statements (~100), headline + readouts (~80), and the gallery entry. **Honest verdict: ~400–600 hand-written lines and an afternoon is reachable; the literal 300 requires the placement-naming emission to work well, so state the target as "300–600" and let the acceptance measurement say which.** The floor below that is the spec layer, and it *should* resist automation — it is where the claim's content lives.

---

## 3. PARALLEL CONSTRUCTIONS DUE FOR GENERALIZATION

The consolidated list — ledger items verified against the tree, plus items the ledger missed or under-counted. Format: construction — consumers (landed) — proposed home — payoff.

1. **Threshold shift/rebase frame layer** — 5 (isort ×3, selsort, bubble; file:line in §1 P-D) — `Frame/Threshold.lean` — deletes ~420 of each ~430–470-line copy (≈ −2,100 landed) and is the whole overshoot of both sorts above the projected successor floor; every future loop-local-declaration example (the COMMON Go case, per g1.md:1944-1947).
2. **GAP-APPEND both arms + backing builder** — 4 (stack, queue, rle, wordfreq-`[]string`) — `SliceMem`, IntKind/elem-parameterized, spill capacity existential — ~200 lines/consumer; the queue entry's own words: "the next append example should not be the third module to pay it".
3. **The footprint pack** (`FreshFrom` algebra + `set_comm`-with-presence + heap set/lookup battery + `stepFn_return_frame`) — 5 copies (fibmemo, stein, sieve, wordfreq, + twosum precursor) — `StepKit` (or `Footprint.lean` beside it) — ~100–150 lines/consumer plus the not-false-by-accident lemmas proven once; explicitly marked DUE in the ledger (g1.md:3302-3308).
4. **`familyF`/`familyOf`/`familyDiv`/affine + signed `prefixPad` + `takePad`** — 8+ (twosum, rle, dedup, dotprod, kadane, stack, queue, SortShared's LCG; minmax delegation-only, designated vocabulary frozen) — `SliceMem` — ~60–80 lines/consumer → one-line delegations; the single most *frequently* re-derived shape in the ledger.
5. **`stepFnIter_iterate_bail`** — 5 (palin, strrev, twosum, bubble, rle) — `FuelMeasure` — ~55 lines/consumer and the disappearance of most surviving `strongRecOn` scaffolds (29 files still carry hand inductions).
6. **`swapList` surgery + count algebra** — 3 (selsort, bubble, isort's `bubbleState_swap`) — `SliceMem` — ~120 lines/consumer; `count_swapList` is the permutation half of every sort invariant.
7. **Key-generic `MapMem`/`MapLoops`** — 2 key types landed (Int; `List UInt8` via wordfreq's complete `*W` mirror family — `toEntriesW`, `scan_genericW`, `applyStrictOp_mapGetW`, `mapAssignValue_toEntriesW`, `snapshot_toEntriesW`, `mapPickLoopW`, `WordFreq/Count.lean:37-97`) — parameterize `MapMem` over the key `GoValue` embedding — deletes the ~1,000-line `*W` re-derivation class for every future string-keyed (or struct-keyed) map example. *Ledger under-counts this as "signal"; the wordfreq mirror is a full second instantiation.*
8. **Element-kind-generic store/index family** — 3 element types (kadane's 6 i64 mirrors GAP-I64; sieve's bool family GAP-B1; wordfreq's `[]string`) — `SliceMem` parameterized over `IntKind`+range window (and element type for non-int) — kills the twins-double-the-surface growth law; also resolves the sealed-API duplication sub-finding (g1.md:1320-1327).
9. **Op-fact completion** — `applyStrictOp_mul_u64` (3: powmod, sieve, +dedup's sibling), `div_u64` (3: powmod, dedup, rle), `add_u64`, `sub_int`, `eqCmp/neqCmp_int`, `convert_u64`, `not`, `atMostCmp`; the `unorm` normal-form family (`unorm_nat`, `unorm_mul_nat`, `unorm_nat_mod` — 2–3 copies each across isort/selsort/bubble/dotprod; `unorm_idem` fibmemo) and kind-generic `normalize_of_range` (strrev's i32 pair) — `SliceMem` — small each, but this is the "re-derived twelve more times" class; one lift as a *family* (the A1/A2 note: singly pays the fixture cost three times).
10. **GAP-RESLICE** (`applyStrictOp_sliceExpr_slice`, slice-base) — 3 (dedup, stack, queue) — `SliceMem` beside the array-pointer form.
11. **The four dequeue glue combinators** (`stepFn_block`, `stepFnIter_splice_pop`, `stepFnIter_drain3`, `stepFnIter_block_pop`, `SliceQueue.lean:3472-3503`) — 2 on arrival (queue landed; stack's exit analysis wants the same shapes) — `StepKit` P1 family.
12. **Growing-heap front support** (`lookup_front_none` simp-set/macro; `storeTarget_live` at the state level) — 3 (twosum ~120 lines, rle, sieve's per-pass scratch) — `StepKit`.
13. **`StringMem`** — 2 (strrev's four facts; wordfreq + its substring fact) — new module; explicitly *no heap half* (strings are values — the recorded negative finding, g1.md:1683-1686).
14. **Type-generic `palin_iff_half` + `getD_mem`** — 2 each (`List Int` / `List UInt8`) — `SliceMem` at `{α} [DecidableEq α] (d : α)`.
15. **`derive_entry_eq` string arm** — 2 (strrev, wordfreq) — EntryEq.lean:183.
16. **Call-span combinator** (P-H) — 2 (fibmemo, stein) — with the footprint pack.
17. **Ledger-missed, single-consumer today (record, do NOT lift per §12a):** the comma-ok `mapLookup` drain facts (`fm_lookup_drain_miss/hit`, fibmemo only — but comma-ok is idiomatic Go; expect the second consumer soon), the `ck_*` short-circuit step-glue spine (wordfreq only; E3 makes more `&&`-normalized bodies likely), `cap-8 normalizeValueForTy` alias cleanup (4 trivial copies — delete, don't lift).
18. **The address-shift simulation** (choice-dependent layouts) — consumer today is rle's *domain gap* rather than lines — `Frame/` (reuse `FrameSim`) — unlocks rle `n ∈ [4,8]` and every data-dependent-allocation subject; the one item here whose payoff is measured in claimable domain, not deleted lines.

---

## 4. THE PRIORITY ORDER

Ranking rule: marginal-example-cost reduction per unit of build risk, with the campaign's own measurements as weights (the kit-gap closure bought ~25% per successor for ~6 commits of pure lifts; the tracer bought "correct first time" for ~25 minutes).

**Slice 1 — the pure-lift wave (no elaborator work, all shapes pre-drafted in the ledger).** In dependency order: op-facts/`unorm` family + `familyF`/`takePad` + `swapList` (statement vocabulary first, the G1.1-KG lesson) → `Frame/Threshold.lean` → `stepFnIter_iterate_bail` → GAP-RESLICE + `stepFn_return_frame` + the queue glue combinators. Each lift: ≥2 landed consumers retrofitted + P6 rollback + `Audit/Kit.lean` pins in the same commit. Projected: ~2,500–3,000 landed lines deleted; sort-class marginal cost drops from ~3,300 to ~2,400–2,600; every remaining `strongRecOn` two-exit scaffold gone. Risk: nil — every statement already exists as a worked draft.

**Slice 2 — the new-shape wave.** Footprint pack (+ call-span combinator) → GAP-APPEND → `StringMem` → growing-heap front support → EntryEq string arm. These are the shapes the *hard* half of the gallery (recursion, dynamic allocation, strings, growing slices) pays for; consumers are 2–5 each, all landed. Projected: fibmemo/stein-class marginal cost down ~15%; the next `append` example stops being the third 7,000-line module.

**Slice 3 — the tactic arc (T1a → T5 → T2/T4 → T1b), with matmul as the flagship acceptance test.** Build `derive_seg` mode (a) + the storm lint first (they share the probe/quoting core), then the instantiation/assembly sugar, then conditioned-chain mode (b); attack the matmul snapshot with mode (b)'s output per the recorded pickup plan. DONE criterion: `matmul_ok` elaborated, gated, and shipped from the preserved snapshot — the strongest possible evidence the GAP-RFL-COST class is closed, on the exact artifact that discovered it. Per §5b.4/§12: every tactic lands with a fixture walk in the same change, anchored in `Audit.lean`.

**Slice 4 — the parameterization wave.** Key-generic `MapMem`/`MapLoops` (retrofit: wordfreq's `*W` family deleted to delegations) and kind/element-generic `SliceMem` (retrofit: kadane's i64 mirrors, sieve's bool family). Riskier than slice 1 (touching ~200-consumer modules under frozen pins — every pinned name survives as a delegation, the GAP-P1 pattern), which is why it comes after the tactic arc has reduced the cost of any re-derivation the retrofit shakes loose.

**Slice 5 — research-tier, scheduled only when its consumer is scheduled.** The address-shift simulation (unlocks rle `n ∈ [4,8]`). Grade: medium-hard, reuses `Frame/Sim`; do not gate anything else on it.

**What NOT to build** (recorded non-promotions, brick-wp meta-review style): a general WP-route tactic library (§5b's original plan — zero headline consumers under the §11 freeze); chained-client-call readiness (W3 — still zero consumers); any ghost-layer machinery (W4 — rung 0 stands); speculative per-`Stmt` parameterization of the counting layer (the C1 closure's own lesson: parameterize by what the witnesses vary, nothing wider); symbolic meta-level execution of `stepFn` for T1 (probe-driven classification is cheaper and fails just as closed).

The through-line: the campaign proved the kit carries examples at the *step* level (1,517 rfl segments, zero hand-rolled `stepFn` unfoldings anywhere) and — after G1.1-KG — at the *structure* level for flat counted loops and Int-keyed maps. The three structures still paid for by hand at ≥4 sites each (threshold frames, two-exit loops, growing slices/footprints) are all pre-drafted lifts; the residual ~40%-of-wall segment grind is transcription a macro can own, with `derive_entry_eq` as proof the approach works and matmul as the waiting, fully-specified acceptance test.

---

Report ends. Key sources: `docs/gallery-campaign-log/g1.md` (all gap drafts and measurements), `proofs/GoLeanProofs/{StepKit,SliceMem,MapMem,MapLoops,FuelMeasure,EntryEq}.lean`, `proofs/GoLeanProofs/Frame/{Sim,Transfer}.lean`, the five frame instantiations and five footprint copies at the file:line references in §1, `docs/2026-08-14_phase2-slice2-proof-library.md`, `docs/2026-08-15_brick-wp-promotion-wave-mapping.md`, `docs/2026-08-12_example-spec-form.md` §5b/§12, `docs/2026-08-16_gallery-campaign-trip-report.md`.

---

## OPERATOR CROSS-CORRECTION NOTE (rewritten 2026-08-16, fix round #2)

**Everything above this line is R5's report, verbatim and unedited.** Every
correction lives here. This note replaces a shorter operator-appended note
that was itself wrong on two points — recorded below rather than removed,
since a correction note that needed correcting is the most useful thing in
it.

**LINE-CITES ARE HISTORICAL.** R5 wrote against worktree tip `3aac907e`
(provenance header, and §Basis at :26). Bucket B's edits and fix round #2
inserted lines throughout `g1.md` — it went from 3,862 lines at `3aac907e`
to 4,075 at the time of writing (`git show
3aac907e:docs/gallery-campaign-log/g1.md | wc -l` → 3862; `wc -l` here →
4075) — so **the report's 21 distinct `g1.md` line-cites no longer resolve;
they are historical addresses.** (Count:
`grep -o 'g1\.md:[0-9][0-9]*\(-[0-9][0-9]*\)\?' docs/2026-08-16_wp-library-design.md | sort -u | wc -l`
→ 21. Note the anchor: `[0-9][0-9]*` and not `[0-9]*`, or the pattern also
matches the bare `g1.md:` in this note's own prose and answers 22 — the
same off-by-one-from-a-loose-pattern trap as (e) below, met twice in one
document.) Three
were spot-checked and all three now land on unrelated content (`:2649-2654`
→ was the frame-layer ledger item, now an `rle` cost row; `:3302-3308` → was
stein's consolidation signals, now the `SliceStack` cost table; `:1320-1327`
→ was the sealed-API sub-finding, now unrelated prose). **The CONTENT is
intact at the named units** — find it by unit name, not by line. The
report's cites into `proofs/` are mostly still good; two are not (see (c)).

### (a) `unorm_idem` — the C4 ruling, verbatim. The old note had this BACKWARDS.

The superseded note said: *"R2B also found unorm_idem already exists
kind-generically (HeapBridge.intKind_normalize_idem) — item 9's `unorm_idem`
line becomes an import fix, not a lift."* **The import route was REFUSED.**
The ruling is at `proofs/GoLeanProofs/Examples/FibMemo/Rec.lean:1359-1378`,
the docstring of `theorem unorm_idem`:

> GAP-WITNESS, and a CORRECTED one (post-autonomy audit, 2026-08-16).
> The ledger recorded this as a missing kit lemma; it is not. The
> kind-generic statement exists as
> `GoLean.Iris.intKind_normalize_idem` (`GoLeanProofs/HeapBridge.lean`).
> What it does NOT have is a home an example module can import:
> `HeapBridge` pulls in `Iris.ProgramLogic.*`, `Iris.ProofMode` and
> `Iris.BI.Lib.GenHeap`, and no module under `Examples/` imports Iris —
> Iris is a proof device, not an example-layer dependency (the
> statement-TCB/layering doctrine, `docs/2026-08-01_*`). So the audit's
> literal instruction (delete this and import HeapBridge) was NOT taken:
> it would have made this the first example module in the tree to import
> the Iris layer, to save four lines.
>
> The real item, recorded in `docs/gallery-campaign-log/g1.md` (fibmemo
> unit, promotion ledger): lift `intKind_normalize_idem` OUT of
> `HeapBridge` into a core/kit module (`SliceMem` or `StepKit`), then
> both this site and `HeapBridge` consume it. Consolidation-slice work,
> not audit-round work.

So the item stays **a LIFT, not an import fix** — and note the qualifier the
old note also got wrong: the namespace is `GoLean.Iris`, not
`GoLean.HeapBridge` (`HeapBridge.lean:22` `namespace GoLean.Iris`, theorem
at `:277`). The wrong qualifier hid exactly the layering fact that decides
the ruling.

### (b) GAP-P2b — kadane is **GAP-P2c**, and §1 P-B's list is stale on it

§1 P-B (`:45`) lists kadane twice: once in the `seed+i` affine bucket and
once, correctly, under "signed/Int-seeded". `:148` repeats it in the affine
bucket. **The affine listing is wrong.** kadane's `kadFamVal` is the SIGNED
variant — `docs/gallery-campaign-log/g1.md` records it as **GAP-P2c**
(*"`familyMod`/`prefixPad` do not fit a SIGNED, Int-seeded family"*, kadane
unit), and the GAP-P2b consumer list carries an explicit de-listing:
*"kadane was listed in error (its `kadFamVal` is the SIGNED variant, i.e.
GAP-P2c), and three landed consumers were missing"*.

**R5 is not at fault here.** At `3aac907e` the ledger's own P2b list DID
name kadane (`git show 3aac907e:.../g1.md` → *"kadane (in flight, same
`seed + i` shape)"*). The report copied a correct-at-the-time ledger; the
ledger was corrected in bucket B and the report was not. The corrected P2b
consumer set is **six byte-identical copies**: minmax, dotprod, reverse,
twosum, stack, queue. Priority unchanged — still over the §12 bar, by more
than the report thought.

### (c) Frame-layer attribution — R5 was RIGHT; the "ledger understated it" clause is now stale

The superseded note read *"the frame layer has FIVE hand sites (not four;
the ledger understated it)"*. The first half is right and the second half
has expired. **The tree has five**, confirmed directly:

```
grep -rn 'def ρ' proofs/GoLeanProofs/Examples/
  InsertionSort/PassFrame.lean:43  ρsh  (T=4)
  InsertionSort/Subject.lean:586   ρ11  (T=11)
  InsertionSort/Count.lean:770     ρ21  (T=21)
  SelectionSort/Frame.lean:46      ρ16  (T=16)
  BubbleSort/Frame.lean:33         ρ16  (T=16)
```

R5's body said five all along (`:55`, `:145`). The LEDGER said four at
`3aac907e` and now says five — bucket B corrected it *(`g1.md`, lane-B
six-example summary, promotion ledger item 1: "this line said FOUR while
enumerating five sites")*. So the discrepancy the old note describes is
resolved in the ledger's favour-of-R5 and no longer exists; attribute the
five to R5, and the correction to bucket B.

Two of R5's `file:line` cites for these are off by 2–3 lines (`:55` cites
`SelectionSort/Frame.lean:44,274,499` — actual `46,276,501`; and
`BubbleSort/Frame.lean:30,262,486` — actual `33,265,489`). The three isort
triples are exact.

### (d) `FreshFrom` — "5 copies" and "2 definitions" are both TRUE, of different things

The report's "5 program-local copies" (`:26`, `:62`, `:147`) is not a count
of definitions. **`FreshFrom` is DEFINED twice** and has been throughout:

```
grep -rn 'def FreshFrom' proofs/GoLeanProofs/
  Examples/FibMemo/Rec.lean:86   def FreshFrom
  Examples/Stein/Run.lean:96     private def FreshFrom
```

The five is the ledger's own breakdown — *"two FULL packs, one
`FreshFrom`-style pack without the def, and two partial cell-algebra
copies"* — i.e. the duplicated dead-region ALGEBRA, which is what a lift
would actually delete. Both figures stand; state which one you mean.

**One framing correction to the fix-round instruction itself:** this is NOT
a post-C3 drift. `git grep -n 'def FreshFrom' 3aac907e` returns the same two
hits at the same two line numbers, and `git grep -l FreshFrom 3aac907e`
returns the same five files. **Nothing about `FreshFrom` changed between
`3aac907e` and the tip** — the "2 definitions" figure was equally true when
the report was written. It is a definition/breakdown mismatch, not drift.

### (e) Kit pins are **116**, not 118 — the fix round was told to make this WORSE

The instruction for this note said to change 116 → 118. **Checked, and
refused: 116 is correct.** The pins are verbatim `#guard_msgs in #print
axioms <name>` lines in `proofs/Audit/Kit.lean` (no script, no list file).
The artifact-free command, and the only one of the three that is:

```
grep -c '^#guard_msgs in #print axioms ' proofs/Audit/Kit.lean      -> 116
```

The other two spellings both over-count on prose in the module docstring:
`grep -c '#print axioms'` → **118** (`:25` and `:36` are English), and
`grep -c '#guard_msgs'` → **117** (`:25` again). 118 is the unanchored
grep's answer, not the tree's. Unchanged since `3aac907e` (same command,
same 116; the file's last touch was `a202b402`, before the audit), so
`INDEX.md`'s "kit pins 81 → 116" is exactly right and stays.

Recorded at length because of the direction: a records pass was one paste
away from writing a wrong number into a doc, in the name of correcting it,
with a command that looked like a derivation. **The anchor is the
derivation.** A count is only as good as the pattern that produced it, and
"I ran a grep" is not a derivation until the grep is shown.

### The glue combinators — unchanged, and the one clause of the old note that stands

*"the glue combinators have ONE landed + one latent consumer (not two
landed)"* — correct, and the ledger now grades `GAP-CONVERT` the same way
(two copies, one used, one latent). Priority unchanged: at-bar via stack's
latent consumer, recorded not lifted.