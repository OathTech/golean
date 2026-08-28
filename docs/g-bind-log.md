# G-BIND unit log (worktree u0-iris, branch g-bind)

Unit charter: `docs/2026-08-28_iris-corpus-plan.md` §4.1. Executor:
[AGENT] Fable, session 1 (priced 1.5–2 sessions). Base: main
`c484cef9` (U0 landed; pin `e7a0a438`, Lean 4.32.2).

**Quantifier-audit line (per charter, §4.1's line restated):** this
unit advances the **∀ caller contexts / frames** quantifier of every
corpus sentence, by the **bind/fill rule** (`wp_bind`-shaped over our
`plugC` fill) — control composition: the composition half that lets a
function spec proved once at its canonical configuration apply at
every call site inside larger programs. Never by per-arity or
per-context instances.

**LINEAGE:** the ectx-language bind rule (Iris `EctxLanguage`/
`wp_bind`; Felleisen–Hieb evaluation contexts); Perennial analogue
GooseLang `LanguageCtx'`. Divergence: our continuations are
CONFIGURATION DATA (defunctionalized CEK spine), the fill is the
below-barrier replacement `plugC`, and the language has a two-step
panic-abort terminal (`.panicking → .panicked → stuck`) that forces a
context-side drain premise the classic rule does not have (finding
F-3 below).

---

## Session-1 decisions

- **[AGENT] D-1 (brief/plan id conflict resolved to the plan).** The
  executor brief labels the gate instance "C-01" while describing "a
  small two-function Go program (one function calling another, the
  caller doing something with the result)". The plan of record §5.2
  assigns C-01 = `mapwalk` (G-MAPITER's gate) and **C-05 =
  `callchain`** (G-BIND's gate: "nested static call with a defer,
  proved once through `wp_bind` at an open caller context"). The
  description matches C-05; the plan is the plan of record; the gate
  criterion (proof USES `wp_bind`) is C-05's. Resolution: build
  **C-05 `callchain`**; the brief's "C-01" is read as "the first
  corpus program built", which C-05 now is. Flag for the coordinator.
- **[AGENT] D-2 (route (a) — pin `Context` instance — assessed and
  REFUTED, ~30 min).** The plan's A5 said the instance route is
  unavailable; verified rather than assumed, with a concrete
  counterexample sharper than A5's reason: for `K = plugC env' k'`,
  the pin's unconditional `primStep_fill_inv` (`Language.lean:277`)
  is **false** — take `e = .returning .stop` (irreducible: a return
  with no frame has no rule) and `k'` containing a frame; then
  `K e = .returning k'` DOES step (pops `k'`'s frame), and that step
  decomposes as no step of `e`. The bare-`.stop` plug arm lets
  context steps leak into non-barrier configurations, which is
  exactly what the `hasBarrierC` premise excludes — and a premise on
  `e` cannot be baked into a typeclass instance whose laws quantify
  over all `e`. **Route (b) it is** (the direct premise-conditioned
  bind lemma). Measured comparison: route (a) cost ~30 min to refute
  on paper + the counterexample recorded here; route (b) is the rest
  of this unit.
- **[AGENT] D-3 (the machine-level inverse, no second walk if
  avoidable — REVISED; see Session-1 results).** Initial plan: the inverse
  decomposition via `stepFn`-level error-transfer walk
  (`fun_cases`). Before paying it, probe two arms (plan's
  probe-first pricing rule).
- **[AGENT] F-3 (NEW SEMANTIC FINDING — the naive partial-WP bind
  statement is FALSE without a context-drain premise).** The plan's
  §4.1 priced `primStep_fill_inv` as the new obligation but did not
  anticipate this. Derivation: a step from a barrier configuration
  can cross the barrier (`.panicking chain (.frame [] te r [] .stop
  false) → .panicking chain .stop` — the panic pops the barrier).
  The canonical run then aborts in ≤2 steps (render → `.panicked` →
  stuck), so `WP c @NotStuck` refutes crossing SEMANTICALLY — but
  the step-indexed refutation lags the plugged run by one step, and
  the plugged drain `.panicking chain k'` can get stuck EARLIER than
  the canonical render for garbage `k'` (e.g. a `k'` frame whose
  deferred call is an unsupported construct). At that step index the
  hypothesis is still true and the conclusion already false:
  **`WP c {{_, WP (.next k') {{Φ}} }} ⊢ WP (plugC env' k' c) {{Φ}}`
  is not valid for arbitrary `k'` satisfying only the two §7
  premises.** The minimal repair (adopted): a third context premise
  `hdrain : ∀ chain σ, Reducible (.panicking chain k', σ)` — the
  HEAD of the context's panic-drain always steps. With it, the
  crossed case is refuted inside the proof with exactly the budget
  available: round n+1 shows the plugged drain reducible (hdrain),
  receives fresh credits, interrogates the canonical crossed WP
  (render step exhibited, `WP (.panicked msg)` extracted, its
  reducibility conjunct is False at NotStuck). `hdrain` is
  discharged at concrete call sites by one constructor application
  (the panic-passthrough arm for pop-heads); helper lemmas provided.
  Scope note: the bind lemma is stated at `s = .NotStuck` (the
  refutation consumes the reducibility conjunct; `MaybeStuck` has
  none). All WP specs on the Surface exit path are NotStuck, so no
  consumer is narrowed.
- **[AGENT] D-4 (C-05 composition is heap-mediated — the machine's
  geometry, not a dodge).** The plug barrier is the targetless,
  resultless frame (`.frame [] _ _ _ .stop false`), and the machine
  has NO rule for a targetless frame with pinned results
  (`Machine.lean:3218` comment) — result-bearing calls always get
  targets, and target write-back evaluates in the CALLER env, which
  is exactly what a canonical (empty-context) span cannot run. So
  the bind rule composes callee BODY SPANS of resultless callees at
  bare call sites; value plumbing through targets is G-CALLS's
  return-law territory (the plan agrees: G-CALLS §4.3 owns
  `wp_frame_return` and result cells). C-05 therefore lets the
  callee return its result THROUGH THE HEAP (a pointer parameter —
  ordinary Go), and the caller "does something with the result" by
  reading that cell after the call. The brief's composed-FnSpec gate
  criterion is unchanged: the callee's spec is applied at the call
  site through `wp_bind`, three times (caller→ccWork, ccWork→ccDouble,
  and the deferred ccBump at the drain site, which is also a plug
  image).
- **[AGENT] D-5 (C-05 totality piece).** The plan's §5.2 C-05 row
  lists FnSpec + readout + negative twin, NO `Terminates` (totality
  "where apt" — the symbolic-totality machinery is G-TOTAL's, §4.7,
  and `allStreamsOk` enumeration is banned for new members, §2d).
  The landed `TotalWp` theory has only the instance pin + two seqn
  laws — no store/call/bind twins — so a C-05 `Terminates` through
  total-WP is G-TOTAL-scale work, not a quartet line item here.
  Registered as an owed row at G-TOTAL (with C-15 and C-01), per the
  plan's own assignment. The brief's "totality via TotalWp if
  loop-free" is answered honestly: not in this unit's budget, owned
  by the unit the plan assigns it to.
- **[AGENT] D-6 (scripts/ touch).** `scripts/check-golden` gains one
  PINS row + one build-list entry for the C-05 pin (the golden
  discipline: pinned from birth). The A-TRIP sibling lane owns a
  lint over `scripts/`; this is a data-row addition to an existing
  script, kept minimal and flagged here for merge-time conflict
  awareness.
- **[AGENT] D-7 (N-3 posture).** Gate N-3 (corpus-design sign-off)
  reviews the corpus roster; the plan carrying C-05 was
  [USER]-approved at N-1, and N-3's own rule 2 says the first BUILT
  corpus case returns for a conformance look. This session builds
  C-05 as chartered and DESIGNATES NOTHING (candidates marked in
  docstrings, N-5 untouched).

## Session-1 results ([AGENT], 2026-08-28)

**Landed, in order (tip at each step):**
1. `89527243` — C-05 corpus case + golden pin (3/3 differential green;
   both check-golden links green).
2. `a162f5ee` — `Frame/PlugInv.lean`: the fill–step inversion.
   `stepFn_plug_err` (the error-transfer walk), `stepFn_plug_ok_inv`,
   `step_plug`, `step_plug_inv` (= `primStep_fill_inv` for our
   geometry), terminal/value lemmas, `hdrain` step exhibits.
3. `22afd963` — `Laws/Bind.lean`: `wp_crossed_of_canonical` +
   **`wp_plug_bind`** (THE BIND RULE) + `wp_bind_plug` (entailment
   shape) + the two `hdrain` dischargers.
4. `45c740ae` — `Specs/Callchain.lean`: the C-05 quartet through the
   bind rule (3 bind applications) + 4 supporting general laws
   (`wp_call_enter_arg2`, `wp_defer_callee_arg`,
   `wp_defer_register_args`, `wp_frame_defer_fall_arg1`).

**The measured route comparison (charter ask):** route (a) — the
pin's `Context` instance — cost ~30 min to assess and REFUTE
(counterexample in D-2; no code written). Route (b) executed:
- the inverse decomposition (PlugInv): ~2.5 h of iteration; the walk
  itself compiles in ~26 s. The plan priced the inversion as "new
  proof content the W2 forward walk did not pay for" — the actual
  cost was LOWER than a second commutation walk because the
  error-transfer formulation reuses the forward walk's landed
  `_plug`/`_bar` helper equations wholesale and the ok-direction
  comes free from `stepFn`'s functionality (D-3 revised: no second
  commutation argument exists in the tree).
- the bind rule itself: ~1.5 h (the pin's `wp_bind_iff` forward
  branch adapted; the crossed-case machinery is the new content).
- the gate instance: ~2.5 h (three canonical specs + harness +
  quartet; the leaf walks are `GoldenSliceWP`-idiom hand walks).

**[AGENT] F-4 (recorded boundary — the `hdrain` premise at
defer-carrying contexts).** `hdrain` quantifies over ALL states, so at
a context whose HEAD frame still carries deferred entries the drain
step is an `enterFrame` whose success is state-dependent — the two
shipped dischargers cover pop-headed and defer-FREE frame-headed
contexts only. In practice call sites sit under sequence glue (the
frontend's block/seqn desugars), so the head is a pop; if a future
walk hits a bare defer-carrying head, the options are a
program-pinned `hdrain` variant or a `σ.functions`-conditioned drain
lemma. Recorded, not needed by C-05.

**Non-vacuity:** every new law names `Specs/Callchain.lean` as its
discharge witness in its docstring; the bind rule's witness is the
C-05 quartet itself (three applications, checked in-build).

**How a skeptic verifies the proof genuinely goes through `wp_bind`:**
(i) `grep wp_bind_plug proofs/GoLeanProofs/Specs/Callchain.lean` —
three application sites, one per call/drain site; (ii) the callee
bodies (`ccDoubleFunc.body` etc.) are mentioned ONLY in their own
canonical-spec theorems, never inside another walk — the call sites
apply the specs, and deleting `wp_plug_bind` breaks all three
compositions (`Laws/Bind.lean` is on the import spine of the
quartet); (iii) the canonical specs are stated at `k = KB` (the
barrier over `.stop`) — no caller context appears in them, so the
composition into concrete contexts CANNOT have been proved there.

**PlugWitness retirement condition:** the G-BIND gate instance now
exists; per the recorded condition ("retire these, or re-point them
at the G-BIND instance"), the witnesses are RE-POINTED (docstring
edit, same commit) — actual retirement (Audit pin removal =
trust-adjacent) is left to the coordinator with the audit.

**Owed to session 2 / the coordinator:**
- baseline re-pin after the wave-boundary full differential (this
  session runs `scripts/ci --diff`; the 3 new rows join the baseline
  with this log as the written reason).
- C-05 totality via G-TOTAL (plan-assigned; D-5).
- The per-arity enter laws' "widening owed" notes (Laws/Call.lean)
  can now cite the bind rule as the collapse path — G-CALLS's
  charter, not touched here.
- `go_walk` registration for the new laws (they carry
  `@[go_walk_law]` where the shape fits) — G-AUTO's probe will
  measure; the C-05 walks are hand-walks in the GoldenSliceWP idiom.
