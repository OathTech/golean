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
  avoidable — REVISED, see D-8).** Initial plan: the inverse
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
