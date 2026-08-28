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
  REFUTED, ~30 min; wording tightened at the audit fix round, F3).**
  The plan's A5 said the instance route is unavailable; verified
  rather than assumed, with a concrete counterexample sharper than
  A5's reason: for `K = plugC env' k'`, the pin's
  `primStep_fill_inv` (`Language.lean:277`) — which carries the
  premise `toVal e = .none` — is **false**: take
  `e = .returning .stop` (NOT a value, so the premise is SATISFIED;
  and irreducible — a return with no frame has no rule) and `k'`
  headed by a POPPABLE frame (`.frame [] te [] [] k₂ w` — no
  targets, no results, no defers — so `Step.frameReturn` fires; a
  frame with pinned results is deliberately stuck, so the witness
  must be this shape). Then `K e = .returning k'` steps, and that
  step decomposes as no step of `e`. The bare-`.stop` plug arm lets
  context steps leak into non-barrier configurations, which is
  exactly what the `hasBarrierC` premise excludes — and a premise on
  `e` beyond `toVal e = .none` cannot be baked into a typeclass
  instance whose laws quantify over all `e`. **Route (b) it is**
  (the direct premise-conditioned bind lemma). Measured comparison:
  route (a) cost ~30 min to refute on paper + the counterexample
  recorded here; route (b) is the rest of this unit.
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

**[AGENT] F-4 (REVISED at the audit fix round, F1 — the `hdrain`
premise's measured bound).** The audit sharpened this from
"undischargeable" to **FALSE**: at a defer-DRAIN bind site whose
context frame still carries ≥1 remaining deferred entry — i.e. a
subject function with **≥2 live defers** (`defer a(); defer b()`,
routine Go, pervasive in raft) — `hdrain` as stated does not hold:
the drain head's step is `panicFrameDefer`, whose `enterFrame`
premise is state-dependent (a `σ` whose function table lacks the
deferred `fid` has NO step), while `hdrain` quantifies over ALL `σ`.
C-05 passes because `ccWork` has exactly ONE defer, so the drain
site's context frame is defer-free (`drain_reducible_frame`
applies); ordinary call sites sit under sequence glue, so their
heads are pops. Both remedies collapse to ONE fix: a σ-CONDITIONED
restatement of `wp_plug_bind` (`hdrain` receiving the program pins
the state interpretation already carries).

**NAMED OWED ROW (converges with the outsider audit's R4): the
context-premise debt.** One row covering all three of
`mapIterFree k'` / `recoverThroughWrappers k' = none` / `hdrain`:
today each is discharged per-site by computation on concrete
spines, and `hdrain` is additionally σ-blind (above). OWNER: a
σ-conditioned bind-variant unit (restate `wp_plug_bind` with the
premises conditioned on the pinned tables, subsuming the current
form). TRIGGER: G-MAPITER or G-CALLS chartering — or the first
corpus member with ≥2 defers in one subject function, whichever
comes first.

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
composition into concrete contexts was not proved there.
**Honesty note (audit F6):** (iii) shows where the composition was
NOT proved, not that no bind-free route existed — `wp_ccCaller_body`
itself is the counterexample shape: a ∀-k walk with computable
context premises IS a bind-free route for a caller body, and this
unit did NOT measure bind-vs-∀k cost (the measurement-referees
rule). Recorded as a G-AUTO probe question: measure the two idioms
on one member before the corpus wave standardizes on either.

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

## Wave-boundary gate record ([AGENT], 2026-08-28)

- `scripts/capped scripts/ci --diff` at `c43dffd2` (pre-re-pin):
  every step green EXCEPT the baseline diff, whose only drift was the
  3 new C-05 rows (all PASS) — the anticipated case-set change.
  Differential: full, 2478 cases (2306 pass / 172 fail — failing set
  unchanged vs the 2026-08-22 baseline).
- Baseline re-pinned from that full run (`298ee662`; reason in the
  baseline header + this log). `coverage-baseline-diff --full`: no
  regression.
- `scripts/capped scripts/ci` (plain) at `298ee662`: **PASS, rc 0**
  (baseline diff FULL 2478/2478; staleness note only — the recorded
  run was 2 docs/baseline commits behind).
- `scripts/capped scripts/ci --diff` re-run AT the re-pinned tip:
  **PASS, rc 0, wall 217.9 s**, no baseline staleness.
- Judge: NOT run — no designation change, no trusted-closure
  movement; the comparator landmark note stands at 51 theorems /
  118 s @ `534f2710` (pre-branch). The pre-merge ceremony (audit ask
  + any judge re-run) is the coordinator's.
- Axiom envelope spot-check: `callchainSpec`,
  `callchainReturnsFourteen`, `callchainNotThirteen`, `wp_plug_bind`,
  `step_plug_inv` all depend on [propext, Classical.choice,
  Quot.sound] only; no `sorry`, no `partial`, no `native_decide` in
  any new file.

**Park state: G-BIND session 1 COMPLETE at a coherent boundary** —
the bind rule + inversion landed and gated, the C-05 gate instance
closed through the rule, corpus/differential/golden-pin/baseline all
green. Session-2 remainder: the owed list above (G-TOTAL totality
row, per-arity widening-note re-pointing under G-CALLS, go_walk
registration measurement) plus the coordinator's audit ask.

## Audit fix round ([AGENT], 2026-08-28; coordinator's fix list)

The audits returned SOUND on the proof content (Löb structure,
inverse lemma, NotStuck scoping, the D-2 counterexample, the twin's
discriminator; the outsider referee read `Callchain` line-by-line).
Fix round applied on `g-bind`:

- **F4b/F4d/F4c (the one data fix)** — `baselines/native-full.tsv`:
  the re-pin had pasted the 5-column RESULTS header over 3-column
  rows; restored `result/id/stage`. The dropped failing-set
  classification block (BUG-062 by-design rows + the A6
  PASS-controls note) is carried forward in the new header,
  explicitly marked unchanged. F4c on the record: the re-pin
  REGENERATED the file in the run's row order — the line diff is
  ~1800 lines for a 3-row set change; the set-diff cleanliness is
  what `coverage-baseline-diff` verified (do not re-derive this from
  the line diff).
- **F1** — F-4 re-worded to the audit's measured bound (hdrain FALSE
  at ≥2 live defers, not merely undischargeable) + the named
  context-premise-debt owed row (converging with outsider R4); see
  the revised F-4 above.
- **F3** — D-2's "unconditional" adjective dropped here and in
  `docs/2026-08-28_u0-refresh-log.md:103`: the pin's law carries
  `toVal e = .none`; the counterexample SATISFIES that premise, so
  the refutation stands as stated precisely. The "k' containing a
  frame DOES step" phrasing tightened to the poppable-frame witness
  (a frame with pinned results is deliberately stuck).
- **F7** — `wp_defer_register_args` gets its missing non-vacuity
  witness docstring (cites the `ccWork` walk in the callchain
  walks file).
- **F6** — skeptic-check (iii) softened + the unmeasured bind-vs-∀k
  alternative recorded as a G-AUTO probe question (above).
- **F8** — `wp_call_enter_arg2` is the EIGHTH member of the
  per-arity entry family the charter says the bind rule should
  collapse; the collapse is G-CALLS's charter (recorded there by the
  plan), and the audit names the CROSS-PRODUCT gap explicitly: the
  return-path and panic-path `arg1` analogues
  (`wp_frame_defer_fall_arg1`'s siblings) multiply the same
  per-arity axis — G-CALLS owes the list-indexed collapse across
  the whole product, not just the call-entry axis.
- **F9 (retroactive [TRUST-ADJACENT] flag)** — the
  `scripts/check-golden` touch in `89527243` (one PINS row + one
  build-list entry + one import line for the C-05 pin) was
  trust-adjacent per the charter's delta-flag rule and was not
  flagged at the commit; flagged HERE retroactively. The edit is
  data-only (no logic change) and strictly STRENGTHENS the gate
  (one more pinned program under both links).
- **F10 (two scope bounds, recorded)** — (i) the bind rule's
  barrier is the NON-WRAPPER frame (`wrapper = false` is part of
  `hasBarrierK`'s pattern, inherited from the §7 census: wrapper
  frames are transparent to Go's recover walk); wrapper-callee
  composition is out of scope by design. (ii) NO cross-barrier
  panic COMPOSITION: `wp_plug_bind` refutes the crossed case rather
  than composing a panic postcondition — inherent to NotStuck over
  this machine (an escaped panic aborts in ≤2 steps), so a
  panic-propagating bind (caller recover catching a callee panic
  through the barrier) is a different rule, not a weakening of this
  one.
- **F2/F5/R1** — the PlugWitness re-point correction, the Audit pins
  (`wp_plug_bind`, `step_plug_inv`, the quartet exit sentence), the
  `Audit/W2.lean` wording fix, and the in-tree scaffold labels for
  the `allStreamsOk`-route `Terminates` tier: batched in the single
  trust-adjacent Audit commit (delta-flagged; judge at the
  ceremony). Pin-cost measurement for `step_plug_inv` recorded with
  that commit.
- **Sibling coordination** — `Specs/Callchain.lean` SPLIT per the
  A-TRIP lane's file convention: WP walks + canonical specs in
  `Specs/Callchain.lean` (the future police class), the four
  first-order sentences + the `goSpec` exit in
  `Specs/CallchainSentences.lean` (the boundary-sentences class).
  Enrollment in their scope config is NOT done here (that file is
  theirs; enrollment at the post-merge rebase).
