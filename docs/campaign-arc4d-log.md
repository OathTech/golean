# Campaign arc4d log — SM1, the span-computes-model arc

Worker log for the arc4d scoping lane (branch `campaign-arc4d`, base
tip eee6b43b = the arc4 U25 exit). Unit: **SM1 — span-computes-model**
(U24's banked map; priced 1.5–2 units), closing the U23 checker
bridges to the bytes. Ground rules in force: NEW FILES ONLY (the
arc4b/arc4c precedent) — no existing tracked file edited, aggregators
untouched (the landing manifest at the end names the import lines the
operator adds at landing); one writer per worktree; build-lock
protocol for full builds; sibling `campaign-arc4` namespace/files
untouched.

## SM1 successor re-verification (2026-08-26, fresh worker)

U24's banked span-model anatomy spot-verified against the artifacts
it cites (read-only, from the sibling worktree's gitignored
`artifacts/probe/` — the probes themselves were NOT touched):

- `utoacensus.out` verbatim: utoa(0)=28 steps, utoa(7)=151,
  utoa(42)=218, utoa(12345)=419 — the banked formula
  **151 + 67·(digits−1)** reproduces all four (28 zero-branch;
  151+67·0; 151+67·1; 151+67·4). PASS.
- `utoatrace.out` / `utoatrace2.out`: the plain-for desugar shape
  read directly off the config dumps — `$forFirst` latch inside
  `while true`, `seqn []` prep slot, `if cond then seqn [] else
  break`, body block; frame env scopes
  `[[], [$forFirst], [s], [$res0, v]]` exactly as banked. PASS.
- The kit-gap claim (SliceWalk covers ONLY the range desugar) checked
  against `GoLeanProofs/SliceWalk.lean` — its shape vocabulary is
  `$rcoll/$rlen/$ridx/$rfirst` with a fixed bound check; no plain-for
  schema exists anywhere in `GoLeanProofs` (grep). PASS.
- Worktree state at start: clean at eee6b43b; no build cache. Warm
  start: `.lake` + `proofs/.lake/build` rsync'd read-only from the
  sibling (the `setup-deps --from` precedent), then VALIDATED by a
  full default-target build under the box-wide build lock
  (`artifacts/lockbuild.sh`, mkdir-lock + owner file + trap release,
  96G, LEAN_NUM_THREADS=16): **"Build completed successfully
  (529 jobs)", exit 0** — the U25 corpus-split job count, as
  expected at this tip. Lock acquired and released cleanly.

Fresh probes for this arc (all gitignored, this worktree's
`artifacts/probe/`): `UtoaDump.lean` → `utoadump.out` (the verbatim
lowered `utoa` Func — the pin's source), `HarvestDump.lean` →
`harvestdump.out` (verbatim `main.twin.viol` / `main.twin.harvest`
incl. the S1 record block / `main.twin.apply`), `DigitBodyProbe.lean`
→ `digitbody.out` (the 44-step digit-body config chain, every
continuation shape transcribed from it), `BodyPathProbe.lean` →
`bodypath.out` (whole-body walks: v=0 → `.returning FRAME` in 25
steps; v=7 → 148 steps = 37 entry + 96 loop + 15 tail — the census
totals re-derived from a fresh angle), `HC1Bisect{,2}.lean` (the
splice-at-symbolic-env bisect, below).

## SM1 slice 1 — `Sym/UtoaForKit.lean`: THE PLAIN-FOR HEAD SCHEMA
(the unit's one new kit piece; DELIVERED)

The `CondFor` namespace, built in the SliceWalk pattern (LINEAGE:
Floyd/Hoare loop invariant — the docstring carries it):

- Shape vocabulary `flagIf/condIf/wbody/cwhile` — the cond-only
  plain-for desugar, verified verbatim against `utoadump.out` (and
  the harvest loop's same skeleton in `harvestdump.out`). Scope per
  §7 middle-path: the cond-prep slot is fixed EMPTY (pure-expression
  conditions); the call-conditioned variant (harvest's
  `for HasReady()`) is the recorded latent consumer of the
  prep-parameterized generalization, deliberately not built ahead of
  demand.
- Glue segments, measured against the trace and proved conditioned:
  glue_first **19** steps (17 range-schema glue + 2 for the prep
  slot), glue_next **12**, cond entry 1, branch_true 3, branch_false
  4, back edge 2.
- **`condFor_loop`** — the schema: state family `S`, instance cond
  fact (state-untouched Bool delivery, `decide (i < n)`), instance
  body fact (bounded completion + invariant), conclusion
  `∃ m ≤ (25 + bC + bB)·(n − i) + 24 + bC` to `.next k` at the
  exit-glued `S n` state. Bounded-completion form (I2).
- **Discharge witness (same slice, non-checker)**: the countdown loop
  `for c > 0 { c = c - 1 }` — cond fact (5 steps), body fact (12),
  `countdown_span` (`∃ m ≤ 42n + 29`), symbolic in `n`, plus the
  concrete two-cell instance `cd_concrete` (every premise discharged
  on real cells).

Verification: `lake env lean` exit 0, zero warnings; olean built via
explicit target (`lake build +GoLeanProofs.Sym.UtoaForKit`, 20 jobs,
exit 0, lock-exempt ≤48G).

- What-this-taught-us (a): **`seqn` splice does NOT reduce at a
  symbolic env** — `stepFn`'s splice arm carries an env-equality
  `DecidableEq` check (`if_pos trivial` in the kit single), so any
  multi-step `with_unfolding_all rfl` chunk crossing a splice fails
  at a free `envW`; the kit singles (`stepFn_seqn_splice`,
  `stepFnIter_splice_pop`) exist precisely for this. Found by the
  3-line bisect probe (`HC1Bisect.lean`), cost minutes — the
  anti-grinding drill applied at the first wall.
- [AGENT] The `+ (1 + mC)` count-shaping convention: chained segment
  counts must match the statement's literal sum SHAPE (Nat `+` is not
  defeq-associative on open terms; the first attempt's `+ 1 + mC`
  spelling sent the elaborator's whnf into the `stepFnIter` fuel and
  timed out). All schema statements now carry counts in the chain's
  own association; downstream bounds go through `omega` with the
  glue-size case split abstracted (`hgs : (if i = 0 …) ≤ 19`).

## SM1 slice 2 — `Sym/UtoaSpan.lean`: THE UTOA WEAK SPAN (the banked
∃-string form; DELIVERED)

- **`utoa_pinned`** — the whole lowered `Func` (body incl. the digit
  loop spelled in the `CondFor` vocabulary, signature, wrapper flag)
  equals `findFunctionIn? twinLowered.funcs ⟨"utoa"⟩` by
  `kernel_rfl`: the strongest byte anchor yet used for a span module
  (whole-Func equality, not per-guard `.any` pins). A re-lowering
  that reshapes `utoa` turns it red.
- **`twinSt` carrier + `twinSt_of_agrees`** — the four twin tables at
  a symbolic heap/frontier; any `bfTB.Agrees` state transports in
  (the window modules' premise composes directly).
- **`utoa_enterFrame`** — `enterFrame` at the twin tables, symbolic
  heap/frontier/argument, by `kernel_rfl` on the raw form +
  normalization discharge. The two frame cells at the frontier.
- **`dig10`** (WF on `v/10 < v`) + **`dig10_iff`**
  (`i < dig10 v ↔ 0 < v / 10^i`, strong induction) — the measure the
  loop schema consumes; `div_pow_succ` is the body's tower step.
- New conditioned singles (kit-shaped, all `∀σ`):
  `applyStrictOp_greater` (general kinds), `applyStrictOp_add_string`,
  `applyStrictOp_convert_int`, `applyStrictOp_convert_i32` (+
  `i32norm_nat_of_lt`), `normalize_string`, `normalize_int_u64`,
  `defaultValue_string`, `defaultValue_bool`.
- **The digit-loop instance**: `UtoaInv` (latch schedule, `v/10^i` in
  the v-cell, **∃-string in the accumulator — the weak form; no
  decimal modeling**); `utoa_cond_fact` (5 steps, decide-transport
  via `dig10_iff`); `utoa_body_fact` (**44 steps**, the
  `digitbody.out` chain transcribed segment-for-segment; post-state
  exposed as `digitPost` for frame reasoning). `UtoaFrame` (frame
  clause: all non-working cells match a reference heap, parked
  frontier, `Agrees`) + preservation lemmas; **`utoa_loop_span`**:
  `∃ m ≤ 74·dig10 v + 29` through `condFor_loop`.
- **`utoa_body_span`**: entry segment (37 steps, `v ≠ 0`), zero path
  (25 steps), exit tail (15 steps), assembled:
  `∃ m ≤ 74·dig10 v + 81, ∃ str, ∃ σ'` — `.returning` the frame with
  SOME string in the result cell, frontier `+0/+2`, frame respect
  (`∀ x < na₀, x ∉ {v-cell, res-cell}` unchanged), freshness
  preserved, `Agrees` preserved.
- **`utoa_call_span`**: the P-H combinator (`stepFnIter_call_span`)
  closed at `utoa` — from the delivered argument under
  `.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref tgt])]` to the caller's
  resumption (`.exec (.seqn #[]) envC Kc`), `∃ m ≤ 74·dig10 v + 87`,
  target cell = SOME string, four dead frame/loop cells between the
  frontiers. This is the exact shape the S1 record span's three
  `$c229x := utoa(…)` sites consume.

Verification: `lake env lean` exit 0, zero warnings; olean via
explicit target (40 jobs, exit 0). Step counts cross-checked against
the compiled walks in `bodypath.out` (25 / 37+96+15 = 148) before
proving — #eval-first throughout.

- [AGENT] calls, tagged:
  1. The ∃-string weak form implemented exactly as banked (U24's
     design): the invariant, body span, and call span never name the
     digit bytes — the S1 consumer needs only "SOME string" (the
     checker's counters are text-independent), which halved the
     digit-body obligations as priced.
  2. The whole-Func pin (`utoa_pinned`) chosen over guard-granular
     `.any` pins: `utoa` is small enough that whole-body kernel
     equality is cheap, and the span statements quote the body
     verbatim — the pin makes the quoted vocabulary THE bytes with
     one theorem.
  3. The body span is stated `∀σ` (table-free — measured: no step in
     the body consults the tables) with `Agrees` only THREADED for
     the consumer; `enterFrame`/call layers sit at the `twinSt`
     carrier with the `twinSt_of_agrees` transport. Statement
     strength follows the machine's actual footprint, not the
     carrier convenience.
  4. `Mathlib`-flavored tactics (`set`, `conv_lhs`, `by_contra`,
     `norm_num`) are NOT available in this tree; replaced with
     core-form equivalents on first contact. Recorded so successors
     stop rediscovering it.

## Interference/ops note

None so far this session: zero SIGTERM kills, all builds/probes exit
0 (the U24 reaper fingerprint has not fired). Build-lock used for the
one full build; everything else explicit-target/`lake env lean`
under 32–48G caps with captured exit codes.
