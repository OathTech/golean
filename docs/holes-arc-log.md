# Holes arc log — the census's confirmed silent-wrong-answer holes

Branch `holes-arc` off main @ `720e02fb`, worktree
`.claude/worktrees/holes`. Charter: the follow-on arc for
`docs/2026-08-21_w7-desugar-inventory.md` §10 — fix H-a and H-d (both
CONFIRMED live silent wrong answers), harden H-b's latent decoder arm,
reconcile the two recorded doc drifts, and teach `scripts/setup-deps`
the `proofs/.lake/packages` population. NOT in scope: H-c (W7 tier-0,
own design), H-e (probed, not a divergence — census row already
honest), H-f (unprobed identity collapse — census row already honest).

Conventions: bugfix-arc (guardrails first, predicted flips written
before the confirming run, re-pins and BUGS.md in the same commit as
the movement they record). One commit-group per item, full
`scripts/ci --diff` per landing. Commits by explicit path only — the
raft-w42 lane runs concurrently and owns `raftsubject/` +
`tools/raftsubject`; this lane owns the frontend, `NativeToIR.lean`,
`Corpus/`, `baselines/`, and this file.

## Item 1 — BUG-066 (census H-a): elided-high slice base double emission

- Guardrails written first; gc probed directly (artifacts scratch,
  `go run`): callBase 130, callBaseLowOnly 120, explicitHighControl
  130, pointerArrayBase 123, stringElidedHigh 1328.
- Pre-fix machine witnesses, exact to the predicted double-call
  values: 230, 220, 130 (control PASS), 223, 12228. Six-row slice run
  2026-08-21, `stage=differential` on all four reds.
- Judgment call: the census's first-pass witness `f().arr[2:]` with a
  value-returning `f` is not legal Go (array through a call result is
  unaddressable); the pointer-returning `pf().arr[2:]` form from the
  audit round is what the corpus row pins.
- Judgment call (fix shape): slices/strings reuse the ONE emitted base
  node as the `builtin-len` operand — for pure bases this is
  byte-identical wire (the old second emission of a pure expr produced
  a structurally identical node), so only effectful bases change
  shape. Array bases take the static length constant as the default
  high (spec: the default is `len` OF THE ONE EVALUATED OPERAND; for
  an array operand that is the compile-time length) — this changes the
  wire shape of every array-base elided-high slice from
  `builtin-len(second emission)` to an int literal, so golden repr
  pins may re-pin in the fix commit, with this as the reason.
- PREDICTED FLIPS (written before the confirming full run): exactly
  the four pinned reds FAIL→PASS
  (slice-elided-high-eval-once/{call-base,call-base-low-only},
  slice-elided-high-pointer-array-base, slice-eval-order-elided-high);
  zero other movement; goldens unchanged (check-golden ran clean
  post-fix — no golden program slices an array with elided high or an
  effectful base). Focused 11-id slice post-fix: 11/11 PASS including
  all relatives (slice-expr-eval-order, slice-eval-order,
  pointer-array-full-slice, full-slice, three-index-slice,
  array-to-slice-conditional).

## Item 2 — BUG-067 (census H-d): wire func types drop the variadic bit

- Guardrails written first. gc: mismatchVariadicAtSlice 1,
  mismatchSliceAtVariadic 1, matchRightTypes 31.
- Pre-fix machine: 11 / 11 (both mismatch directions red, the
  identity collapse answering `true` for every assert), control PASS.
- INCIDENT, recorded: the first draft added a "method-set direction
  control" at `interfaces/method-set-variadic-mismatch` — a directory
  that ALREADY EXISTED with finding 0's own 5-row family, which the
  Write clobbered; the first full pre-fix run therefore ran the
  1-subject impostor and skipped the 5 real ids (the baseline-diff
  did not flag them — absent-from-results is "not run/skipped" by
  design, `--full` is the completeness mode). Restored from git,
  duplicate dropped (the existing family IS the method-set control,
  green on the restored re-run), full pre-fix run REDONE, and
  `--full` used for the re-pin diff.
- Fix: `variadic` on the wire func TYPE node (emitType Signature arm),
  REQUIRED at decode (§9.5 discipline), carried on `Ty.funcType` into
  type identity (`Ty.eqbFuel` compares it), and rendered in panic
  messages (`goTypeNameForMessageFuel`: the last parameter prints
  `...E` — gc's failed-assert message names the variadic signature).
- BLAST-RADIUS SWEEP (run BEFORE the confirming run, as charged): all
  1119 emittable corpus dirs swept with the new emitter; exactly FOUR
  contain a func TYPE node with `variadic:true` —
  `interfaces/assert-func-variadic` (the new guardrails, the intended
  flips) plus `variadic/variadic-function-value`,
  `variadic/variadic-method-expression`,
  `variadic/variadic-method-value-copy`. The three pre-existing rows
  store/call variadic func VALUES through func-typed slots: no
  type-assert, no func-type equality, and normalization's funcType
  arms are param-wildcards, so nothing consumes the new bit there.
  11 dirs refuse at the frontend (pre-existing coverage gaps,
  unchanged). PREDICTED FLIPS: exactly the two new reds FAIL→PASS,
  zero other movement.
- UNPREDICTED MOVEMENT, investigated and explained (the honest miss in
  the sweep's frame): `imported-goose/channel/google-search` went
  PASS/membership → FAIL/membership on the first confirming run — NOT
  a behavior flip but the tier=slow certified record's fail-loud
  staleness alarm: the wire sha moved because every func TYPE node now
  carries `variadic` (schema widening; the record's own 2026-08-10
  methodSets precedent is the exact class). GOLEAN_SLOW=1
  re-enumeration reproduced the set AND graph bit-for-bit (six
  members, nodes=6193933 edges=6565663 dedupHits=371731,
  certified=checkCert); record updated deliberately with the new sha
  and the reason, row green again. Lesson recorded: a wire-schema
  widening's blast radius includes every wire-sha-keyed cache, not
  just behavior.
- Also missed by the first grep sweep: `Tests/GoCoreEval.lean:1640`'s
  `.funcType [] []` term (eval-tests build failed loud; fixed with the
  explicit `false`, 141/141 ok).
- Proof-layer fallout of the Ty field, all mechanical: pattern arity
  at ~30 sites (Ops/Mirror/Frame/StateWf/MachineSound/DriftOps),
  `false` added to the 9 pinned-term constructions (Muxer/Defer —
  matches what the fresh decode now produces), one new conjunct
  alternative in `StateEqb`'s `Ty.eqbFuel` soundness `first` block,
  and `ih` added to TypeCongr's funcType nil-results branch (the
  variadic render's new fully-applied recursive call).

## Item 3 — census H-b: `intKindOfOptType`'s silent `.int` coerce arm

- Latent: the census's reachability reading (J-1) says `emit.go:3727`
  (range-over-`*[N]T` index-only collection) is the one emitter site
  shipping a TYPELESS int node; `emit.go:6439` attaches `type` for
  every basic-integer-typed constant (untyped int included; untyped
  rune would already fail closed in `emitBasic`).
- Fix: attach `type` at 3727 (emitter) and make the decoder's int arm
  fail closed on a missing or non-integer `type` — the exact hardening
  its two siblings (incdec `:572-576`, range-over-int `:910-918`)
  already got for BUG-042/043's class; `intKindOfOptType` deleted
  outright (its only consumer was the int arm — J-7's warning about
  re-armable defaults sitting next to hardened code applies one level
  up). Predicted flips: ZERO; static sweep backs the prediction: no
  handwritten wire fixtures with int nodes exist anywhere
  (Tests/tools/Corpus/proofs/scripts/compat grep), the frontend is the
  only producer, and 3727 was its only typeless site. Range family
  post-fix: 27 PASS / 12 FAIL, every FAIL a pre-existing
  frontend-export gap. Census J-1/J-24/§10-H-b updated to "hardened";
  no BUG entry (nothing observable was ever wrong — closed as latent).

## Item 4 — the two doc drifts

- `docs/2026-08-18_multipackage-identity.md` §6: "shims are
  main-package-only" → per-unit (G-35, `load.go:206-218`, raft W4.0).
  Fixed with the supersession dated in place.
- fmt `%X` doctrine/code split (G-11): RECONCILED BY GC PROBE
  (go1.26.5): `%X` over an Error-implementing named uint64 prints
  `4F4F5053` — the UPPERCASE hex of the method result — so gc DOES
  consult error/Stringer for `X` (the doctrine header was right about
  gc). The code is safe purely because `parseFmtFormat` refuses `%X`
  (verb-set default arm) — no wrong answer, a two-site invariant.
  Reconciliation = the invariant NAMED at both sites (the header's
  "%X AND THE TWO-SITE INVARIANT" block; a comment on the stringable
  switch's case list), each naming the other and the render-helper
  third leg; admitting `%X` stays a matrix widening owing differential
  pins. Census G-11 residual + §10 drift paragraph updated (those
  census paragraphs landed with the BUG-066 commit, which swept the
  census file — cross-noted here for the record).
- Judgment call: no code change for `%X` — implementing it would be a
  modeled-matrix widening (needs its own guardrails), out of this
  arc's charter; the drift item asked for reconciliation, which the
  probe settles on the doctrine's side with the code fail-closed.

## Item 5 — setup-deps populates proofs/.lake/packages

- The gap has bitten five lanes (each needed a manual
  `cp -a proofs/.lake/packages` beside `scripts/setup-deps`): this
  arc's own bootstrap (the charter's cp landed as `proofs/.lake`
  itself and needed restructuring — exactly the manual-step fragility
  the item names), and the worktree-per-lane cohort before it.
- Test: a scratch worktree bootstraps to a green fast gate with no
  manual cp.
