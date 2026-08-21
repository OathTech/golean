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
  type identity. Blast radius sweep before the confirming run: every
  wire func type node changes (gains the key), so the corpus wire
  sweep + golden repr diff is the prediction instrument; predicted
  behavioral flips are ONLY rows asserting/comparing at func types
  where variadic-ness differs — i.e. the two new reds.

## Item 3 — census H-b: `intKindOfOptType`'s silent `.int` coerce arm

- Latent: the census's reachability reading (J-1) says `emit.go:3727`
  (range-over-`*[N]T` index-only collection) is the one emitter site
  shipping a TYPELESS int node; `emit.go:6439` attaches `type` for
  every basic-integer-typed constant (untyped int included; untyped
  rune would already fail closed in `emitBasic`).
- Fix: attach `type` at 3727 (emitter) and make the decoder's int arm
  fail closed on a missing or non-integer `type` — the exact hardening
  its two siblings (incdec `:572-576`, range-over-int `:910-918`)
  already got for BUG-042/043's class. Predicted flips: ZERO; the full
  run is the confirmation, and the census J-1/H-b rows get updated to
  "hardened" in the same commit.

## Item 4 — the two doc drifts

- `docs/2026-08-18_multipackage-identity.md` §6: "shims are
  main-package-only" → per-unit (G-35, `load.go:206-218`, raft W4.0).
- fmt `%X` doctrine/code split (G-11): header at `fmtdesugar.go:35`
  claims Stringer/error consult for `x, X, q, s, v`; the verb switch
  at `:516` handles `s, v, x, q` — no `X`. Reconcile by gc probe.

## Item 5 — setup-deps populates proofs/.lake/packages

- The gap has bitten five lanes (each needed a manual
  `cp -a proofs/.lake/packages` beside `scripts/setup-deps`): this
  arc's own bootstrap (the charter's cp landed as `proofs/.lake`
  itself and needed restructuring — exactly the manual-step fragility
  the item names), and the worktree-per-lane cohort before it.
- Test: a scratch worktree bootstraps to a green fast gate with no
  manual cp.
