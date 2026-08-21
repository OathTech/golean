# Holes arc log — the census's confirmed silent-wrong-answer holes

## AUDIT FIX ROUND (2026-08-21, after the pre-merge audit of `4490bc24`)

The audit ran on the branch's final state and returned four findings
plus three `scripts/setup-deps` defects and a set of doc drifts. All are
fixed on the branch; the exit state below is otherwise unchanged and
still stands. What moved:

- **F1 (MEDIUM) — the fix WIDENED a refusal, and nothing said so.**
  Removing BUG-066's second base emission removed an ACCIDENT: for a nil
  pointer-to-array with an elided high, `(*ap)[:]` and `(*ap)[1:]` used
  to answer gc's recovered panic *because the re-emitted operand
  dereferenced the nil pointer*. With one evaluation and a static
  default high they converge on B-33's documented `emitAddressOf`
  StarExpr-collapse hole — an honest STUCK, the same message and class
  as the already-red explicit-high sibling. Measured through one
  decoder (emitter `6146b217` vs `90b12339`): those two ok/100 → stuck;
  `ap[:]` and the `*[0]int` form were ALREADY stuck. Landed: a corpus
  row per variant class (`pointers/nil-array-ptr-slice-elided-high/*` —
  4 reds at `lean-observation` + 2 greens proving the refusal is the
  slice-base arm and not the field-selector path), the untriaged-ids row
  extended with the four ids at `coverage` (ceiling 7 → 11), BUG-066's
  widening paragraph, and the census B-18/B-33 cross-refs.
  **Fail-closed in both directions — never a wrong answer.**
- **F2 (LOW) — four newly-fixed classes were unpinned.** Now green rows
  with gc-derived expectations: `f()[1:][1:]` (the nested case, the
  sharpest: the inner slice expression is the outer's base, so the call
  ran **four** times pre-fix — gc 133, machine 433), a map-index base
  with an effectful key (122/222), `pf()[1:]` on the pointer-reuse path
  (128/228), and a conversion base `[]byte(f())[1:]` (131/231).
- **F3 (LOW-MEDIUM) — BUG-067's panic direction was unpinned.** The
  comma-ok witness loses a boolean; the single-result form loses the
  CONTROL PATH: pre-fix `_ = i.(func([]int) int)` on a boxed variadic
  func returned normally at status `ok` where gc panics. The new row is
  green post-fix and pins the `...E` render byte-exact against gc's
  message, so dropping the bit from the MESSAGE (not just from
  identity) is red too.
- **F4 (LOW-MEDIUM) — the google-search record's width note was wrong.**
  It called the `width=` move from 16 to 4 "a report-shape difference
  only". It was not: the PREVIOUS record declared `params: width=4` and
  echoed `width=16`, so its enum-stats line was not produced by a run at
  its own declared params (all seven pre-arc versions declare 4; only
  the two POR ones echo 16). This arc's re-certification RESOLVED the
  inconsistency — declares 4, echoes 4, reproduces set and graph
  bit-for-bit, re-verified here. The open question (what the old record
  was certified under) is unrecoverable from the file and is recorded in
  the record as moot-but-noted.
- **`scripts/setup-deps`, three defects**, all fixed with the five
  scratch-root probes re-run: (1) `--only` now scopes the Lake section
  (pseudo-names `lake` / `lake:<pkg>`), so the documented replicate
  command at `docs/spec-sources.md` works again; (2) the
  `--from <deps dir>` spelling now resolves the repo root too, so the
  Lake section uses the offline sibling instead of silently reaching the
  network; (3) a POPULATED non-git package directory is REFUSED, never
  `rm -rf`'d. Defect 3's hazard was demonstrated, not argued: the same
  scratch state under the pre-fix script deleted a hand-populated
  `proofs/.lake/packages/iris` — which is precisely the state the five
  lanes' manual `cp -a` leaves behind, i.e. this script would have eaten
  the very workaround it was written to retire.
- **Doc drifts fixed**: census §10's status prose put in FIXED tense
  (the paragraph still read as if H-a/H-d were live) and §11's Tier-0
  queue (H-b has landed; H-c is what remains); census B-18 and B-33
  anchors re-shifted to the post-fix file; this log's item-3 sweep
  sentence corrected (below — it was false); BUG-067's `tyEq` →
  `Ty.eqbFuel`; `docs/2026-08-18_multipackage-identity.md` §6's
  `newSourcePkg` → `parseLocal` (`load.go:187`, the shim call at `:212`;
  `newSourcePkg` does not exist — `sourcePkg` is the returned TYPE); the
  baseline header now states its sort collation and why `6146b217`'s
  diff moved ~90 unchanged lines.

**Landing gate for the round: full `scripts/ci --diff` at the tip
(`82df0451`) — RESULT: PASS.** Verbatim from the run: `eval tests (141
ok)`, `differential run completed (exit 1; failing-set judged by
baseline diff)`, `negative baseline diff (no regression)`, **`baseline
diff FULL (2343/2343, no regression)`**; goldens, imported-goose R2
pins, verbatim guard, statement-TCB closure, import-direction, core
build, proofs + Audit gate all ok; the two report-only notes
(proof-cost trend 0 modules over +25%, storm lint) unchanged. Predicted
drift was the eleven new ids and nothing else — confirmed at re-pin
time by the run's own drift report, every line reading "NEW id (not in
baseline)". (Recorded by amending the docs commit that carries this
line; the tree the gate ran on differs from the committed tree in this
paragraph only.)

**Bootstrap test for the setup-deps changes, re-run end to end:** a
fresh detached worktree at this tip, `scripts/setup-deps --from
/home/dev/projects/golean` with no other flags — five deps (goose
`3be88bb`, perennial `43d4efa`, raft `56e3200`, iris-lean `3877dbe`, go
`c19862e5f8`) and three Lake packages (iris `3877dbe`, batteries
`fa08db58`, Qq `f463249`) all cloned OFFLINE, `setup-deps: complete` —
then `GOLEAN_ALLOW_NO_DIFF=1 scripts/ci`: **PASS**, including the proofs
+ Audit gate, with NO manual `cp` anywhere and the two visible
`NOT RUN (no record; explicitly allowed here)` notes the hatch owes.
Scratch worktree pruned after.

## EXIT STATE (2026-08-21)

All five charter items DONE; branch-complete, awaiting the audit ask.
(The audit was then run and its findings fixed — see the section above;
the merge sign-off is still the user's and still outstanding.)

- Item 1 · BUG-066 (H-a, elided-high slice base double-eval): FIXED.
  Guardrails wave (both bugs' rows witnessed red) `6146b217`, fix
  `90b12339`. Landing gate: full `scripts/ci --diff` at `90b12339` —
  RESULT: PASS, `baseline diff FULL (2332/2332, no regression)`.
- Item 2 · BUG-067 (H-d, variadic bit dropped from wire func types):
  FIXED. Commit `1c918155`. Landing gate: full `scripts/ci --slow`
  (tier=slow record + Ty touched) — RESULT: PASS; google-search
  re-certified (set/graph bit-for-bit, new wire sha).
- Item 3 · H-b (decoder's silent `.int` coerce arm): HARDENED as
  latent, commit `3b38dcd5`, zero flips predicted and confirmed.
- Item 4 · doc drifts: FIXED, commit `b6fa4b03` (multipackage §6
  per-unit; %X reconciled by gc probe, invariant named at both sites).
- Item 5 · setup-deps Lake-packages population: LANDED, commit
  `2b1c30a8`, scratch-worktree test to a green fast gate, no manual cp.
- Items 3–5 landing gate: full `scripts/ci --diff` at the branch tip
  (`2b1c30a8` + this closing docs commit's log/census status updates in
  the tree) — RESULT: PASS, `baseline diff FULL (2332/2332, no
  regression)`, eval tests 141 ok, goldens/pins/negative all ok.

NOT in scope, unchanged and honest in the census: H-c (W7 tier-0
design), H-e (probed non-divergence, latitude-census gap), H-f
(observability open).

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
  up). Predicted flips: ZERO. **CORRECTION (audit fix round
  2026-08-21):** the sentence that stood here — "no handwritten wire
  fixtures with int nodes exist anywhere" — was FALSE, and the sweep
  behind it was reported wrong. One handwritten fixture exists,
  `compat/gobra/testdata/sum/wire.json`, and it carries **6 int-kind
  nodes** (and 0 func-kind TYPE nodes, the BUG-067 sweep's question).
  The CONCLUSION survives, and for a better reason than the false one:
  all 6 already carry `type`, so the hardened int arm accepts them
  unchanged — the prediction was right, the evidence for it was not.
  What the corrected sweep says: the frontend is the only wire producer
  at scale, `3727` was its only typeless int site, and the single
  handwritten fixture is typed throughout. Range family
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

- The gap has bitten five lanes, each paying a manual
  `cp -a proofs/.lake/packages` (or a red first gate) beside
  `scripts/setup-deps`: gallery g1 (`docs/gallery-campaign-log/
  g1.md:861` — named it an INFRA gap explicitly), gallery g4
  (`g4.md:578`), w32 (`docs/w32-log.md:47`, which also records
  channel-logic and raft-w4 carrying the same pattern), raft-w41
  (`docs/raft-w41-log.md:115` — 4 unrelated gate FAILs traced to the
  missing packages), and this arc's own bootstrap (the charter's cp
  landed as `proofs/.lake` itself and needed restructuring — exactly
  the manual-step fragility the item names).
- Implementation: a Lake-packages section in `scripts/setup-deps`,
  same posture as the deps/ table — pins read from
  `proofs/lake-manifest.json` (git-type entries only; the path-type
  GoLean entry skipped), offline clone from `--from`'s sibling
  `proofs/.lake/packages/<name>` first, manifest URL fallback,
  rev-drift reported and never touched, every failure loud.
- TEST, run before this commit: scratch worktree
  `.claude/worktrees/holes-scratch` detached at `1c918155` + the new
  script; `setup-deps --from /home/dev/projects/golean` cloned and
  pinned lake:iris @ 3877dbe, lake:batteries @ fa08db58,
  lake:Qq @ f463249 (plus the deps/ set); then
  `GOLEAN_ALLOW_NO_DIFF=1 scripts/ci` (fast gate, docs-only-lane
  hatch with its visible notes) — RESULT: PASS, including the
  proofs + Audit gate, with NO manual cp anywhere. Scratch worktree
  pruned after the test.
