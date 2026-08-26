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

## SM1 slice 3 — the viol/S1-record spans: `s1_span_computes`
(items 3a+3b; DELIVERED — the S1 checker bridge is now REAL ABOUT THE
BYTES at symbolic checker state)

Files: `Specs/Raft/SpanCells.lean` (the cell machinery + `viol`),
`Specs/Raft/SpanS1.lean` (vocabulary, pins, projection bridge),
`Specs/Raft/SpanS1Walk.lean` (the walk; split so the kernel pins
compile once — an 11-min full-file elaboration became a 3-min
iteration), `Specs/Raft/SpanS1Witness.lean`, `Audit/Span.lean`.

### 3a — `SpanCells`
- **`twinFs`** — the twin struct at the pinned declaration's field
  order (probe `twintypes.out`), symbolic in every payload;
  **measured off the machine's own definition**: `normalizeValueForTy`
  is the IDENTITY at slice/map/string/bool field types (no arm
  matches; the catch-all returns the value), so the whole-struct
  re-normalization every `declaredTy = main.twin` field store routes
  through only touches the four int fields. `twinDecl_pinned`
  (kernel, axiom-FREE) pins the declaration.
- `normalize_twinFs` (the normalization identity at in-range
  counters; `kernel_rfl` raw + `inorm` discharge), the three
  field-store singles (claims/violations/trace) through the
  `fieldAddr` chain, `read_field_seg` (the 5-step
  `p.f`-through-pointer read — the arc's workhorse single).
- **`viol_pinned`** (whole-`Func`, axiom-free) + **`viol_call_span`**
  (42 steps, probe-verified `violprobe.out`): `violations`
  incremented EXACTLY, `trace` appended, targetless-frame exit
  (`.next k` directly — the machine's `[] [] []` frame arm).

### 3b — `SpanS1` + the walk
- **`s1Block_pinned`**: the WHOLE S1 record span (claims++, comma-ok
  lookup, the fire branch with its three `utoa` calls + `viol` call
  + the five string concats byte-for-byte, the overwrite-insert)
  occurs verbatim among `main.twin.harvest`'s sub-statements —
  statement-granular, strictly stronger than U23's per-guard pins.
- **The projection bridge**: `projLOf` (MapMem's `List (Int × Nat)`
  model → the U23 model's assoc list); `lookupTerm_projLOf`
  (first-match agreement — NO key-distinctness needed: both sides
  are first-match), `lookupTerm_projLOf_setk` (machine
  overwrite-insert ≈ model cons, lookup-extensionally),
  `s1Fires_projLOf` (the machine's `ok && prev != id` value IS
  `s1Fires` at the projection), `LookupEq` + `s1Step`/fold
  congruences (counters EXACT through folds — the bridge's
  `0 < viols` predicate transfers on the nose), `s1_abs_step`.
- **`s1_span_computes`** (5200-step bound, three branches:
  short-circuit skip / same-claimant / FIRE): from ANY symbolic
  checker state (t/nd pointers, twin struct, node struct, map cell,
  freshness, `Agrees`, ranges, five disjointness facts), the span
  ends `.next K` with claims `= cN+1`, violations
  `= wN + (if s1Fires ⟨projLOf kvs,…⟩ (tm,idv) then 1 else 0)` —
  THE MODEL PREDICATE LITERALLY IN THE MACHINE READOUT — the map
  cell at `toEntries (setk kvs tm idv)`, trace ∃, frame respect,
  frontier/freshness/`Agrees` threaded. The fire branch runs the
  three `utoa` call spans + the concat + the `viol` span
  compositionally (the frame clauses carry every checker cell across
  the calls).
- **Witnesses (same slice)**: `s1w_span_fire` (the U23 bridge
  witness's event — `(5,2)` after `(5,1)` — through the SPAN;
  `s1w_span_fire_fires : s1Fires … = true` axiom-free) +
  `s1w_span_clean`, every premise discharged on a concrete five-cell
  state. Compiled cross-checks (`s1block.out`): clean = **74 steps**,
  = the composed 47+4+3+20 EXACTLY; fire = 646 (one-digit args),
  under the bound.
- **Audit/Span.lean**: 22 pins, readouts verbatim from `axspan.out`
  (all within [propext, Classical.choice, Quot.sound]; the three
  byte pins + the fire-readout axiom-FREE), `#guard_msgs` verified
  in place (`lake env lean` exit 0). Hatch grep over all 7 new
  modules: **0**.

- [AGENT] calls, tagged:
  1. The map bridge rides `MapMem` (Group-2/5 public API:
     `idxOf?/cnt/setk/toEntries`, `mapEntryIndex?_toEntries`,
     `mapAssignValue_toEntries`) — the leaderOf map is
     `map[uint64]uint64`, exactly MapMem's fragment. One new
     machine-op lemma (`applyRhsOp_mapLookup_toEntries`, the comma-ok
     read) + one new step single (`stepFn_rhs_apply`) were the whole
     gap; the anti-grinding survey before building saved a
     re-derivation of the entire map theory.
  2. The struct-store cost was resolved by MEASURING the
     normalization function first (the identity-at-untyped-arms
     observation) instead of fighting a general struct-normalization
     theory — the twinFs shape encodes exactly what the machine
     checks.
  3. `s1_span_computes`' conclusions are the WEAK FORM as banked:
     counters exact, map by `setk` + lookup-equality transport, trace
     existential, and an abstract frontier (`+2 ≤`, not exact — the
     fire branch's allocation count depends on the arguments' digit
     counts, which the consumer never needs).
  4. The file split (pins vs walk) is an ITERATION-SPEED move, not
     architecture; recorded in both docstrings.

Verification: every module `lake env lean` exit 0, zero warnings;
oleans via explicit targets (≤48G, lock-exempt); `#eval`-first via
the probes (`s1block.out` config chains transcribed
segment-for-segment before proving).

## SM1 slice 4 — the pb-getter call spans (item 4's banked piece;
DELIVERED) + THE APPLY-WALK BOUNDARY-STOP (measured)

`Specs/Raft/SpanApplyGetters.lean`:

- **Four whole-`Func` pins, axiom-FREE** (`getIndex/getTerm/getType/
  getData_pinned` + `entryTypeDecl_pinned`): the getters' verbatim
  lowered bodies (`getterdump.out`) — nil-checked pointer-field reads
  (`Index`/`Term`/`Type` are `*uint64`/`*EntryType` protobuf-optional
  fields; `Data` a direct `[]byte`).
- **`ptrGetter_body_span`** — ONE generic 43-step body walk over
  (field, payload type, result type, store-normalization fact),
  serving Index/Term/Type; **`getData_body_span`** (29 steps, single
  nil check, no second deref). New singles:
  `applyStrictOp_neq_addr_nil` (pointer-type `!=` against nil, any
  address, any state), `normalize_slice` (slice normalization is the
  identity — no arm matches, measured off the definition),
  `normalize_entryType` (the alias resolves to `int32` at the pinned
  table).
- **Four call spans** (`getIndex/getTerm/getType/getData_call_span`;
  49/49/49/35 steps, all EXACT, probe-verified `getterprobe.out`
  51-step end-to-end at a concrete state = 49 + the probe's 2
  continuation steps): from the delivered receiver to the caller's
  resumption, the target cell holding EXACTLY the entry's field
  value, explicit `twinSt` final states, dead frame cells between
  the frontiers.
- Audit/Span extended to **30 pins** (8 getter rows; readouts
  verbatim from `axgetters.out`), all `#guard_msgs` verified in
  place. Warnings zero; hatch grep over the module: 0.

### THE BOUNDARY-STOP (the chartered clause, fired at the measurement)

The FULL `apply` walk (`s23_span_computes` — S23's interpreter half)
was measured against the bank before building, off the verbatim body
(`harvestdump.out`, 560 dump lines vs `s1Block`'s 170):

- The banked price ("+0.7–1: the 4 pb-getter call spans × the same
  idiom + 12 branch combinations") covers the getters (delivered
  above) and the branch combinatorics — but the walk needs TWO map
  fragments the bank did NOT price and `MapMem` does not cover:
  1. `nd.got` — a `map[string]bool` write (`got[data] = true`):
     string-keyed; `MapMem`'s whole model (`idxOf?/cnt/setk/
     toEntries` + every operation lemma) is `Int`-keyed uint64 — a
     parallel model + `mapEntryIndex?` scan lemmas at string
     `valueEq` is a fresh MapMem-scale build.
  2. `t.byIndex` — a `map[uint64]main.slot` comma-ok lookup + insert:
     STRUCT-VALUED, so `mapAssignValue` normalizes the slot value at
     the DEFINED type (the U23 table-footprint class) and the model
     needs a slot-struct encoding + its normalization identity —
     a second fresh fragment.
  Plus: the anomaly and empty-data branches EARLY-RETURN through the
  frame (`.returning` mid-span), so the span theorem needs
  per-branch-class conclusion shapes (unlike `s1Block`'s single
  `.next K` exit), × the S3-idx × S3-term × type × data × byIndex
  branch product.
- Measured against the S1 span (the like-for-like anchor: `s1Block`
  with ONE `MapMem`-covered map and one exit shape consumed the
  `+0.5`-unit slot), the apply walk with two fresh map models and
  the exit-shape split prices at ≥ 2× its banked "+0.7–1" residue
  after the getters. **That is the chartered stop condition**;
  stopping AT the measurement, with the route mapped:
  1. a string-keyed `MapMem` sibling (promotable — `wordfreq`-class
     examples are latent second consumers);
  2. a `slotFs` cell vocabulary + `normalize_slotFs` (the `twinFs`
     pattern verbatim, 3 fields);
  3. the walk itself is `SpanS1Walk`'s pattern with per-branch-class
     endpoints — no new machine machinery beyond 1–2.
  Everything below the two map models is already on the shelf: the
  getters (this slice), `utoa_call_span`, `viol_call_span`,
  `storeTarget_twin_*` (committed++ reuses the claims-store single's
  pattern at the `committed` field), `read_field_seg`,
  `stringFromByteSlice` being the one further single.

- [AGENT] The stop is taken at the measurement, not after sinking
  the budget (the U24 discipline verbatim): items 1–3 + the banked
  getter piece stand delivered and witnessed; the S23 byte-closure's
  remaining distance is exactly the two map fragments + the
  branch-shape split, priced above for the successor.

## SM1 layering fix (gate finding, fixed on the branch)

The first gate run (`artifacts/ci-arc4d-sm1.log`, GATE_EXIT=1) found
TWO reds: the anticipated un-swept-files red AND a REAL layering
finding — `import-direction violated`: `Sym/UtoaSpan.lean` (general
layer) imported target-layer Specs modules (`Specs.TwinProgram`,
`Specs.Raft.HandlerEqSym`). The charter's location list allowed
`Sym/Utoa*`, but the repo's import-direction lint (the TCB/layering
doctrine's mechanization) is right: the utoa span PINS THE TWIN'S
BYTES — target-specific, Specs-layer content. Fixed by `git mv` to
`Specs/Raft/UtoaSpan.lean` (namespace unchanged;
the only importers are this arc's own new files — no existing file
touched). `Sym/UtoaForKit.lean` STAYS in Sym/: it imports only kit
modules and passes the lint — the schema is genuinely general.
[AGENT] The lint finding was taken as correct over the charter's
location hint; gates are speedbumps, and this one caught a real
layering drift before landing.

## SM1 unit-end gate record (2026-08-26)

`GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=96G scripts/ci` under the
box-wide build lock (`artifacts/lockgate.sh`), second run after the
layering fix: `artifacts/ci-arc4d-sm1-2.log`, **GATE_EXIT=1 — the
KNOWN NEW-FILES-ONLY RED, exactly as chartered**:

- **21 `ok` steps** (oracle toolchain, escape hatches, bug-index,
  feature-coverage, spec anchors, lane validation, imported-goose
  verbatim + R2 pins, surface purity, statement-TCB closure, core
  build warning-free, **proofs + Audit gate ok**, Challenge/Solution
  elaborate, verdi compat, frontend unit tests, eval tests 141 ok,
  …) + the two sanctioned no-diff notes (docs/proofs-only arc, hatch
  set explicitly, notes printed).
- **The ONE red, verbatim**: `FAIL proofs-file audit coverage
  (un-swept proof file — import it from Audit.lean or
  AuditCorpus.lean, or allowlist with a reason)`, listing exactly
  this arc's 8 new files (UtoaForKit, UtoaSpan, SpanCells, SpanS1,
  SpanS1Walk, SpanS1Witness, SpanApplyGetters, Audit/Span) — the
  NEW-FILES-ONLY consequence: the aggregators are untouched by
  charter, so the sweep cannot see the new modules until the
  operator adds the imports at landing.
- **Compensating checks (all run, exit codes captured)**: every new
  module `lake env lean` exit 0, zero warnings; every module built
  to olean via explicit `lake build +<module>` (56/57 jobs, exit 0);
  `Audit/Span.lean` — 30 `#guard_msgs` axiom pins — verified IN
  PLACE (`lake env lean` exit 0, empty output), axiom readouts
  verbatim from `axspan.out`/`axgetters.out`, all within
  [propext, Classical.choice, Quot.sound], the seven byte-pins
  axiom-free; hatch grep (`sorry|native_decide|hatch`) over all 8
  new files: **0**.
- Standing report-only notes, unchanged and re-escalated for the
  operator: comparator landmark STALE (174 commits) + OWED (scope,
  2 Challenge-closure files) — standing since U8; NOT this arc's
  surface (no designated statement touched).

## LANDING MANIFEST (the operator's one-commit import additions)

At landing (after merge-protocol steps), add exactly these lines:

1. `proofs/Audit.lean`: `import Audit.Span`
2. `proofs/GoLeanProofs.lean` (the aggregator, alphabetical spot):
   `import GoLeanProofs.Specs.Raft.SpanApplyGetters` and
   `import GoLeanProofs.Specs.Raft.SpanS1Witness`
   (their closures pull UtoaForKit, UtoaSpan, SpanCells, SpanS1,
   SpanS1Walk — nothing else is needed).

Then `scripts/ci` goes green with no other change (the un-swept red
is exactly these 8 files; all 30 pins already verify in-build via
Audit.Span).

## SM1 EXIT (branch-complete; nothing merged)

**CHECKPOINT (recomputed):** worker commits on `campaign-arc4d` since
base eee6b43b: e215c670 (slices 1–2), deb6f8c9 (slice 3), + the
slice-4/move/gate-record commit (this one). New tracked files: 8
modules + this log. Cost vs the banked 1.5–2 units: items 1–3 + the
banked item-4 piece delivered in ONE session ≈ 1 unit of work at the
banked rates (the utoa kit came in UNDER the 0.5-unit bank — the
CondFor schema + weak form landed without the feared act_inc
grinding); the apply-walk REMAINDER is boundary-stopped at the
measurement with the two unbanked map fragments priced.

**Deliverable state vs the SM1 charter:**
1. The plain-for head schema — **DELIVERED** (`CondFor`, witnessed).
2. The utoa weak span — **DELIVERED** (∃-string as banked; pin,
   loop/body/call spans).
3. The viol/S1-record spans — **DELIVERED**: `s1_span_computes` +
   `s1_abs_step` + the `LookupEq` fold congruences close the U23
   bridge's S1 half TO THE BYTES at symbolic checker state (the I4
   interpreter half for S1); fire/clean witnesses at the bridge's
   own event.
4. The apply spans — **the banked getter piece DELIVERED** (4
   pins + 4 exact call spans); the full `s23_span_computes` walk
   **BOUNDARY-STOPPED at the measurement** (two unbanked
   map-fragment models + per-branch exit shapes ≥ 2× the banked
   residue; route mapped above for the successor).

**Which bridges are byte-closed:** S1 — YES (span-computes-model
proved end-to-end; the remaining S1 distance to T1 is the
`ClaimTrace` run-correspondence seam, which was ALWAYS the assembly's
by design). S23 — NOT YET (getters + all shared machinery on the
shelf; the two map fragments + branch shapes are the exact residue,
priced).

**PROPOSED NEXT CHARTER (successor):** (1) `s23_span_computes` from
the banked route: the string-keyed MapMem sibling (promotable;
wordfreq-class latent consumers), the `slotFs` vocabulary +
`normalize_slotFs` (twinFs pattern, 3 fields), then the apply walk
in the `SpanS1Walk` pattern with per-branch-class endpoints
(`.next K` / `.returning` early exits); ≈ 1–1.5 units by the
measured S1 rate. (2) The harvest-loop prep-parameterized `CondFor`
generalization only if the T1 assembly demands the Ready-loop span
(recorded latent consumer). (3) Operator items: the landing manifest
above; the standing comparator STALE+OWED escalation.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).

# ── SM2 (fresh worker, 2026-08-26): `s23_span_computes` from the banked route ──

## SM2 successor re-verification (2026-08-26)

- Tip clean at 365f4502 (SM1's exit commit), branch `campaign-arc4d`. PASS.
- SM1's modules re-built green as explicit targets from this worktree's
  cache: `lake build +GoLeanProofs.Specs.Raft.SpanS1Witness
  +GoLeanProofs.Specs.Raft.SpanApplyGetters +Audit.Span` — "Build
  completed successfully (57 jobs)", exit 0. The one warning stream in
  the transitive build is `GoLeanProofs/SliceMem.lean` (a PRE-EXISTING
  tracked file, replayed — not SM1's); SM1's zero-warnings claim was
  about its new modules and stands. PASS.
- `Audit/Span.lean`: 30 `#guard_msgs` pins counted in place. PASS.
- Hatch grep (`sorry|native_decide|hatch`) over SM1's 8 modules: 0. PASS.
- SM1's gate record re-read (`artifacts/ci-arc4d-sm1-2.log` tail:
  RESULT: FAIL / GATE_EXIT=1 — the known new-files-only red, as
  recorded). PASS.

## SM2 probes (`#eval`-first; all gitignored `artifacts/probe/`)

`ApplyProbe.lean` → `applyprobe.out`: type-decl dumps (`main.slot` =
term u64/data string/node u64; `raft.StateType` = defined uint64;
`raftpb.EntryType` = defined int32), normalization probes (slot + node
struct normalization = IDENTITY at in-range payloads; `defaultValue`
main.slot = the zero slot; `buildStructValue` = the named fields;
string keys hashable), and WHOLE-CALL walks of `main.twin.apply` at
concrete states for all seven branch classes — every class runs to
`.next .stop` with the s23Step-predicted readout:
- A clean-insert 428 steps (committed++, cursors set, got+{data},
  byIndex append, viol 0)
- B S2-fire 1339 (viol 1, byIndex UNCHANGED on hit)
- C hit-agree 427 (viol 0, byIndex unchanged)
- D S3-idx-fire 990 / E S3-term-fire 990 (viol 1, cursors still set)
- F anomaly 622 (viol 1, committed/got/byIndex untouched, early return)
- G empty-data 289 (viol 0, cursors set, committed/got/byIndex
  untouched, early return)
Verbose config chains for A/G/F/B/D dumped for segment transcription.

## SM2 slice 1 — `SpanS23Maps.lean` + `SpanS23Cells.lean` (items 1-2:
the two map fragments + the cell/op layer; DELIVERED)

`Specs/Raft/SpanS23Maps.lean`:
- **`encGS`** — the injective GoString→Nat data code (base-257,
  digits 1..256): `encB_inj`/`encGS_inj`, `encGS_eq_zero_iff` (empty ↔
  0 — the machine's `len(data)==0` branch IS the model's `data = 0`),
  `gsBeq_iff_eq` (the derived GoString BEq decides equality),
  `gsBeq_encGS` (machine string `==` IS model code `==` — the S2
  data-comparison transport). [AGENT] The model's `AEv.data : Nat` is
  bridged by a CONCRETE injection rather than an abstract premise: the
  walk theorem then states `s23Step` literally, and the T1 assembly
  renames data through `encGS_inj` (assembly-seam note; recorded here
  because the banked route had left the data-vocabulary mismatch
  unpriced — it cost one design decision, no new theory).
- **The string-keyed MapMem sibling** (`nd.got`'s fragment, MapMem
  reuse pattern — one scan engine + one op lemma): `sIdxOf?`/`setks`/
  `toEntriesS`, `valueEq_string`, `checkKeyHashable_string`,
  `scanS_generic`, `mapEntryIndex?_toEntriesS`,
  `mapAssignValue_toEntriesS` (update-or-append = `setks`; string
  keys/bool values normalize as identities). PROMOTABLE (wordfreq-class
  latent consumers); promotion target `GoLeanProofs/StrMapMem.lean`
  recorded in the module docstring; located here per the lane's
  location rule + §7 one-consumer test.
- **The slot-valued fragment** (`t.byIndex`): `slotFs` +
  `slotDecl_pinned` (kernel) + `normalize_slotFs` +
  `defaultValue_slot` + `buildStructValue_slot` (the twinFs pattern,
  3 fields; table-footprint normalizations conditioned on
  `σ.types = twinTypes`); `bIdxOf?`/`bget?`/`toEntriesB`,
  `scanB_generic`, `mapEntryIndex?_toEntriesB`,
  `applyRhsOp_mapLookup_toEntriesB` (comma-ok: first-match slot or
  the ZERO slot + flag), `mapAssignValue_toEntriesB_insert` (the
  miss-arm append — the only assignment the checker performs; the hit
  arm never assigns, so it is deliberately not built — §7).

`Specs/Raft/SpanS23Cells.lean`:
- **`nodeFs`** (9 fields, `rn`/`st`/`got` opaque) + `nodeDecl_pinned`
  + `stateTypeDecl_pinned` + `entryTypeResolve_pinned` (kernel pins) +
  field lookups + `normalize_nodeFs` (identity at in-range payloads —
  `state` resolves through `raft.StateType` to uint64, measured in
  the probe first).
- **Cursor stores** `storeTarget_node_applied`/`_lastTrm` +
  `storeTarget_twin_committed` (the SpanCells store-single pattern at
  the two new cells).
- **Comparison singles**: `applyStrictOp_eqCmp_int`, `_neqCmp_u64`,
  `_neqCmp_string`, `_neqCmp_entryType` (htypes-conditioned — the
  defined chain resolves through the pinned table),
  `_atMostCmp_int`, `_lessCmp_int'` (kind-blind int payloads),
  `_length_slice`.
- **`applyStrictOp_stringFromByteSlice`** — the byte fold
  (`byteFold_generic`, scan-engine pattern; `UInt8.ofNat_toNat`
  round-trip); the `sliceVisibleValues` fact enters as a HYPOTHESIS —
  [AGENT] the SliceMem append-family precedent, chosen so the span
  stays shape-generic in the Data slice's offset/backing (fixing
  offset 0/cap=len would have been target-shaped over-specialization;
  witnesses discharge the fact by kernel evaluation).

Verification: both modules `lake env lean` exit 0, ZERO warnings
(`SpanS23Maps` carries MapMem's documented `unusedSimpArgs`
suppression for the same `letFun` false-flag, comment carried over).

## SM2 slice 2 — `SpanS23Apply.lean`: the spelled `main.twin.apply`
+ PIN + the projection bridge (DELIVERED)

- **`apply_pinned`** — the WHOLE lowered `main.twin.apply` `Func`
  (every branch a named def: `s3IdxBranch`/`s3TermBranch`/
  `anomalyBranch`/`s2Branch`/`byIdxBlock`, the five viol concat
  chains byte-for-byte) equals
  `findFunctionIn? twinLowered.funcs ⟨"main.twin.apply"⟩` by
  `kernel_rfl` — `utoa_pinned`'s whole-Func pattern at the arc's
  biggest body. **#eval'd FIRST** (`applypin.out`: `Stmt.eqbF` true +
  args/results/id/wrapper equal — the eval-before-decide drill; the
  pin was kernel-checked only after the eval said true; 37 s
  whole-file elaboration).
- **`apply_enterFrame`** — three pointer-argument cells at the
  frontier, targetless frame, `kernel_rfl` at symbolic heap/frontier
  (the frame env `[[e, nd, t]]` shape eval-verified in the probe).
- **The projection bridge**: `projBy` (machine slot list → model
  byIndex rows, `encGS` on data), `KeysWfB`, `lookupIdx_projBy`
  (first-match agreement), `lookupIdx_projBy_append` (machine
  append-if-absent ≈ model cons, lookup-extensionally — the
  `s23Step` byIndex transport), `s2guard_proj` (the machine's
  short-circuit `s.term != trm || s.data != data` Bool IS the
  model's disagreement decision at the projection), `LookupEqB` +
  `s2Hit_congr`/`s23Step_congr`/`s23Fold_congr` (counters and
  cursors EXACT through folds — SpanS1's `LookupEq` pattern at the
  S23 state).

Verification: `lake env lean` exit 0, ZERO warnings; olean via
explicit target.

## SM2 slice 3 — `SpanS23Walk1.lean`: shared units + the getters
prelude (DELIVERED)

- **`sliceVisibleValues_of_array`** — the Data slice's visible bytes
  from first-order premises (the backing-array cell + the pointwise
  window fact): the walk's `string(bytes)` premises never quantify
  over states (the ∀σ-premise smell deliberately avoided); Std.Range
  `forIn` handled via the SliceMem `range'` route with a local
  push-fold engine.
- **`utoaUnit_walk`** — ONE generic `$c := utoa(arg)` unit walk
  (splice/init/call-plan glue + `utoa_call_span`), parameterized by
  the argument-delivery fact at the post-init state. [AGENT] the
  lift-repeated-patterns rule applied UP FRONT: SpanS1Walk paid this
  shape inline three times; the apply walk has THIRTEEN utoa call
  sites across its four violation branches — the unit lemma turns
  each into a ~15-line delivery-fact derivation.
- **Named body views** (`s3IdxIfS`/`s3TermIfS`/`appliedAsn`/
  `lastTrmAsn`/`anomalyIfS`/`lenIfS`/`dataAsn`/`gotAsn`/`commitAsn` +
  `restAfterGetters`, `applyBody_view` rfl-pin) and
  **`s23_getters_seg`** — the deterministic 117-step prelude: frame
  entry (`apply_enterFrame`), `idx`/`trm` delivered by the two pinned
  getter call spans (`getIndex/getTerm_call_span`, 49 each), landing
  on the S3-index guard at the explicit 11-set `gettersSt` state,
  frontier +9. Step count matches the probe chain ([0]→[117] in
  `applyprobe.out` V-A) exactly.

Verification: `lake env lean` exit 0, zero warnings; olean via
explicit target; hatch grep 0.

## SM2 slice 4-6 — THE APPLY WALK + `s23_span_computes` + witnesses
+ pins (items 3-4; DELIVERED — **S23 IS BYTE-CLOSED**)

Files: `SpanS23Walk1-5.lean` (the walk, split for iteration speed —
the SM1 convention, plus one forced split: a single byIdx decl blew
the PER-DECL heartbeat budget, so the hit path became its own
theorem), `SpanS23.lean` (abs step + headline),
`SpanS23Witness.lean`, `Audit/SpanS23.lean`.

### The walk (SpanS23Walk1-5)
- **Walk1**: `sliceVisibleValues_of_array` (first-order Data-window
  premises — no ∀σ premise), **`utoaUnit_walk`** (ONE generic
  `$c := utoa(arg)` unit for the THIRTEEN call sites; ka + 1572
  bound each), the named body views + `s23_getters_seg` (117 exact,
  probe-verified, the `gettersSt` 11-set state).
- **Walk2**: `BrCells` (the branch cell pack + `thread`/`threadF`
  transports), `concat6_eval` (21), **`s3Branch_walk`** — ONE engine
  for BOTH S3 fire branches (3 units + concat + `viol_call_span`,
  `∃ ≤ k1+k2+k3+4800`), and the two guard segments
  (`s3idx_seg`/`s3term_seg`) with **the guard readout EXACT**:
  `violations + (if ixN ≤ apl then 1 else 0)` — the model predicate
  literally in the machine readout, the fire branch's trace
  existential.
- **Walk3**: `s23_cursors_seg` (22; whole-node re-normalizing
  stores), `getterUnit_prelude` + `lookup_declare_self/_ne`,
  `s23_type_seg` (66; the EntryNormal skip), `s23_len_seg` (54,
  fall-through) and **`s23_len_ret` (58, the EMPTY-PAYLOAD EARLY
  RETURN through the targetless frame — the `.returning` cascade)**,
  `s23_tail_seg` (87: `string(bytes)` via the window premises,
  `got[data] = true` = `setks`, `committed++`).
- **Walk4**: `bget?_mem`, the 26-step comma-ok slot lookup (zero
  slot on miss, store normalization by cases on the scan),
  `fieldOnVar_seg`, the miss/insert subcase (30, `.next Kc`), **the
  generic left-spine concat evaluator** (`spineE/nestK/spineSteps/
  spine_desc/spine_consume/spine_eval` — structural induction over a
  leaf-descriptor list; replaces a hand-rolled 14-leaf walk;
  [AGENT]: promotion note — `concat6_eval` is this engine's
  hand-rolled instance, fold it in at the next consolidation slice),
  and **`s2Branch_walk`** (5 `utoaUnit` rides + the 14-leaf spine +
  `viol_call_span`, `S2Cells` threading).
- **Walk5**: `s23_byidx_hit_seg` (own decl: the short-circuit S2
  guard, agree-skip and fire paths exit-unified) +
  **`s23_byidx_seg`** — the block's three subcases with
  `s2HitB`/`bInsertIfAbsent` readouts EXACT.

### The headline (`SpanS23.lean`)
- **`s23_abs_step`** — the data-refinement commutation: the machine
  readouts ARE `s23Step`'s fields at the `projBy`/`encGS`
  projection — byIndex lookup-extensional (machine APPEND vs model
  CONS via `lookupIdx_projBy_append`), cursors/counters EQUAL;
  composable through folds by `s23Fold_congr`.
- **`s23_span_computes`** — from ANY symbolic checker state
  (EntryNormal entry — the model's own scope, per the U23/C4 note,
  RECORDED in the docstring; the anomaly branch stays covered by the
  U23 guard pin + this walk's guard evaluation showing it is NOT
  taken at EntryNormal): the whole `main.twin.apply` CALL
  (`∃ m ≤ 18400`) ends `.next Kc` with
  - cursors `= (ixN, tmN)` EXACT,
  - `violations + (iteS3idx + iteS3trm + (if encGS data = 0 then 0
    else s2HitB))` — `s23Step`'s deltas literally,
  - `committed`/`got`/`byIndex` per the empty-payload branch
    (`encGS = 0 ↔` empty, `encGS_eq_zero_iff`),
  - trace ∃, frame respect, frontier `+9..+130`, freshness,
    `Agrees`.
  Axioms: [propext, Classical.choice, Quot.sound]; `s23_abs_step`
  [propext, Quot.sound].

### Witnesses (`SpanS23Witness.lean`) — at the U23 bridge's OWN events
- `s23w_span` (the parameterized fixture discharge, every premise
  concrete), **`s23w_span_s2fire`** at the bridge's
  `⟨1,2,2,7⟩/⟨2,2,2,8⟩` pair — the data bytes `[6]`/`[7]` code to
  EXACTLY the bridge's `7`/`8` (`s23w_data_codes`, axiom-free);
  violations 0→1, committed 1→2. **`s23w_span_s3fire`**
  (re-applied index), **`s23w_span_clean`** (zero violations, the
  slot appended). `s23w_s2hit_model` : the machine readout IS
  `s2Hit` at the projection — `rfl`, axiom-free.

### Audit (`Audit/SpanS23.lean`)
31 `#guard_msgs` pins verified in place (`lake env lean` exit 0,
zero output), readouts verbatim from `artifacts/probe/axs23.out`;
all within [propext, Classical.choice, Quot.sound]; the five
declaration/Func pins + the two model ties axiom-FREE.

- [AGENT] calls, tagged:
  1. **The `encGS` data code** (base-257, digits 1..256, injective,
     0 ↔ empty): the model's `AEv.data : Nat` vs the machine's
     `GoString` was an unpriced vocabulary mismatch in the banked
     route; resolved by a CONCRETE injection so the span states
     `s23Step` literally. The T1 assembly renames data through any
     injection; `encGS_inj` makes the transport sound (the
     assembly-seam note; same class as S1's `ClaimTrace` seam).
  2. **EntryNormal scope**: `s23_span_computes` takes the type value
     0 as a premise — the MODEL's own scope (the C4 note: v1
     proposes no conf changes); the anomaly branch's walk was
     deliberately not built (≈400 lines computing no model
     predicate). Recorded as scope, not a gap: the walk PROVES the
     branch untaken at EntryNormal.
  3. **`sliceVisibleValues` premises are first-order** (the
     array-cell + pointwise window facts) — the SliceMem
     hypothesis-style was rejected at the span level because it
     would smell of the ∀σ vacuity class; the walk transports the
     cell facts itself.
  4. **Per-decl heartbeat wall** (byIdx): four timeouts inside ONE
     giant decl (heartbeats are per-declaration) — split the hit
     path into `s23_byidx_hit_seg`. The debugging drill that found
     it: the whnf-grind-on-false-unification smell twice traced to
     WRONG sub-chain literals (11-not-13, 17-not-15) — the
     eval-before-decide lesson in unification form; counts now
     always spelled in the chain's own association.
  5. The s3term_seg statement had its icell payload silently
     clobbered (tmN for ixN) by a text transformation — caught
     IMMEDIATELY at the headline composition (the assembly is the
     checker of the segments). Fixed at the statement.

## LANDING MANIFEST (updated for SM1 + SM2 — the operator's
one-commit import additions)

At landing (after merge-protocol steps), add exactly these lines:

1. `proofs/Audit.lean`:
   `import Audit.Span` and `import Audit.SpanS23`
2. `proofs/GoLeanProofs.lean` (the aggregator, alphabetical spot):
   `import GoLeanProofs.Specs.Raft.SpanApplyGetters`,
   `import GoLeanProofs.Specs.Raft.SpanS1Witness`, and
   `import GoLeanProofs.Specs.Raft.SpanS23Witness`
   (the closures pull UtoaForKit, UtoaSpan, SpanCells, SpanS1,
   SpanS1Walk, SpanS23Maps, SpanS23Cells, SpanS23Apply,
   SpanS23Walk1-5, SpanS23 — nothing else is needed).

Then `scripts/ci` goes green with no other change (the un-swept red
is exactly SM1's 8 + SM2's 11 files; all 30 + 31 pins already verify
in-build via Audit.Span / Audit.SpanS23).

## SM2 unit-end gate record (2026-08-26)

`GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=96G LEAN_NUM_THREADS=16
scripts/ci` under the box-wide build lock
(`artifacts/lockgate-sm2.sh`, mkdir-lock + owner file + trap
release; WAITED through two other lock holders —
`coordinator-landing`, then `campaign-arc4-fixround` — exactly the
protocol's serialization): `artifacts/ci-arc4d-sm2.log`,
**GATE_EXIT=1 — the KNOWN NEW-FILES-ONLY RED, exactly as
chartered**:

- All other steps `ok` (oracle toolchain, escape hatches,
  bug-index, feature-coverage, spec anchors, lane validation,
  imported-goose verbatim + R2 pins, surface purity, statement-TCB
  closure, import-direction, core build warning-free, **proofs +
  Audit gate ok**, Challenge/Solution elaborate, verdi compat,
  golden lowering, frontend unit tests, eval tests 141 ok) + the
  two sanctioned no-diff notes (docs/proofs-only arc, hatch set
  explicitly, notes printed).
- **The ONE red, verbatim**: `FAIL proofs-file audit coverage
  (un-swept proof file — import it from Audit.lean or
  AuditCorpus.lean, or allowlist with a reason)`, listing EXACTLY
  the lane's 19 new files (SM1's 8: UtoaForKit, UtoaSpan, SpanCells,
  SpanS1, SpanS1Walk, SpanS1Witness, SpanApplyGetters, Audit/Span;
  SM2's 11: SpanS23Maps, SpanS23Cells, SpanS23Apply, SpanS23Walk1-5,
  SpanS23, SpanS23Witness, Audit/SpanS23) — the NEW-FILES-ONLY
  consequence; the landing manifest above makes it green in one
  commit.
- **Compensating checks (all run, exit codes captured)**: every SM2
  module `lake env lean` exit 0, ZERO warnings; every module built
  to olean via explicit `lake build +<module>` (up to 65 jobs,
  exit 0); `Audit/SpanS23.lean` — 31 `#guard_msgs` axiom pins —
  verified IN PLACE (`lake env lean` exit 0, empty output), axiom
  readouts verbatim from `artifacts/probe/axs23.out`, all within
  [propext, Classical.choice, Quot.sound], the five
  declaration/Func pins + two model ties axiom-FREE; hatch grep
  (`sorry|native_decide|GOLEAN_ESCAPE`) over all 11 SM2 files: **0**.
- Standing report-only notes, unchanged and re-escalated for the
  operator: comparator landmark STALE (now 188 commits) + OWED
  (scope, 2 Challenge-closure files) — standing since U8; NOT this
  arc's surface (no designated statement touched).

## SM2 EXIT (branch-complete; nothing merged)

**CHECKPOINT (recomputed):** worker commits on `campaign-arc4d`
since SM1's exit 365f4502: bb030366 (maps+cells), 3e0d40b2
(apply pin + bridge), 298987ff (walk 1), 3030c713 (walk 2 + walk 3
start), f7d4e0e9 (walk 3), 2a703c37 (lookup seg), e98d1d82 (spine +
S2 engine + miss), 67403811 (walk 5 + abs step), 9dc765ec (the
headline), 95e4d0be (witnesses + pins), bf720267 + faaa3745 + this
one (log/manifest/gate). New tracked files: 11 modules + log
appends.

**Deliverable state vs the SM2 charter:**
1. The string-keyed MapMem sibling — **DELIVERED** (promotable;
   promotion target recorded).
2. `slotFs` + `normalize_slotFs` — **DELIVERED** (+ the full
   slot-valued byIndex fragment).
3. The apply walk + **`s23_span_computes`** — **DELIVERED**: the
   whole `main.twin.apply` call at symbolic checker state computes
   `s23Step`'s fields literally; `s23_abs_step` is the projection
   commutation; fire (S2 at the bridge's own 7/8-coded events, S3)
   AND clean witnesses, every premise discharged.
4. The landing manifest — **UPDATED** (SM1+SM2).

**Which bridges are byte-closed:** S1 — YES (SM1). **S23 — YES**:
`s23_span_computes` + `s23_abs_step` close the U23
`S23CheckerInterface`'s interpreter half TO THE BYTES at symbolic
checker state, scoped to EntryNormal entries (the model's own
scope, C4 note) — the remaining S23 distance to T1 is the
`appliedLog` projection (`hlog`) + the event-data renaming through
`encGS_inj`, both assembly-time seams by design (S1's `ClaimTrace`
class). **O5's last piece is done.**

**Cost vs the 1-1.5-unit price:** ONE session ≈ 1.2 units at the
banked rates — within price. The two map fragments (SM1's measured
"≥2× the banked residue" trigger) came in at ≈0.25 units thanks to
the MapMem reuse pattern; the walk's overrun risk was absorbed by
the two lifted engines (`utoaUnit_walk`, the spine evaluator) —
leverage, not grind.

**PROPOSED NEXT CHARTER: none — the lane completes with this unit**
(as expected by the SM2 charter). Operator items: (1) the landing
manifest above (one green-making commit at landing); (2) the
standing comparator STALE+OWED escalation; (3) the recorded
promotion targets (`StrMapMem`, the spine evaluator absorbing
`concat6_eval`) for a future consolidation slice.

Nothing merged; branch-complete. Merge/audit-ask remain the
operator's (constitution §4.1).
