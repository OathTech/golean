# Audit of `core/intn-pick-0930` at `f4276cdb` (window unit 5b, the native `Intn`-style pick site)

[AGENT auditor, branch `review/intn-pick-0930`, worktree `.claude/worktrees/audit-intn-pick`] 2026-10-01. Candidate tip
`f4276cdb` (8 commits over `main` @ `ac6baa31`, ff-mergeable). Under the [USER]'s every-merge-audited rule (relayed). The
candidate and `main` were not edited; no merge, no push. Reference for `main`: `git archive ac6baa31` built in the worktree's
`.tmp/main-ref` (its own frontend, scripts and binary). Oracle: `/usr/local/go/bin/go` = go1.26.5 linux/amd64 (the pin);
`deps/go` @ `c19862e5f8` (go1.26.5). Evidence (small): `docs/evidence/2026-10-01_intn-pick-audit/` — `probes.tsv`
(31 frontend probes + CLI runs), `forged.tsv` (6 forged-wire mutants), `gc-probe.go`/`gc-probe.txt` (the oracle's texts,
payload class, ranges), `trace-and-twin.txt` (sampled two-binary choice trace, twin-pin classification, certified-row
hash, BridgeSet mutation), `ci-slow-tail.txt` (the gate). Scratch under the worktree's `.tmp/` (bulk deleted at the end).

## Verdict: MERGE-CLEAN (Low records findings only; D1–D8 and option B stay PENDING [USER])

The lane's claim — ONE general `[0, n)` choice-tape draw (`ChoiceSite.intn`, `Stmt.randIntn`), the callee's `n ≤ 0`
guard emitted by the decoder as upstream's own `panic(string)`, `math/rand.Intn` + `math/rand/v2.IntN` bound at direct
call sites only, D-11 re-keyed onto it, eight born rows and nothing else moved — holds on every attack below. The findings
are records hygiene (F1, F2, F5), one pre-existing frontend scope gap the lane's wording over-claims (F3), and the
apparatus defect the lane itself reported (F4), none of which changes an observation or a trust-surface behaviour.

## 1. Faithful to Go (brief item 1)

- Pin texts: `deps/go/src/math/rand/rand.go:178–181` `if n <= 0 { panic("invalid argument to Intn") }`;
  `math/rand/v2/rand.go:191–193` `panic("invalid argument to IntN")`. Both are literal `panic(string)`; gc confirms
  (`gc-probe.txt`): `recover()` yields a `string` for both callees at `n = 0`, `-1`, `-2^62`; the uncaught abort lines are
  `panic: invalid argument to Intn` / `… IntN`; `Intn(1)` is 0 (20/20); 200 000 draws of `Intn(5)`, `IntN(3)`,
  `Intn(MaxInt64)`, `Intn(2^31−1)`, `Intn(2^31)` all inside `[0, n)`; `Intn(5)` exhibits all 5 members.
- Machine membership: `coverage-observations` on `Intn(5)` enumerates EXACTLY `{0,1,2,3,4}` (5 leaves, 1 site); `IntN(3)`
  `{0,1,2}`; tapes `[5]`, `[9]`, `[1000]` draw `0`, `4`, `0` (`Choices.consume` reduces mod the bound — `consume_fst_lt`
  is the proof that no member lies outside). `n = 1` draws 0 with no record. Huge bounds (`2^62`, `MaxInt64`) are REFUSED by
  name by the enumerator («site bound … exceeds the case's width … REFUTED») — fail closed, never a truncated set. A
  negative computed bound panics with no site consumed. A package-level `var x = rand.Intn(5)` and an `init()` draw are
  ENUMERATED by the init driver (`{0..4}`), not silently fixed at 0.
- Latitude model: Go ≥ 1.20 auto-seeds the global source, so the output of the package-level functions is latitude; the
  shapes that DETERMINE it — `rand.Seed`, `rand.New(src)` / method forms — refuse by name (§3). The envelope is the
  weakest machine for the bound callees; nothing wider is admitted (`stepFn`'s domain is `n ≥ 1`, a bound `≤ 0` at the
  apply is `stuck` by name, `Machine.lean` `.randIntn` arm).

## 2. The guard in the lowering (D2; brief item 2)

`expandRandIntn` emits `$intn := e; if $intn < 1 { panic(toInterface any string "<text>") }; randIntn target $intn` — the
same `panicStmt (.toInterface (.interface any) .string …)` shape the frontend's own `panic("lit")` decodes to (wrap =
string), so payload class and `recover().(string)` match gc for free; the born row `recover-string-payload` and the oracle
agree. Evaluation order (`probes.tsv`): `rand.Intn(f())` prints `f` THEN panics (argument evaluated once, before the
guard); `rand.Intn(g())` with `g` panicking aborts with `g` and draws nothing; `Intn(f()) + Intn(g())` prints `f`, `g`
(left-to-right; two hoisted draws). Forged wires (`forged.tsv`): a bool `n` is `stuck` («expected int value, got … bool»),
a string `n` and a nested `rand-intn` refuse at lowering by name, a forged callee / result type / absent `resultTypes` /
two targets refuse by name (the gate's 5 controls); a literal `0`/`−7` bound panics through the guard. The guard cannot be
skipped by any wire: only the decoder manufactures `Stmt.randIntn`, and it always emits the guard first. (F6 below: a
forged `int32` bound is normalized by the typed-local binding and draws — pre-existing binding policy, unreachable from
the frontend.)

## 3. Scope (D3/D5; brief item 3)

Refused BY NAME, naming the member and package (`probes.tsv`): `rand.New(...)` + `r.Intn` (method form), a nil `*rand.Rand`
receiver, `rand.Seed`, `rand.Int`, `Int63n`, `Perm`, `Shuffle`, v2 `N`, `Int64N`, `UintN`, `rand.New(rand.NewPCG…)`;
`defer rand.Intn(n)` / `go rand.Intn(n)` («lowers at direct-call sites only … refused by name»); `f := rand.Intn` (a
stdlib selector in value position). `rand.Float64()` refuses on the `println` float operand (FR-29) before reaching the
package quarantine — still a refusal. An aliased import (`import r "math/rand"`), an unaliased `math/rand/v2`, `len(s)`
as the bound, the blank target and the bare statement all lower to the primitive; a local type with its own `Intn` method
lowers as a user method (105), never as the primitive. Register: `primitive` 3 / cap 3, `check-stdlib-register` green in
the gate; the cap move is D5 — PENDING [USER] (§7). Gap: F3 (dot import), pre-existing.

## 4. Choice-tape coherence (brief item 4)

`consumeAtE .intn n.toNat` is the one consult, in the validate phase like the spill's; `intnBound?` is `none` at `n = 1`
(no record — `one` consumes nothing in the trace) and at a non-address target. No new `Step` constructor: the diff adds no
`| ` to `Step`; `Step_randIntn_draw` is a theorem over `Step.stmtOpApply` (BridgeSet row 134). The statements of
`stepFn_picks_none` / `_some`, `replay_coverage`, `stepFn_sound`, `step_complete` are untouched (no diff line names them
except comments); `stepFn_stmtOp_spill` was generalized to `stepFn_stmtOp_pick` (it was pinned nowhere; both uses updated);
no `set_option` added or raised anywhere in `GoLean/` (the mirrored `maxHeartbeats` was dropped in `4406c702`). BridgeSet
rows 1–132 are byte-identical (the diff is additions only); row 133 is REAL: mutating its `1 ≤ n` to `0 ≤ n` fails
elaboration against `applyStmtOp_randIntn_eq` (`trace-and-twin.txt`). The dedup engine refuses the site by name (D8).
Core totality audit: the gate's step (§8) with the 10 new required names.

## 5. D-11 re-keyed and the twin (brief item 5)

`derive.py --check` clean; `check-frontend-pins` ok on all three checks, the fresh twin emit = the pin `d5186f43…`. The
old→new pin diff reproduced key-by-key: 3159 hoist-temp renumberings + 230 `pos` line shifts + 0 other; everything else
sits inside `methods[lockedRand.Intn]` (2 subtrees — body and locals — where the lane counts 29 leaves). The re-keyed body
is lock / `v := rand-intn(Intn, n)` / unlock / return, `n` passed as the bound directly. Residual delta stated honestly in
the design §4 and `raft-w42-log.md`: the callee (`crypto/rand.Int` + `math/big` vs `math/rand.Intn`) and the unreachable
`n ≤ 0` text; `Config.validate` (`raft.go:313–319`) forces `ElectionTick > HeartbeatTick > 0`, so `n = electionTimeout ≥ 2`
at the one call site (`raft.go:2066`). The twin's election distribution: the machine admits every member of
`[et, 2·et)` — a superset of upstream's uniform draw; no raft replay/observation baseline depends on the twin's stream
(only the wire pin), and the removed map-range idiom removes a `mapIter` consult of the same width — no observable change
beyond the draw. Option B: four refused keys measured by the lane, POSED — PENDING [USER].

## 6. Zero unplanned change (brief item 6)

Baseline 3791 → 3799: exactly the 8 born `PASS` rows (5 strict, 3 membership); no existing row's result or stage moved
(diff = header + 8 rows). Sampled two-binary choice trace (40 `nondet` ids + `maps/jitter-draw`; `trace-and-twin.txt`):
dump rows IDENTICAL on all 42 common consuming ids (digest `536a2471dc529d63` both sides), results identical; the lane-only
consumers are exactly the four consuming born rows, site `intn` only. Certified row `imported-goose/channel/google-search`
lowered with BOTH frontends: `f448d579…` = the installed record (a provenance refresh at the train, not a re-pin).

## 7. Findings (by severity)

- **F1 — Low (records).** `Corpus/coverage/exec/maps/jitter-draw/main.go:3–6` still says the subject-tree D-11 patch
  «carries EXACTLY this draw» (the map-range idiom) — FALSE since D6; the file is not in the lane's diff. The handoff §1 and
  `docs/raft-w42-log.md` claim «its `main.go` comment says which [idiom it pins]» — it does not. Fix: one comment edit
  (comments do not reach the wire; `cases.tsv` line 6 has the same stale sentence). No observation affected.
- **F2 — Low (records).** `docs/stdlib-admission-register.md:73` («primitive (2) caps are enforced INSIDE») and `:172`
  («a PRIMITIVE admission (cap 2, [USER]-gated)») contradict the same document's rows 36 and 95 (cap 3, PENDING). Fix: two
  numbers (or an «at the time» marker on :172, which is a slice-2 narrative).
- **F3 — Low (scope gap; PRE-EXISTING).** `import . "math/rand"; Intn(5)` lowers to a bare user `call "Intn"` (no
  primitive, no package-named refusal); the CLI then answers `stuck: GoCore function not found: Intn` — fail-noisy, and the
  wire is byte-identical under `main`'s frontend. Not a regression; it narrows the lane's «every other shape refused by
  name» wording (`randintn.go` header, register row): dot imports are a frontend-wide gap, worth a ledger line.
- **F4 — Low (apparatus, trust surface #2; CONFIRMED, pre-existing).** `tools/coverageharness/main.go:407–416`
  `importName` = `path.Base`, so an unaliased `math/rand/v2` binds `v2`, is pruned as unused, and the oracle build fails
  `undefined: rand`. FAIL-NOISY only: the mis-named import is dropped (compile error), and the reverse (a retained unused
  import) is also a compile error — no fail-open direction found. Blast radius today: none — the only `/vN` imports in the
  corpus are the two born v2 rows, which carry the explicit alias and say why; `raftharness/harness.go` imports
  `math/rand/v2` but is not driven through `coverageharness`. Fix (one line: strip a `v[1-9][0-9]*` last element, goimports'
  rule) is the coordinator's, as the lane says; the alias workaround in two corpus rows is acceptable until then.
- **F5 — Low (hygiene).** The 8 born baseline rows sit at `baselines/native-full.tsv:1859–1866`, ABOVE the
  `result	id	stage` header row (`:1867`), not among the `builtins/` rows. `scripts/coverage-baseline-diff` skips the
  header wherever it appears and is order-insensitive, so nothing misparses; `main`'s body is not strictly sorted either.
  Cosmetic; worth moving at the next re-pin.
- **F6 — Info.** A forged `rand-intn` bound of kind `int32` is normalized by the typed-local binding (`$intn : int`) and
  draws at bound 5 rather than `stuck`. The same normalization applies to a user call's forged `int32` argument on BOTH
  binaries (105/105) — pre-existing binding policy, not this lane's; unreachable from the frontend (`emitRandIntnCall`
  pins `func(int) int`). Recorded, no action asked.
- **F7 — Info (PENDING [USER], not decided here).** Two reasoned departures from the window plan's letter
  (`docs/2026-09-24_window-plan.md` §4 unit 5b): (a) the plan lists `(*math/rand.Rand).Intn` among the callees; D3 binds
  only the package-level functions (a `*Rand` needs `rand.New`, outside the surface; a nil receiver dereferences in gc) —
  verified refused by name; (b) the plan says «a `Step` rule + `stepFn` arm»; D7 derives the rule from `stmtOpApply`
  (`Step_randIntn_draw`, pinned) and adds no constructor. Both are what the design note says, with reasons; they are the
  [USER]'s to ratify with D1–D8.

Statements checked and found accurate: the design's Go citations (`rand.go:178` is the `func` line, `:179–181` the guard;
`v2/rand.go:191–193` likewise); «no `Step` constructor»; «rows 1–132 byte-identical»; «statements unchanged»
for the four coherence theorems; the 3159 / 230 / 0 twin classification; «the whole-corpus choice trace identical except
the born rows» (sampled here, §6); `f448d579…` unchanged; `derive.py --check` clean; elaboration — no `set_option`
movement (timings not re-measured here).

## 8. Gate

Builds under the box-wide lock (`scripts/capped`, `GOLEAN_MEM_MAX=48G`): the candidate's `lake build GoLean golean
gocore-eval-tests` — 114 jobs, 0 errors, 0 warnings, EXIT 0 (cache warmed from the lane's worktree with its 193 + 15
foreign-path `setup.json`/trace files purged first, as the handoff §4c warns); `main`'s reference build in `.tmp/main-ref`
— 109 jobs, EXIT 0.

`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `f4276cdb` (2026-10-01, wall 1133 s, quiet box; tail in
`ci-slow-tail.txt`): **EXIT 1 on EXACTLY the 5a pair** — `FAIL certificate provenance` (reconciler C9 HIGH: STALE
certification, changed dependency `GoLean/ChoiceTrace.lean` and kin — the train's step 5a, a provenance refresh since the
certified row's wire is unchanged, §6) and `FAIL baseline diff` with the ONE drift line `imported-goose/channel/google-search
baseline[PASS/membership] -> now[FAIL/membership]` (the certified slow-tier row; `cases=3799 pass=3561 fail=238` = the
pin's 3562 / 237 with that row). Every other step `ok`: oracle toolchain go1.26.5 = pin, escape-hatch scans, bug index,
feature coverage, spec anchors, stdlib register = frontend tables (3/3 primitives), evidence size, AGENTS alias, goose
verbatim, engine isolation, memory-module call sites, core build warning-free, core totality audit (required list incl. the
10 new names; poison controls), admission audit, declaration boundary, wire boundary (incl. the 5 `rand-intn` controls),
method identity, unseq Stage B/C (56 mutants), frontend pins (twin = `d5186f43…`), goose fixtures, frontend unit tests,
lowering-diagnostic tables, harness unit tests, eval tests 298, lane-validation self-tests (the T1–T8 «TIMED OUT after 1s»
rows are the self-tests' expected content, all `ok`), negative corpus 394 matched, FloatVectors + inittask regenerations
byte-exact. Reconciler: C9 (the 5a item) and the pre-existing C13 only. The `git_dirty` note is this audit's untracked
note and evidence. No load flakes on this run.

## 9. PENDING [USER] at the merge ask (assessed, not decided)

D1–D8 (`docs/2026-09-30_intn-pick-design.md` §3) are each implemented as written and verified above: D1 (site, slot 0 =
0, bound `n` exactly), D2 (guard in the lowering; payload class matches gc), D3 (method forms not bound — refusals verified;
departs from plan §4's listing, F7a), D4 (discard still draws — the trace shows the consult), D5 (cap 2 → 3 — the number
is the [USER]'s), D6 (D-11 re-keyed; residual stated), D7 (derived rule, pinned 133–135; departs from plan §4's «Step
rule», F7b), D8 (dedup refuses by name). Option B (retire D-11 to upstream's verbatim `crypto/rand` + `math/big` body):
measured at four refused keys, POSED — a separate [USER] decision. The baseline re-pin (born rows only) and the twin re-pin
are both verified as described.

## 10. Not verified here

The whole-corpus choice trace (3757/3765 rows; the lane's `7748758dff29ca9a` digest) — sampled at 42 consuming ids
instead; the per-module elaboration timings (1.00–1.05×) — not re-measured, but no `set_option` moved; the lane's run-1/2
flakes — not reproduced (the gate here ran on a quieter box, see §8).
