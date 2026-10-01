# Lane `core/intn-pick-0930` — handoff (window unit 5b, the native `Intn`-style pick site)

[AGENT] worker, 2026-09-30. Worktree `.claude/worktrees/intn-pick`, branch `core/intn-pick-0930` off `main` @
`bc91aa39` (main advanced to `ac6baa31` with two records-only commits during the lane; see §5). Authority: [USER] Mike
2026-09-30, item 2 of «The raft-proofs team's subject-delta note (2026-09-30) — RULED» (relayed): a GENERAL native pick
site, «a value in `[0, n)`, panic if `n ≤ 0`», inside the window before the single re-pin. Design note (read first):
`docs/2026-09-30_intn-pick-design.md` — decisions D1–D8 are [AGENT]; PENDING [USER] ratification at the merge ask, RATIFIED [USER] Mike 2026-10-01 at train r58 —
«agree, land it, ratify all including the harness fix» (relayed by the [AGENT] coordinator — cite as relayed); option B not taken (§3).

## 1. What landed (the design as built)

- **The site.** `ChoiceSite.intn` (`State.lean`, canonical slot 0 = the value 0). **The statement.** `Stmt.randIntn
  (target : Option Assignee) (n : Expr)` (`Syntax.lean`; its docstring is the envelope statement) riding the
  wide-statement machinery: `StmtOp.randIntn`, `stmtPlan` (target address first, then `n`; `nt = 0` in the
  discarded-result form), `applyStmtOp.plan`'s arm — ONE `Choices.consumeAtE .intn n.toNat` consult, the pick stored as
  `.int pick .int`; a bound `≤ 0` is `stuck` by name (unreachable for a decoded program, see the lowering). `intnBound?`
  + the `stmtConsult?` arm are the `seqConsumption` projection (nine sites).
- **The lowering (D2).** Frontend `tools/nativefrontend/randintn.go`: a direct `math/rand.Intn(n)` / `math/rand/v2.IntN(n)`
  call emits `{"expr":"rand-intn","callee":<Intn|IntN>,"n":…,"resultTypes":[int]}`, effectful, hoisted like a call;
  `defer`/`go` of the function refuse by name. Decoder `GoLean/NativeToIR.lean` (`asRandIntnOp?`, `expandRandIntn`):
  `target := rand-intn(e)` → `$intn := e; if $intn < 1 { panic("<callee's text>") }; randIntn target $intn` — upstream's
  own guard as a language-level `panic(string)` (the payload class gc realizes; an apply-arm panic would box as
  `runtime.Error`). Forged callee tag / non-`int` result / node in expression position refuse by name.
- **Coherence.** No new `Step` rule (`Step.stmtOpApply` covers the apply). The «one step rule» is DERIVED:
  `Step_randIntn_draw` (for every `i < n` the singleton tape steps with label `⟨tr, PickRecord.ofPick .intn n.toNat i, []⟩`)
  beside the apply equation `applyStmtOp_randIntn_eq`. `stmtConsult?_some` is a disjunction now; `stepFn_stmtOp_spill`
  generalized to `stepFn_stmtOp_pick`; `consumesRandIntn` threaded through `stepFn_oblivious` /
  `seqConsumption_none_of_flags` / `allStreamsOk` / `poolThreadOblivious` / `innerVecs` (the dedup engine refuses the
  site, D8 — the default enumerator carries the rows). NEW int-store class congruence chain (`normalizeValueForTyTy_int_congr`
  → `Mem.store_int_congr` → `applyStmtOp_randIntn_congr`) for the ∀-streams kit (`applyStmtOp_congr_any_ch`'s new case).
  `stepFn_picks_none` / `_some`, `replay_coverage`, `stepFn_sound`, `step_complete`: statements unchanged, re-proved.
- **Register.** `primitive` row `rand-intn`; cap 2 → 3 (D5, POSED). `docs/stdlib-admission-register.md` block regenerated,
  header + slice log updated; `check-stdlib-register` green.
- **Subject.** D-11 re-keyed (`tools/raftsubject/derive.py`: `swap_imports` crypto/rand → math/rand; body = lock /
  `v := rand.Intn(n)` / unlock); `derive.py --check` clean; twin wire `8a158eff…` → `d5186f43…` (reason:
  `scripts/check-frontend-pins`' comment block; classification script §4). Ledger: `docs/raft-w42-log.md` (2026-09-30
  continuation), dated pointer in `docs/raft-w41-log.md`, `raftsubject/README.md`.
- **Rows.** `Corpus/coverage/exec/builtins/rand-intn/{membership,v2-membership,one,zero-panics,v2-negative-panics,
  recover-string-payload,jitter-shape,discard}` (tag `rand` added to `Corpus/coverage/tags.tsv`). Wire-boundary controls:
  `Tests/wire-boundary-randintn/main.go` + 5 controls in `scripts/check-wire-boundary`.
- **Records.** Latitude inventory §0 row; changelog row 5b (`docs/changelog/61958f2e-WINDOW.md`); BridgeSet re-pin 7 and the
  core audit's required list (§3).

## 2. Gate results

1. **Build.** `scripts/capped lake build GoLean golean` green at the runtime tip — 109 jobs, 0 errors, 0 warnings
   (eight iterations; the proof-side repairs were: `Stmt.locSup`'s two-arm form, `applyStmtOpCore_wf`'s refusal arm,
   the `hri` inequality on the two core-dispatch lemmas, a mis-parsed `absurd`, `intnBound?_some` by `by_cases`, the
   nested-bind congruence by case analysis on both stores, the `MultiStreams` flag argument, the `StepErrors` commit
   arm). `scripts/check-stdlib-register` green (3/3 primitives; overlay rows verified). `derive.py --check` clean.
2. **Born rows.** `scripts/capped scripts/diff-one` over the 8 ids + `maps/jitter-draw`: 9/9 PASS (2026-10-01 00:05Z) —
   `membership` enumerated 5 / exhibited 5 (11 draws, stopped at the `members=5` pin), `jitter-shape` 5/5,
   `v2-membership` 3/3, the three `n` controls and the payload-class control strict PASS, `discard` PASS (invariance
   re-run across streams). The two v2 rows first FAILED at `go-run` on the oracle-harness `/v2` import defect (§4a) and
   pass with the explicit alias.
3. **Wire boundary.** `scripts/capped scripts/check-wire-boundary`: PASS — 11 + 56 + 13 + 16 + the 5 new `rand-intn`
   controls (`ri` answers 42; `ri-bad-callee`, `ri-result-not-int`, `ri-absent-resultTypes`, `ri-two-targets` refuse
   naming the cause).
4. **Whole-corpus choice trace vs `main`: IDENTICAL except the born rows.** Pre = the primary checkout at `ac6baa31`
   (its own frontend and binary, `scripts/choice-trace-corpus --jobs 4 --dump --out <root-relative dir>`), post = the
   lane; the two B6 exclusions (`goroutines/send-then-spin`, `strings/trimspace-repeat/repeat-bound-refused` — the
   first spins to the fuel cap under every stream and stalled chunk 1 on BOTH sides for ~1 h; killed by PID, the chunk's
   remaining ids re-traced with `--exclude`). 3757 / 3765 rows exported (pre / post; the same 34 frontend refusals).
   Consuming ids 790 → 794: the four new ids are exactly the born rows that CONSUME (`builtins/rand-intn/{membership,
   v2-membership,jitter-shape,discard}`, 6 streams each, site `intn` only); the other four born rows consume nothing by
   design (`n = 1` pops nothing; `n ≤ 0` panics ahead of the draw). Ids only in pre: none. Ids with changed rows: NONE
   — the sorted dump rows of the 790 common ids digest `7748758dff29ca9a` on both sides (25404 → 25428 rows = +4×6).
   The raft twin is not an executable-corpus row (its draw moves in the twin pin, §1). Comparison script: §4.
5. **Elaboration cost (G-C3's 1.5× stop rule): INSIDE.** `scripts/capped lake env lean <file>` per module, before =
   `main`'s sources in the primary checkout, after = the lane, same box, sequential under the lock (2026-10-01
   00:05–00:22Z): StepErrors 227.3 → 227.8 s (1.00×), MachineSound 69.8 → 71.7 (1.03×), NativeToIR 89.0 → 89.0,
   StateWf 17.1 → 17.3, PrefixFacts 15.8 → 16.0, SyntaxEqb 8.0 → 8.4 (1.05×, the max), MachineEqb 5.0 → 5.0, Machine
   4.4 → 4.5. No `maxHeartbeats` raised; the one NEW setting the int-congruence chain had mirrored was REMOVED and the
   gate's build confirms it unnecessary.
6. **`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at the fix-round tip (run 3, quiet box, 2026-10-01
   01:41–01:58Z, wall 1030 s): EXIT 1 on EXACTLY the 5a pair** — `certificate provenance` STALE (changed dependency
   files, `GoLean/ChoiceTrace.lean` and kin; the train's step 5a) and the ONE drift line `imported-goose/channel/
   google-search PASS/membership → FAIL/membership` (the certified slow-tier row, STALE certification — the same line B6
   and C3 reported); `cases=3799 pass=3561 fail=238` = the pin's 3562 / 237 with that row; the row's program draws
   nothing, so its WIRE is unchanged (§2a). Every other step ok: core build warning-free, core totality audit (the
   required list with the 10 new names), admission audit, declaration boundary, wire boundary (incl. the 5 `rand-intn`
   controls), method identity, frontend pins (twin = the new pin), stdlib register, lowering-diagnostic tables, eval
   tests 298, Go tests, the lane-validation self-tests, negative lane 394 matched. Reconciler: C9 (5a) and the
   pre-existing C13 only. The `git_dirty` note is this handoff, committed after the run.
   Runs 1 and 2 (same tip modulo the fix round) surfaced and resolved: (i) the baseline's `# reason:` block detached
   from its alternation row by my first edit (`baseline diff` REFUSED — fixed in place); (ii) the `lowerdiag`
   vocabulary (3 new frontend formats); (iii) the warmed cache's foreign absolute paths (`declaration boundary`, §4c);
   (iv) two load-induced 1 s / subprocess-timeout flakes in the lane-validation T3 self-test and the method-identity
   audit while eight tracer processes ran — both green on their quiet re-runs (`check-method-identity` alone: PASS).

### 2a. The certified slow-tier row's wire (for the train's 5a step)

`imported-goose/channel/google-search`: the fresh `certification-candidate.json` of run 3 carries `wire_sha256
f448d579dfdbaadbbeceabe9f3872638552ae7331aa4c1740db5a5333d98f5d2` = the installed record's (B6's hash). The program
draws nothing, the frontend change touches only `math/rand.Intn` / `math/rand/v2.IntN` call sites, so the wire did not
move; the row's STALE certification is the changed-dependency inventory (`GoLean/ChoiceTrace.lean` and the other
touched modules) — a provenance refresh at the train (the r55/r57 precedent), not a re-pin. This lane does not touch
`baselines/certified/`.

## 3. PENDING [USER] at the merge ask — RULED 2026-10-01

RATIFIED [USER] Mike 2026-10-01 — «agree, land it, ratify all including the harness fix» (relayed by the [AGENT] coordinator — cite as relayed): items 1 and 3 ratified
as posed (D1–D8, the cap 3, both re-pins); item 2, option B, NOT taken; the §4a harness fix included (train r58 prep, audit
F4). The list as posed at the lane's tip:

1. Design D1–D8 (`docs/2026-09-30_intn-pick-design.md` §3) — in particular D2 (the guard lives in the lowering, the machine
   op is the draw alone with domain `n ≥ 1`), D3 (method forms NOT bound), D5 (the primitive cap 2 → 3).
2. Option B (retiring D-11 to upstream's verbatim `crypto/rand.Int` + `math/big` body) — measured at four refused keys,
   POSED, not taken (design §2).
3. The baseline re-pin (born rows only) and the twin re-pin (D-11's body).

## 4. Tooling notes

- Twin-diff classification (the written reason): `python3` over the two wires — walk both JSON trees; classify each
  difference as (a) inside `methods[i]` with `id.name == "Intn"` and `recvType == "raft.lockedRand"`, (b) a value change
  where both sides match `\$[a-z]+\d+` (hoist-temp renumbering), (c) a `.pos` change `raft.go:L:C` → `raft.go:L':C`,
  (d) other. Result at the pin: 29 / 3159 / 230 / 0 of 3418.
- `scripts/lower-diagnose .tmp/probe4` on upstream's verbatim `lockedRand.Intn` body (design §2 B).

## 4a. Apparatus FINDING (trust surface #2, NOT touched by this lane) — `/vN` imports in the oracle harness

`tools/coverageharness/main.go` `importName` assumes an unaliased import binds `path.Base(path)`; for `math/rand/v2`
that is `v2`, never used as an identifier, so `pruneUnusedImports` drops the import and the oracle's Go build fails
(`undefined: rand`) — FAIL-NOISY (the row goes red at `go-run`), not fail-open. Go's rule is the imported package's
clause (`rand`); goimports' assumed-name convention strips a major-version suffix `v[1-9][0-9]*` and takes the previous
element. The two v2 rows spell the import with the explicit alias `rand "math/rand/v2"` (legal Go, honoured by
`importName`'s `spec.Name` branch) and say why in a comment. The fix (the assumed-name rule in `importName`) is a
one-liner on the DIFFERENTIAL APPARATUS and therefore not this lane's to make — posed for the coordinator.
**FIXED 2026-10-01** [AGENT], train r58 prep (branch `prep/r58-0930`, [USER]-ratified with the lane — «… including the
harness fix», relayed): `assumedImportName` applies goimports' rule; born row `builtins/rand-intn/v2-membership-unaliased`
(red-first + gc evidence `docs/evidence/2026-10-01_r58-harness-fix/`). The two aliased v2 rows keep their alias as coverage of
the aliased spelling.

## 4b. Operational note — the build lock and a late EXIT trap

Each build ran as `( trap 'rm -rf artifacts/build-lock.d' EXIT; scripts/capped lake build …; … )` after an atomic
`mkdir` with an owner line. Build 6's subshell reported completion only minutes after its log ended, so its lock
outlived the build (the next build's wait-retry loop waited on MY OWN stale tag); I verified no `lake build` of this
lane was running (a process LIST, never a kill), removed the lane's own lock, and re-checked the lock dir once the late
trap fired (it had not removed the successor's lock). Later builds release explicitly after the build as well as by
trap. Lesson for `docs/operational-lessons.md` if it recurs: a background subshell's EXIT trap is not a reliable release
under the agent harness; pair it with an explicit `rm` in the command chain and an owner-checked cleanup.

## 4c. Operational note — warming `.lake/build` from a cache that was itself warmed elsewhere

The lane warmed `.lake/build` from the primary checkout (sources identical at the time). That cache had been warmed from
the `continuations` worktree by an earlier train, and 50 of its `*.setup.json` / `*.trace` files still carried ABSOLUTE
paths into `.claude/worktrees/continuations/.lake/…`. Lake judged the oleans current (content hashes), so the stale
files survived every build; the first gate run then FAILED `declaration boundary`, which runs `lake env lean --setup
.lake/build/ir/<module>.setup.json` directly and could not open the foreign path. Remedy applied: `grep -rlZ
worktrees/continuations .lake/build | xargs -0 rm -f` (the gate's own `lake build` regenerated them — deterministic
oleans, no cascade). Lesson for `docs/operational-lessons.md`: after warming, purge cache files that name another
worktree, or warm only from a cache built in place. (Also: zsh does not word-split an unquoted `$files` — the first
purge attempt removed nothing; use `xargs -0`.)

## 4d. Operational note — pattern-derived PIDs

Terminating the two fuel-capped tracers (§2 item 4) by PID, the PID list came from `pgrep -f "golean choice-trace
--batch"`, which also matched the tool shell running that very command (its command line contains the pattern); the
signal went to my own shell as well (harmless — it survived). Filter pattern-derived PID lists to the intended binary
(`pgrep -f "bin/golean choice-trace"`) before signalling; never signal a list without reading it.

## 5. Rebase note

`main` moved `bc91aa39` → `ac6baa31` (train r57's 5a records and close; records only, no `GoLean/` change). The lane
rebases onto `main` before its gate run so the merge is `--ff-only`.

## Merge train r58 — the 5a record ([AGENT] coordinator, 2026-10-01)

[USER] Mike 2026-10-01 «agree, land it, ratify all including the harness fix» (relayed). Pre-merge main `ac6baa31` →
`refs/snapshots/r58/main`; train tip `723939b3` fast-forwarded. The first `ci --slow` (1253 s) was red on the 5a pair PLUS
`declaration boundary` and `executed library coverage`: the primary checkout's `.lake/build` held 55 files naming
`.claude/worktrees/continuations/…` (an r56 warm copy by the coordinator; that worktree's `.lake` was later pruned) — a
coordinator process defect, not a candidate defect. The 55 files were purged (list in `artifacts/train-r58/`), the build
redone, and `ci --slow` re-run (1047 s): red on EXACTLY the 5a pair; 3800 rows, 3562 PASS / 238 FAIL = the pin 3563 / 237
with the one 5a-class row red. Candidate: `claim` and `observations_sha256` IDENTICAL (receipt `723939b3`, 156.864 s) —
INSTALLED; a provenance refresh. Tail: `docs/evidence/2026-10-01_r58-harness-fix/r58-ci-slow.tail.txt`.

**Green re-run at the records commit `2230c84c`** ([AGENT] coordinator, 2026-10-01): `ci --diff` EXIT=0, `RESULT: PASS`, baseline diff FULL 3800/3800, certificate provenance ok. Round 58 closed: the native Intn pick site landed.
