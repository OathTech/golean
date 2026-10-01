# Lane `core/intn-pick-0930` — handoff (window unit 5b, the native `Intn`-style pick site)

[AGENT] worker, 2026-09-30. Worktree `.claude/worktrees/intn-pick`, branch `core/intn-pick-0930` off `main` @
`bc91aa39` (main advanced to `ac6baa31` with two records-only commits during the lane; see §5). Authority: [USER] Mike
2026-09-30, item 2 of «The raft-proofs team's subject-delta note (2026-09-30) — RULED» (relayed): a GENERAL native pick
site, «a value in `[0, n)`, panic if `n ≤ 0`», inside the window before the single re-pin. Design note (read first):
`docs/2026-09-30_intn-pick-design.md` — decisions D1–D8 are [AGENT], PENDING [USER] ratification at the merge ask.

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

TBD — filled at the end of the lane (build; `ci --diff`; the whole-corpus choice trace vs `main`; `ci --slow`; the
elaboration-cost measurement against G-C3's 1.5× stop rule).

## 3. PENDING [USER] at the merge ask

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

## 4b. Operational note — the build lock and a late EXIT trap

Each build ran as `( trap 'rm -rf artifacts/build-lock.d' EXIT; scripts/capped lake build …; … )` after an atomic
`mkdir` with an owner line. Build 6's subshell reported completion only minutes after its log ended, so its lock
outlived the build (the next build's wait-retry loop waited on MY OWN stale tag); I verified no `lake build` of this
lane was running (a process LIST, never a kill), removed the lane's own lock, and re-checked the lock dir once the late
trap fired (it had not removed the successor's lock). Later builds release explicitly after the build as well as by
trap. Lesson for `docs/operational-lessons.md` if it recurs: a background subshell's EXIT trap is not a reliable release
under the agent harness; pair it with an explicit `rm` in the command chain and an owner-checked cleanup.

## 5. Rebase note

`main` moved `bc91aa39` → `ac6baa31` (train r57's 5a records and close; records only, no `GoLean/` change). The lane
rebases onto `main` before its gate run so the merge is `--ff-only`.
