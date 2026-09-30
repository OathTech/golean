# Pre-merge adversarial audit — lane `core/continuations-0929` (window row 4 / packet C, `Cont := List Frame`)

STATUS: **VERDICT MERGE-CLEAN** — no FIX-FIRST finding; four LOW and two TRIVIAL notes, none blocking. [AGENT] auditor,
2026-09-30, branch `review/continuations-0929` (worktree `.claude/worktrees/audit-continuations`) under the [USER]'s
every-merge-audited rule (relayed). Candidate tip `fffa3212` (`121d8501` design note · `3ff30fa6` ledger + brief refresh ·
`3be9a643` runtime, TRUST-SURFACE #1 · `fffa3212` records) over `main` @ `883ebc36`. Nothing on the candidate or `main`
edited; no merge, no push. Evidence (small): `docs/evidence/2026-09-30_continuations-audit/`.

Method: independent reproduction, not re-reading the lane's evidence — `main`'s binary rebuilt from `git archive
883ebc36` (capped, under the box lock); the candidate's binary from a `.lake` warmed from the lane worktree after
verifying every Lean source identical; every corpus wire, every enumerating-lane row and the whole-corpus choice trace
run through BOTH binaries; theorem statements dumped from the two environments and diffed name by name; axioms swept;
BridgeSet pins mutated; `fun_cases stepFn` re-counted at both commits; elaboration A/B re-measured; the gate re-run.

## Findings (by severity; witnesses in the evidence files or inline)

- **F1 — LOW, records.** `fun_cases stepFn`'s frame arms now bind `fid` BEFORE `k'` (the view `Cont.frame … k fid`
  unfolds to `Frame.frame … fid :: k`): `stepFn.fun_cases_unfolding`'s motive premises read `(fid : FuncId) (k' : Cont)`
  where `883ebc36` had `(k' : Cont) (fid : FuncId)` (`static-checks.txt`). Changelog row 4 says the positional tags are
  unchanged (TRUE — 162 cases, `case140`/`case155` the same arms at both commits) and «the tail binder comes FIRST in
  `rename_i`» for `cases`-shaped splits; the `fun_cases`-shaped swap (`fid`/`k'` only) is not mentioned. A downstream
  `rename_i` on a `fun_cases stepFn` frame arm binds the two names swapped. Recommend one clause in the row / handoff at
  the 5a records commit (records only; no code change).
- **F2 — LOW, robustness.** `stepFn_sound` / `stepFn_consumption_none` close the `.retV`/`.next` catch-all refusals by
  POSITIONAL tag (`case case140`, `case case155`, `MachineSound.lean:1693/5845`). Fragile to any arm inserted before
  them, but FAIL-NOISY either way (the direct close fails on a wrong arm; a moved catch-all falls to the generic
  `simp_all [stepFn]`, which the lane measured at ~9 s and past the default heartbeats). `fun_cases` offers no named
  tags; a shape-guarded `first` alternative would cost a failed attempt on ~160 goals — not cheap enough to recommend
  blind. Recommendation: accept; packet D (which re-touches these proofs for the per-arm equations) should attach the
  direct close to the arm's SHAPE (the `h : throw … = .ok _` hypothesis), not its number.
- **F3 — LOW, informational.** Among 3837 theorems common to both commits, 221 elaborated statements print
  differently; 220 are auto-generated equation/unfolding/induction principles (`.eq_N`, `.eq_def`, `match_N.congr_eq_N`,
  `induct_unfolding`, `fun_cases_unfolding`) whose compiled patterns now print `[]` for `.stop` and `Frame.frame … fid
  :: k'` for the frame view. The ONE human-written theorem is `execStmtLoop_unfold` (`MachineSound.lean:6587`): its
  statement is a `match c with | .next .stop => …`, so the elaborated pattern reads `.next []`. Source text and meaning
  unchanged (`Cont.stop` is `[]` by `rfl`). Every other human-written statement — every coherence theorem, every packet
  A/B `_stmt`, every P lemma, the 89 pre-existing BridgeSet rows — is IDENTICAL as printed. The evidence README's «no
  theorem statement edited» holds at the source level; this is the only elaboration-level residue.
- **F4 — LOW, reach of the list laws.** «Frame exit as a list law» is thin: `stepFn_next_frame` is the view unfolding
  (`rfl`) and `stepFrameExit_nil` covers only the frame with no targets, no results and no defers. The defers-run and
  result-read cases are exactly packet D's request-7 equations (G-C3 decision 2) — consistent with the ruling, but D's
  brief should name them so the customer's frame-exit reasoning gets real equations, not a `rfl`. The other laws DO
  serve the customer's shapes: the logic repo (`~/projects/golean-logic`, pinned at `61958f2e`) proves `pushDefer (…) k
  = some next` facts by hand-stepping `Cont.rebuild_descend (by rfl)` / `dsimp only [Cont.tail]` / `Cont.rebuild_act`
  (`packages/golean-iris/GoLeanIris/Unwind.lean:37–84`); `pushDefer_eq`/`pushDefer_some` state that walk once for any
  statement-glue prefix, and their `Control.Agrees` spine (`.stop`/`.seq`/`.frame`) is a `List Frame` induction with
  `Cont.class_cons`/`Frame.class`. Their `cases k <;> simp_all [panicPassthrough, Cont.isGlue, Cont.class, Cont.tail,
  stepFn]` (`Unwind.lean:105`) and `case next k => cases k <;> simp_all` (`Language.lean:29`) are the disclosed re-pin
  cost (nil/cons then `cases f`; `Frame.class` beside `Cont.class`) — the changelog row says exactly this.
- **F5 — TRIVIAL, design note (not the lane's records).** D6 lists `pushDefer_eq`, `seqCont_eq` as «already present and
  kept»; only `recoverResult_eq` pre-existed — both others are new at `3be9a643` (the handoff and changelog say so
  correctly).
- **F6 — TRIVIAL.** The handoff is 80 lines against the brief's ≤ 60; the brief §7 commit template differs from the
  repo's TRUST-SURFACE convention (the brief's «as executed» note covers it).

## Attack results

1. **Zero behaviour change — reproduced independently.** `main`'s binary from `git archive 883ebc36`: sha256
   `697001fc…feb52c` — bit-identical to the lane's pre binary AND to the certified record's `receipt.binary_sha256`.
   Candidate `8e042f19…3b5f4`. (a) 3755 exported wires × `native-json-run` (gate flags, default stream, order
   alternated per row): stdout + exit code AND stderr identical for all; 3084 exit 0 / 671 exit 1 both sides
   (`wires.txt`). (b) Enumerating lanes, the gate's argument construction (`parse_lane_params` → `coverage-observations
   --max-width/--max-sites/--cap/--work-cap/--expect-status/--backedge/--engine/--allow-nonterm`): 384 rows — 102
   confluent, 237 membership, 45 racy (every manifest row of those lanes except the lane's standing exclusion
   `goroutines/send-then-spin` and the slow-tier row) — observations, enum-stats and exit identical; the two exit-1 rows
   are the baseline's FAIL rows (`worker-pool/sum`, `box-sync-stub-race`), same text both sides. The slow-tier certified
   row `imported-goose/channel/google-search` (work 60 000 000, dedup engine): 6 members both sides, `observations_sha256`
   = the certified record's, enum-stats sha = the receipt's `stats_sha256` (nodes=6193933 edges=6565663
   dedupHits=371731) — dedup state hashing (`contDepth`) and the statistics unchanged (`enumeration.txt`). (c) Whole-
   corpus choice trace (`scripts/choice-trace-corpus --dump`, 6 streams, 8 jobs, the lane's two exclusions): all 8
   `dump-*.tsv` byte-identical (26419 rows incl. chunk headers), `results-1..7` identical, `results-0` identical after
   normalizing the one embedded `--out` path (`arrays/materialization-budget/over-budget`'s refusal text), exhausted-
   strict/confluent, export-fail (34), batch (3755) identical, the 3755 exported wires identical, both runs exit 1 on
   the summarizer's standing findings (`choice-trace.txt`). Fuel: `Cont.eqbF`'s text is unchanged (one unit per frame);
   `contDepth`'s text unchanged (views); the certified row's dedup statistics equal — the fuel-sensitive rows are in
   (a)/(b) and identical.
2. **Faithful to the four decisions.** No `Config` change (`inductive Config` untouched); no `fill`/append law, no
   `recover` commutation claim — the only `fill`/`commut` mentions in Lean or the lane's docs are disclaimers (plus the
   pre-existing `signalStep` doc line at `Machine.lean:4216`, present at `883ebc36:3995`). `Cont.frame targets tenv
   results defers k fid` (k before fid) and `Frame.frame targets tenv results defers fid`; `Cont.stop : Cont := []`;
   `breakableK`/`boolK`/`panicArgK`/`probeK` nullary; 32 `Frame` constructors in the pre-C3 order, fields verbatim minus
   `k`; `Frame.class` = the old `Cont.class` table minus the `.stop` arm, no default arm (`static-checks.txt`).
3. **Soundness.** `collectAxioms` over every theorem of Machine, MachineEqb, MachineSound, StateWf, StepFn, UnseqSound,
   BridgeSet: 2195 theorems (post) / 2238 (pre), zero beyond `propext`/`Classical.choice`/`Quot.sound`; the gate's core
   audit sweeps the whole closure (below). `cases_cont` is a `syntax`+`macro_rules` tactic macro used in proofs only
   (`Machine.lean` ×3, `MachineSound.lean` ×4, `StateWf.lean` ×4); no `sorry`/`axiom`/`native_decide`/`partial`/
   `set_option` among the added lines. Statements: every human-written theorem identical as printed (F3 for the one
   `match`-statement residue); only-in-pre = 316 auto-generated lemmas (the old inductive's `inj`/`injEq`/`sizeOf_spec`,
   `Cont.class/tail/withTail.eq_N`, `stepFn.match_N.congr_eq_N`), only-in-post = 27 new human theorems + auto-generated.
   `Step`: 128 constructors, identical list in order at both commits (from `InductiveVal.ctors`). `fun_cases stepFn`:
   `case162` exists and `case163` does not at both commits; `case140` is the `.retV v k` catch-all (26 overlap
   hypotheses) and `case155` the `.next k` catch-all at both. Types of `Cont.rebuild`/`tail`/`withTail`/`class`/
   `pushDefer`/`recoverResult`/`Cont.sizeOf_tail_lt`/`Cont.rebuild_stop` identical. Definition TEXT identical at both
   commits for `stepFn` (627 lines), `stepFrameExit`, `execStmtLoop`, `signalStep`, `seqConsumption`, `pushDefer`,
   `seqCont`, `panicPassthrough`, `recoverAtDeferred`, `recoverResult`, `Cont.locSup`/`ownSup`/`isGlue`. No `deriving`
   on `Cont` (pre) or `Frame` (post), no `Repr`/`BEq`/`Hashable`/`Inhabited Cont` instance either side, no `sizeOf`
   outside proofs — no instance-mediated behaviour path exists.
4. **List laws.** All 27 new theorems elaborate; the proofs are `rfl`, list induction or `cases_cont`. Pinned: BridgeSet
   rows 90–107, `example : T := @name`; mutating row 93 (`pushDefer_eq`'s `(d :: ds)` → `ds`) and row 101
   (`panicPassthrough_eq`'s branches swapped) each fails the file with `Type mismatch`; the unmutated file elaborates
   clean. `Tests.GoCoreAudit.exports.length = 144` (`#eval`), all 34 additions present (the gate's audit step passes).
   Usefulness for the customer: F4.
5. **Elaboration (decision 4) — the stop rule is NOT triggered, re-measured.** A/B interleaved pre→post per module,
   back to back, capped, under the lock, two reps (`elaboration.txt`). Rep 2 at load 5–6 (the lane's conditions), wall
   s pre → post: StepFn 0.97 → 1.00 (1.03×), Machine 4.34 → 4.16 (0.96×), MachineEqb 4.89 → 4.89 (1.00×), BridgeSet
   0.86 → 0.93 (1.08×, 0.07 s), StateWf 17.29 → 17.19 (0.99×), MachineSound 64.99 → 64.15 (0.99×), StepErrors 220.84 →
   220.25 (1.00×) — worst 1.08×. Rep 1 ran under other projects' load (6–23) and is noise-dominated (StepFn 0.68×,
   Machine 1.33×, MachineEqb 0.76×; MachineSound 0.97×, StepErrors 1.03×); kept in the evidence, not relied on. This
   agrees with the lane's interleaved numbers (max 1.07× MachineSound) and does not reproduce its loaded first-run 2.8×.
   `set_option maxHeartbeats`/`maxRecDepth`: 59 lines at both commits, identical values (sorted listing differs by line
   offsets only) — none new, none raised.
6. **Records.** Changelog row 4 (both the long row and the table line) accurate against the diff: constructor shape
   before → after, the views' argument order, `.stop = []`, the walks as list functions, the textual-unchanged list,
   `Step` 128, BridgeSet 1–89 byte-identical (the file's diff is exactly two hunks: the RE-PIN 5 header note and rows
   90–107 appended), required list 110 → 144, what a re-pin touches (F1 adds one clause). Design-hygiene-arc and
   reasoning-surface-plan amendment notes: accurate (G-C3 narrowed to `Cont := List Frame` only, 33 names). Handoff:
   honest — the loaded first-run numbers are disclosed and superseded; the two removed costs are proof-local and
   verified in the diff (`case140`/`case155` direct close; `stepFn_next_frame` as `rfl`). `maxHeartbeats`/`maxRecDepth`:
   59 `set_option` lines at both commits, identical values, line offsets only.
7. **Gate.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `fffa3212` under the lock (audit worktree, dirty
   only by this note and its evidence dir): **EXIT 1 on exactly the 5a pair** — `FAIL certificate provenance`
   (`certification: STALE certification: changed dependency build/files/GoLean/GoCore/BridgeSet.lean`) and `FAIL
   baseline diff` with the ONE drift line `imported-goose/channel/google-search baseline[PASS/membership] ->
   now[FAIL/membership]` (the certified row fails on its stale certificate, not on its enumeration — attack 1(b)
   reproduced its certified set and statistics with the candidate binary). `differential coverage summary: cases=3791
   pass=3553 fail=238` = the baseline's 3554 / 237 plus that line; `git diff main -- baselines` EMPTY. Every other step
   ok: core build warning-free; core totality audit `50 GoLean modules … 144 required theorems present; 18622
   declarations … classical trio only` (its five poison controls rejected by name); frontend pins ok (hidden-dep-order,
   twin wire `0b58402a7699…`, 61 stdlib files); eval tests 298 ok; negative baseline diff matched (394; noted DIRTY
   because of this note). CI total wall 942 s. Reconciler (report-only): C9 HIGH = the same certificate staleness;
   C13 MEDIUM = pre-existing doc Go-version sites. Tail: `ci-diff-tail.txt`. This is the train's 5a business
   (`scripts/build-certified` + `release-check` + `ci --slow` at the merged tip), as the lane and the brief say.

## What I could not verify
- The lane's elaboration numbers on a QUIET box: this is a shared machine (other projects' `lean`/`cerberus`/`sc_run`
  jobs; load 6–22 during my runs). The A/B interleaving controls for that; absolute times are not comparable to the
  lane's load-5 runs.
- The customer's actual re-pin: the logic repo is pinned at `61958f2e` (pre-P — its `Agrees.frame` still carries the
  `wrapper` slot), so «their patterns keep elaborating through the abbrevs» is argued from the in-repo `Step`/`stepFn`
  (unchanged text, 128 rules) and their sources, not by building their tree.
- `#print axioms` was run as a sweep over the seven touched modules plus the gate's whole-closure audit, not as a
  per-theorem printout of all 4110 theorems.
