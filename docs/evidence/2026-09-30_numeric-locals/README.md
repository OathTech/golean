# B6 (numeric locals, `VarId := Nat`) — evidence

[AGENT worker], lane `core/numeric-locals-0930`, 2026-09-30. Fork base `main` @ `131a7313`; the runtime commit is
`0fb43dcd` (every run below is at it; the later lane commit is records only). Scratch under the worktree's `.tmp/`
(deleted at the end); every build/gate `scripts/capped`, under the box-wide lock (taken 05:12Z after the train r56
coordinator released it; never taken over; released at the lane's end).

## Acceptance

1. **Gate.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `0fb43dcd`: EXIT 1, `RESULT: FAIL` on exactly
   the 5a pair — `certificate provenance` (STALE: changed dependency files, the train's 5a business; reconciler C9
   names `build/files/GoLean/GoCore.lean`) and `baseline diff` with the ONE drift line
   `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the certified slow-tier
   row; the same line packet C and r55 reported). Every other step ok, incl. core build warning-free, core totality
   audit (153 required theorems), memory-module call sites, wire boundary (11 B6 controls + the v2-schema control),
   unseq scheduler/wire (56 mutants), frontend pins (twin = the re-pinned bytes), eval tests (298 ok), frontend unit
   tests, negative baseline. `differential coverage summary: cases=3791 pass=3553 fail=238` = the baseline's 3554 /
   237 with the google-search line. NO `baselines/native-full.tsv` edit; under `baselines/` only the twin pin moved.
   CI total wall seconds 1018. Tail: `ci-slow-tail.txt`.
2. **Choice trace, byte-identical.** Pre = `.tmp/pre-b6` (a detached checkout at `131a7313`, `lake build golean`
   there — lake judged the primary's binary current), post = the lane's binary; both
   `scripts/choice-trace-corpus --dump --jobs 6 --golean <bin> --out <relative dir>` with the same two exclusions
   (`goroutines/send-then-spin`, `strings/trimspace-repeat/repeat-bound-refused`); each side lowers the corpus with
   ITS OWN frontend (v2 vs v3 wires), so the comparison is of the machine's consumption dumps and results. 3755 rows
   exported on both sides, the same 34 frontend refusals, 2 exclusions. All 30 tsv files identical modulo the `--out`
   path (6 `dump-*.tsv` = 26417 rows, concatenated sha256 `1d621c3a…` on both sides; 6 `results-*.tsv`; manifest,
   batch, excluded, export-fail, exhausted-*); `summary.txt` identical except the absolute path inside the one
   pre-existing BUG-078 ERROR line. Summary: `choice-trace.txt`. (A first pre attempt with an ABSOLUTE `--out` ran no
   rows: the tracer joins the checkout's cwd with the out path — recorded, superseded.)
3. **Twin re-pin.** `baselines/pins/twin-chdriver.wire.json` 0b58402a… → 8a158eff… (`check-frontend-pins` ok at the
   lane tip; the history line is in the script). The written reason: `twin-diff.txt` — key by key identical after
   removing the B6 additions except 49 unnamed receivers/parameters whose empty spelling became `$recv`/`$p{i}`;
   +12641 `local`, +60 `keyLocal`, +66 `valLocal`, 924 tables / 2879 entries.
4. **The certified slow-tier row's wire** (the coordinator's wire-hash step at the train, r55 precedent):
   `google-search-wire-diff.txt` — dc232a8c… (= the record's `claim.wire_sha256`) → f448d579…; zero residual diff
   beyond the B6 fields (+51 `local`, +1 `valLocal`, 8 tables / 18 entries).
5. **Frontend+decode smoke over the corpus** (new frontend, new decoder, every `Corpus/**/main.go`): 1782 fixtures —
   1353 decode+run OK, 428 frontend-side refusals (394 `coverage/negative`, 25 `coverage/exec`, 9 `challenges/
   cedar-go`; main's frontend refuses the same 34 non-negative ones), 1 decoder refusal = the pre-existing BUG-078
   materialization-budget row; ZERO B6 refusals — no go/types-vs-lexical scoping disagreement anywhere in the
   corpus. Summary: `smoke.txt`.
6. **Theorems.** Every existing theorem and the packet A/B statements proved AS STATED; BridgeSet rows 1–107
   byte-identical (`git diff 131a7313 -- GoLean/GoCore/BridgeSet.lean` touches the header note and rows 108–125
   only); no `sorry`/axiom/`native_decide` (escape-hatch preflight ok); no `partial` in `GoLean/GoCore/`.

## Elaboration (the C3 1.5× stop rule)

A/B interleaved on the same box (pre = `.tmp/pre-b6`, post = the lane tree), `lake env lean -Dprofiler=true
-Dprofiler.threshold=100` wall/cpu per module (StepFn, Machine, MachineEqb, BridgeSet, StateWf, MachineSound,
StepErrors): `elaboration.txt`; the verdict is in the handoff §2.6.

## Fix round (2026-09-30; the audit's F1–F5; runtime commit = the fix-round commit on top of `79b48a2e`, rebased onto `main` @ `90df0fe1`)

7. **Gate.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` on the fix-round tree: EXIT 1, `RESULT: FAIL` on
   exactly the 5a pair (certificate provenance STALE; the one `google-search` drift line), `cases=3791 pass=3553
   fail=238` = the pin with that row; every other step ok — wire boundary now 16 B6 controls (M1/M6/M13/M14-format/M16
   added), unseq scheduler (the three re-pointed rows refused at ENTER by name), unseq wire (56 mutants; 141 fixtures
   byte-identical to the generator after the prune pass — nothing was orphaned), core audit (158 required), frontend
   pins (twin unchanged), eval 298, Go tests. Wall 890 s. Tail: `ci-diff-fix-tail.txt`.
8. **Trace.** POST re-run with the fix-round binary; compared against the FIRST round's recorded digest (its pre and
   post were identical: 26417 dump rows, concatenated sha256 `1d621c3a…`; those scratch outputs were deleted at the
   first round's end, so this is a digest comparison, not a file diff): IDENTICAL — 6 dump files, 26417 rows, concatenated sha256 `1d621c3a099e525d…`; the same 3755 rows exported, the same 34 frontend refusals, 2 exclusions. `choice-trace.txt`..
9. **Smoke.** 1782 fixtures with the strengthened decoder: 1353 OK, 428 frontend refusals (unchanged), 1 BUG-078
   row; the id-level ENTRY check fires on 0 of 1354 decoded wires (`smoke.txt`).
