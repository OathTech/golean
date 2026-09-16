# Stage B — the `unseq` scheduler on hand-built graphs: gate lines and first budgets (2026-09-16)

[AGENT] Evidence for lane `core/unseq-scheduler-b-0916` (branch of the same
name, base main `32398203`); design of record
`docs/2026-09-16_evaluation-order-model-v2.md` (v2.1) §3/§7 row B; the lane
handoff is `docs/2026-09-16_unseq-stage-b-handoff.md`. Records only: small
gate tails, the reference-set table and the budget numbers — every number
below is copied from the named log under the lane worktree's `.tmp/`
(untracked; the commands to regenerate are given). Nothing here is a
differential claim about Go: the reference sets are the v2.1 spike's
(`docs/evidence/2026-09-16_eval-order-v2-spike/outcomes.txt`), reproduced
by the MACHINE on hand-built graphs — check (a) «reference graph checks
pass» for the machine; check (b) «machine equals reference over the wire»
remains Stage C's.

- Toolchain: Lean `leanprover/lean4:v4.32.2` (repo pin); `go1.26.5` (= `baselines/go-oracle-pin`).
- Host: linux/amd64, 32 cores, 125 GiB; every lake/lean command through `scripts/capped` at `GOLEAN_MEM_MAX=32G`; full builds and gates under the box-wide build lock (`artifacts/build-lock.d`, owner file, trap-protected release).

## Gate lines (captured exit codes, never grepped greens)

| run | command | exit | wall s | SHA / tree | result |
|---|---|---|---|---|---|
| warm | `scripts/capped lake build` (plain copy of the primary's `.lake` at identical source `32398203`) | 0 | <1 (202 jobs, no-op) | `32398203` clean | the copy is current |
| gate 1 (core) | `scripts/capped scripts/ci --diff` (lock) | **1** | 1162 | `32398203` + the core tree (17 dirty files → commit `306fb3ef`) | 3676 rows 3427 PASS / 249 expected FAIL; 394 negatives; 211 eval tests; every step green EXCEPT the two EXPECTED 5a-class items: `certificate provenance` STALE («changed dependency build/files/GoLean/CLI.lean» — compiled semantic inputs changed) and, in consequence, the ONE cached certified row `imported-goose/channel/google-search` PASS→FAIL/membership (its cached record judged stale; NOT an observation change). No other row moved. Reconciler: C9 HIGH (the same stale certification) + C12 HIGH ×2 (the census mirrors lacked `unseqNext` — fixed in the next commit). |
| gate 2 (tests + wiring + records) | `scripts/capped scripts/ci --slow` (lock; `--slow` implies `--diff` and RE-CERTIFIES the tier=slow row) | **1** | 1306 | `306fb3ef` + the tests tree (11 dirty → commit `c770c59c`) | 3676 rows 3427 PASS / 249 expected FAIL; 394 negatives; 211 eval tests; the new `unseq-scheduler` step ok; every step green EXCEPT the same two EXPECTED 5a-class items: `certificate provenance` STALE and the cached certified row `imported-goose/channel/google-search`, whose `--slow` RE-ENUMERATION reports «Fresh certification: unchanged set; seconds=153.901» — the certified SET is IDENTICAL to the tracked record; the row is red only because the record's provenance (compiled inputs) is stale → the train's 5a records refresh (install the reviewed `certification-candidate.json`), NOT a finding, NOT a re-pin. No other row moved; reconciler: C9 (the same stale certification) + C13 (pre-existing, doc Go-version sites). C12 is green (the census mirrors carry `unseqNext`). |
| unseq gate step | `scripts/check-unseq-scheduler` (also a named `scripts/ci` step, `unseq-scheduler`) | 0 | (in gate 2) | same | 47 checks ok: every reference set exact, every refusal by name; audit: 24 required theorems, 14 376 declarations across all imported local origins, classical trio only |
| fix round: unseq gate step | `GOLEAN_MEM_MAX=32G scripts/capped scripts/check-unseq-scheduler` (standalone, after the sequential warm build of the six edited modules — every module EXIT=0: Unseq, Machine 4 s, StepFn 17 s incl. StateWf, MachineSound 57 s, UnseqSound) | **0** | 94 | `ba8767da` + the fix round's edits (before its runtime commit) | **64 checks ok** (47 + 17: F1 ×6 incl. the legitimate join, A8, A3, F2 ×3, F3 ×2, N3 ×2, R5 ×2), 0 FAIL; audit: 24 required theorems, 14 444 declarations, classical trio only — `fix-round-unseq-gate-tail.txt`; the literal refusal texts on the canonical tape: `fix-round-refusals.txt` |
| fix round: gate 3 (core + tests + records) | `scripts/capped scripts/ci --diff` (lock; `GOLEAN_MEM_MAX=32G`) | see `gate3-tail.txt` | see `gate3-tail.txt` | same tree | the tail INCLUDES THE DRIFT BLOCK (audit R6); expected red = exactly the two 5a-class items (`certificate provenance` STALE — compiled inputs changed; the one certified row `imported-goose/channel/google-search` for that reason) |

Gate 1's log tail (`.tmp/ci-1.log`, lines 898–949): the summary block lists
`FAIL certificate provenance` and `FAIL baseline diff (DRIFT — see above)`
with the single drift line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`;
everything else `ok`. The certificate-provenance step's own controls all
PASS (the STALE verdict is the intended one for changed compiled inputs).

## The reference sets, reproduced by the machine (check (a))

`Tests/UnseqScheduler.lean` builds every witness of `outcomes.txt` as a
hand-built `Stmt.unseq` graph and enumerates it over ALL tapes through the
EXISTING enumerator/driver path — `CLI.enumSetup` → `CLI.explore` (the
stepwise pool explorer with the machine's own consumption accountant and the
alias-ladder certification check), single tapes through `CLI.enumRunProgram`
— then compares the projected observations (status, int values, output,
panic-text substring) EXACTLY with the reference members. Figures from
`.tmp/check-unseq.log` (leaves = complete enumeration paths; sites = pick
positions branched; steps = machine steps across the tree, shared prefixes
counted once):

| witness | reference set | machine set | leaves | sites | steps | maxDepth |
|---|---|---|---|---|---|---|
| W1 `v := mut() + a` | {1, 2} | = | 8 | 6 | 334 | 3 |
| W2 `v := a[b[0]] + mut()` | {10, 30, 40} | = | 15 | 12 | 990 | 4 |
| W3 `a[i] += mut()` | {[11 20], [10 21]}; [10 11] absent | = | 10 | 8 | 704 | 4 |
| W4 `_ = a[1] + b[2]` both nil | {panic [1] len 0, panic [2] len 0} | = | 2 | 1 | 25 | 1 |
| W5 loop ×2 `println(a[0] + mut())` | {panic; "7" then panic}; no 2nd-iteration completion | = | 3 | 2 | 233 | 2 |
| W6 `v := x + inc() + inc()` | {0, 1, 2} | = | 15 | 12 | 977 | 4 |
| X1 `xs[ys[9]], b = zs[7], 2` | {panic [9] len 3, panic [7] len 3}; no store | = | 32 | 16 | 522 | 4 |
| X2 `b2i(z ‖ h()) + x`, z false / true | {2, 3} / {2} | = / = | 48 / 24 | 42 / 20 | 2779 / 1024 | 7 / 5 |
| X3 `x[f()] += <-ch` buffered (len(ch) read by a deferred println on the panic path) | {panic·len 0, panic·len 1} | = | 7 | 6 | 385 | 4 |
| X3e same, EMPTY channel | members {panic·len 0}; `blocked` a REFUSAL apart | `explore` refuses by name («deadlock member … fail loud»); the canonical tape gives the panic member | — | — | — | — |
| R1 `v := x + y + mut()` unreduced / REDUCED (negative) | {0,1,2,3} / {0,2,3} | = / = | 30 / 15 | 23 / 12 | 1418 / 770 | 4 / 4 |
| R2a `sink(z ‖ h(), k())` z true / false | {`k, result true 7`} / {`h, k, result true 7`} | = / = | 1 / 1 | 0 / 0 | 105 / 137 | 0 / 0 |
| R2a INVALID join (k value-depends on the skipped h) | refused by name | «value-depends on '$h', confined to a skipped region (no valid join)» | — | — | — | — |
| R2b `sink(left ‖ b, change())` E1 at COMPLETION / at ENTRY (refuted) | {false} / {false, true} | = / = | 1 / 3 | 0 / 2 | 111 / 235 | 0 / 2 |
| R2c `sink(g(), a ‖ (b && h()), k())` b true / false | {`g k`, `g h k`} / {`g k` ×2 results}; `h g k` absent | = / = | 2 / 2 | 1 / 1 | 297 / 265 | 1 / 1 |
| R4 `old := a; a[0] += mut()` (mut rebinds a) | {old [11 20] a [100 200], old [10 20] a [101 200]}; hybrids absent | = | 4 | 3 | 427 | 3 |
| R6 `v := a[f()]` SPLIT / FUSED | {10, 20} / {20} | = / = | 8 / 3 | 6 / 2 | 371 / 168 | 3 / 2 |
| C1 `f(g())` / C2 `sink(a)` / C3 `sink(a, mut())` | {8} / {3} / {1, 2} | = | 1 / 1 / 8 | 0 / 0 / 6 | 109 / 61 / 487 | 0 / 0 / 3 |
| C4 cycle A↔B | refused by name | «pending active work with no ready occurrence» | — | — | — | — |
| target: pointer redirection | {x 11 y 100, x 10 y 101} | = | 4 | 3 | 277 | 3 |
| target: cell mutation at a stable address | {a 11, a 101} | = | 4 | 3 | 289 | 3 |
| target: frozen MAP-element plan | Stage E | refused by name («frozen map-element plan (Stage E)») | — | — | — | — |
| recursion `sum(n) = g(n) + sum(n-1)` in a sweep | {10} (per-activation cells) | = | 10 000 | 9 414 | 889 276 | 16 |
| replay graph (three unordered printing events) | 6 orders | = ; each order reproduced by its RANK tape | 6 | 4 | 480 | 2 |
| singleton picks (C1 with tape [5,6]; C2 with [7]) | tape untouched | leftover [5,6] / [7] | — | — | — | — |
| malformed: unknown slot / duplicate result / sort mismatch ×2 / unknown reference / unproduced cell | refused by name at ENTER | six named refusals | — | — | — | — |

## First budgets (v2.1 §3.5–3.6 route β: the default DFS explorer, RECORDED)

A loop of N sweeps, each with ONE wide pick (two unordered invocations),
enumerated by `CLI.explore` (fuel 2 000 000, width 8, sites 64, cap 4096,
work cap 50 000 000). Regenerate: `scripts/capped lake env lean --run
<Budget.lean> N [quiet]` under `/usr/bin/time -v` (the driver text is in
the handoff's evidence appendix; it is scratch, not a trusted driver — it
only calls `CLI.enumSetup`/`CLI.explore`). Wall is in-process (`IO.monoMsNow`
around `explore`); `time -v` wall includes Lean start-up (~0.3 s) and olean
loading; RSS is dominated by the loaded oleans (~750 MB), the DFS itself is
in the noise. Measured concurrently with gate 2's early steps on the shared
box (single-threaded runs; wall numbers indicative, not paired).

Printing events (every order a DISTINCT observation — members = paths):

| N | members | leaves (paths) | sites | steps | probes | maxDepth | wall ms (explore) | time -v wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 2 | 2 | 1 | 205 | 3 | 1 | 5 | 0:00.31 | 754 112 |
| 2 | 4 | 4 | 3 | 539 | 9 | 2 | 17 | 0:00.32 | 756 612 |
| 3 | 8 | 8 | 7 | 1 207 | 21 | 3 | 42 | 0:00.36 | 759 664 |
| 4 | 16 | 16 | 15 | 2 543 | 45 | 4 | 108 | 0:00.41 | 755 780 |
| 5 | 32 | 32 | 31 | 5 215 | 93 | 5 | 266 | 0:00.58 | 760 248 |
| 6 | 64 | 64 | 63 | 10 559 | 189 | 6 | 663 | 0:01.00 | 758 564 |
| 7 | 128 | 128 | 127 | 21 247 | 381 | 7 | 1 410 | 0:01.76 | 762 584 |
| 8 | 256 | 256 | 255 | 42 623 | 765 | 8 | 3 080 | 0:03.37 | 760 952 |

SILENT events (no observable effect: every order the SAME outcome — the
outcome-equivalent product review R5 names; members stay 1 while paths
double):

| N | members | leaves (paths) | sites | steps | probes | maxDepth | wall ms (explore) | time -v wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 2 | 1 | 181 | 3 | 1 | 5 | 0:00.30 | 755 448 |
| 2 | 1 | 4 | 3 | 467 | 9 | 2 | 14 | 0:00.33 | 758 752 |
| 3 | 1 | 8 | 7 | 1 039 | 21 | 3 | 38 | 0:00.36 | 759 420 |
| 4 | 1 | 16 | 15 | 2 183 | 45 | 4 | 93 | 0:00.41 | 759 216 |
| 5 | 1 | 32 | 31 | 4 471 | 93 | 5 | 224 | 0:00.55 | 758 020 |
| 6 | 1 | 64 | 63 | 9 047 | 189 | 6 | 520 | 0:00.81 | 760 404 |
| 7 | 1 | 128 | 127 | 18 199 | 381 | 7 | 1 299 | 0:01.64 | 759 564 |
| 8 | 1 | 256 | 255 | 36 503 | 765 | 8 | 2 778 | 0:03.09 | 763 692 |

Reading: paths = 2^N exactly (one wide pick of width 2 per sweep, no other
consumption); steps ≈ 2^N × 165 (silent) — a full replay per path (the DFS
shares prefixes, not states); wall doubles per N (~11 ms per path at N=8).
UNIQUE STATES are not measured: the stepwise explorer has no state
identity; that metric belongs to route α (the certified dedup engine),
which Stage B does NOT extend — the engine REJECTS every `unseq` pick
position by name today (`GoLean/GoCore/EnumDedupCheck.lean` `innerVecs` →
`none` at `consumesUnseqNext`; `GoLean/GoCore/MultiStreams.lean`
`poolThreadOblivious` → `false`; `GoLean/EnumDedup.lean` `refusalReason`
names «unseq scheduler pick (unseqNext, … route α … is owed before Stage
E; use the default enumerator)»). The recursion witness above (4 nested
activations, three-way-unordered sweeps) is the same product on a real
shape: 10 000 leaves for a singleton outcome. Stage D's ladder starts
here; N3 (budget refusal) stays PENDING [USER].

## Audit fix round (2026-09-16)

The adversarial audit (`docs/2026-09-16_unseq-stage-b-audit.md`, branch
`review/unseq-stage-b-0916` @ `2440278d`) returned FIX-FIRST; the fix round
is the lane handoff's §9 (F1–F3 as named machine refusals, N3, R1–R6, N2
owed). Records corrections that touch THIS file: the rule inventory is TEN
`Step` rules (audit R3 — «eleven» counted the legacy `unseqProbe`); the gate
tails of record now include the drift block (audit R6: `gate3-tail.txt` —
`gate1-tail.txt`/`gate2-tail.txt` carry the summary block only, their drift
line is quoted in the gate-1 paragraph above and was independently
reproduced by the audit's own `ci --diff`, `ci-diff-drift.txt` on the review
branch). Files added: `fix-round-unseq-gate-tail.txt` (the 17 new checks +
the R4/target-identity lines + the audit line), `fix-round-refusals.txt`
(the literal F1/F2/F3/N3/A3 texts), `gate3-tail.txt` (summary + drift
block + exit/seconds of the fix round's `ci --diff`).

## Regeneration

    scripts/capped scripts/ci --diff                 # gate 1's shape (lock)
    scripts/capped scripts/ci --slow                 # gate 2's shape (lock; re-certifies the slow row)
    scripts/capped scripts/check-unseq-scheduler     # the lane's named step

## Merge train r36 — the 5a record (2026-09-16, [AGENT] coordinator)

[USER] Mike 2026-09-16, verbatim (relayed): «Great, let's land it as you propose». Pre-merge main
`32398203` → `refs/snapshots/r36/main`; Stage B `29a34663` fast-forwarded; the audit branch rebased
(`6793943c`) and fast-forwarded. Under the box-wide lock at `6793943c`:

| step | result |
|---|---|
| `scripts/build-certified` | EXIT=0, 116 s — compiled inputs match; `golean` sha256 `0dec9436e1c8a6b0…` |
| `release-check --base refs/snapshots/r36/main` | EXIT=2 (EXPECTED) — «STALE certification: changed dependency build/files/GoLean/CLI.lean» (the Stage B core files are certification inputs) |
| `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` | EXIT=1, 1336 s — red on EXACTLY the two 5a items: `FAIL certificate provenance` (stale) and `FAIL baseline diff` whose DRIFT block is the single line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the stale record); 3676 rows otherwise unchanged; negatives 394 no regression; `unseq scheduler (Stage B)` step ok; `RESULT: FAIL` for those two reasons only. Step-line tail incl. the drift block: `r36-ci-slow.tail.txt` |
| candidate vs tracked record | `claim` and `observations` (the six members) IDENTICAL; `inputs` differ exactly in the Stage B files (`State/Machine/StepFn/StateWf/MachineSound/Syntax*/Unseq*/EnumDedup*/MultiStreams/Race/AdmissionIndices/MachineEqb/GoCore.lean`, `CLI/ChoiceTrace/EnumDedup.lean`, `lakefile.toml`, `scripts/ci`, `scripts/ci-libraries.json`, `scripts/check-unseq-scheduler`) and the receipt (binary `0dec9436…`, source_commit `6793943c`, clean tree) — INSTALLED as `baselines/certified/imported-goose__channel__google-search.certified.json` in this commit; a provenance refresh, not a re-pin and not a finding |

The lane's own gates (tails `gate1-3`) ran on the dirty tree just before each commit; this train's run at the committed merged tip is the tail of record. No runtime file is touched by this commit.

**Green re-run at the records commit `7741464c`** ([AGENT] coordinator, 2026-09-16): a fast `scripts/ci`
first went RED on `baseline diff` — it re-reads the `--slow` run's recorded `latest.tsv`, in which the
certified row was FAIL because its record was stale AT RUN TIME (provenance itself was already green) —
so the green re-run is the full differential: `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at
`7741464c`, EXIT=0, `RESULT: PASS`, `baseline diff FULL (3676/3676, no regression)`, `certificate
provenance` ok, negatives 394 no regression. Lesson for every 5a train: after installing the candidate,
re-run `ci --diff`, not fast `ci`.
