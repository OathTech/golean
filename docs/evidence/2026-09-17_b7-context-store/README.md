# B7 fixed context / mutable store — gate lines, census and measurements (2026-09-17)

[AGENT] Evidence for lane `core/b7-context-store-0917` (branch of the same
name, base main `7f1c1fe7`); the brief is `docs/2026-09-16_b7-context-store-charter.md`
(§7 slices, §8 exit evidence), the lane handoff is
`docs/2026-09-17_b7-context-store-handoff.md`. Records only: small gate
tails, the hypothesis census, the positional-tag probe and the one warm
measurement every estimate is conditional on. Every number below is copied
from the named log under the lane worktree's `.tmp/` (untracked; the commands
to regenerate are given, repo-relative). Nothing here is a differential
claim about Go: B7 claims NO fidelity progress (zero corpus rows move, or the
slice stops).

- Toolchain: Lean `leanprover/lean4:v4.32.2` (repo pin `lean-toolchain`); `go1.26.5` (= `baselines/go-oracle-pin`).
- Host: linux/amd64, 32 cores, 125 GiB; every lake/lean command through `scripts/capped`;
  explicit-target builds at `GOLEAN_MEM_MAX=32G` while the coordinator's train held the
  box-wide lock (`artifacts/build-lock.d` in the primary, a live `scripts/ci --diff` at 48G
  concurrently — timing numbers below were taken under that load).
- Provenance: [AGENT] = this lane's executor; [USER] rulings are cited verbatim as relayed
  from `docs/2026-08-31_qrow-rulings.md` («The B7 charter rulings record (2026-09-16)»).

## S0 — census, probe, reverse-import map, warm measurement (records only)

### The hypothesis census BEFORE (the payoff to be counted gone by type)

Recorded greps at `7f1c1fe7` (`GoLean/` unchanged from `9e690c2e`):

| site class | file | count | command |
|---|---|---|---|
| field-equality conjuncts in theorem STATEMENTS (`σ'.types = σ.types`, `.functions`, `.methods`) | `GoLean/GoCore/StateWf.lean` | **38** on 24 statement lines (39 atoms on 25 lines incl. the one `have` at `:5709`) | `grep -n "\.types = " GoLean/GoCore/StateWf.lean` (25 lines), atoms summed per line |
| the same, any occurrence (statements + proof-internal) | `GoLean/GoCore/StateWf.lean` | 54 atoms | `grep -oE "\.(types\|functions\|methods\|methodSets\|typeDisplays) = [a-zA-Zσ₀-₉']+\.(types\|functions\|methods\|methodSets\|typeDisplays)" … \| wc -l` |
| `s'.types = s.types` conjuncts | `GoLean/GoCore/MultiWfSound.lean` | **6** (`:102 :146 :172 :195 :641 :1086`) | `grep -n "\.types = " GoLean/GoCore/MultiWfSound.lean` |
| `htypes : σ₂.types = σ₁.types` hypotheses | `GoLean/GoCore/MachineSound.lean` | **4** (`:1475 :1485 :1991 :2149`; 11 mentions incl. uses) | `grep -n "htypes" GoLean/GoCore/MachineSound.lean` |
| **total statement sites** | | **48** (= the charter §1's 38 + 6 + 4) | |
| `SameContext` / `Extension.context` | (parked family, D3) | 0 in the tree — left with `docs/2026-09-16_typed-profiles-parked.md` | `grep -rn SameContext GoLean Tests` → none |

### The reverse-import map of `ExecState`'s five context fields (reads per file, `\.field\b`)

`for f in GoLean/GoCore/*.lean GoLean/*.lean Tests/*.lean; do grep -oE "\.types\b" …; done` — counts of
`.types`/`.functions`/`.methods`/`.methodSets`/`.typeDisplays` mentions (state reads AND
`Program.*`/`MethodInfo.*` reads share the spelling; the per-file split is the census the charter
§7 S0 asked for — `Ops.lean` 24/4/4/1/1, `Machine.lean` 6/1/0/0/0, `StepFn.lean` 0/1/1/1/1,
`Race.lean` 0/2/0/0/0 — matching the charter's numbers exactly):

| file | types | functions | methods | methodSets | typeDisplays |
|---|---|---|---|---|---|
| `GoLean/GoCore/Ops.lean` | 24 | 4 | 4 | 1 | 1 |
| `GoLean/GoCore/Machine.lean` | 6 | 1 | 0 | 0 | 0 |
| `GoLean/GoCore/StepFn.lean` | 0 | 1 | 1 | 1 | 1 |
| `GoLean/GoCore/Race.lean` | 0 | 2 | 0 | 0 | 0 |
| `GoLean/GoCore/Multi.lean` | 1 | 0 | 0 | 0 | 0 |
| `GoLean/GoCore/StateWf.lean` | 61 | 41 | 26 | 0 | 0 |
| `GoLean/GoCore/MachineSound.lean` | 14 | 0 | 0 | 0 | 0 |
| `GoLean/GoCore/MultiWfSound.lean` | 40 | 0 | 0 | 0 | 0 |
| `GoLean/GoCore/MachineEqb.lean` | 2 | 2 | 2 | 2 | 2 |
| `GoLean/GoCore/AdmissionIndices.lean` / `AdmissionPolicy.lean` | 0 | 0 | 1 / 2 | 0 | 0 |
| `GoLean/GoCore/Syntax.lean` | 0 | 0 | 0 | 0 | 1 |
| `GoLean/CLI.lean` | 4 | 0 | 1 | 1 | 1 |
| `GoLean/ChoiceTrace.lean` | 0 | 2 | 1 | 0 | 0 |
| `GoLean/NativeToIR.lean` (decoder: `Program.*` construction, UNTOUCHED) | 10 | 0 | 5 | 8 | 0 |
| `GoLean/NativeDeclaration.lean` | 0 | 0 | 2 | 0 | 0 |
| `Tests/GoCoreEval.lean` | 2 | 0 | 1 | 1 | 4 |
| `Tests/MethodIdentity.lean` | 5 | 0 | 10 | 0 | 0 |

`ExecState` mentions per file (the re-typing surface): StateWf 142, MachineSound 163, Machine 113,
Ops 55, Multi 45, MultiSound 44, StepFn 38, MultiStreams 22, State 17, MultiWfSound 15, NPDRF 12,
ChoiceTrace 12, EnumDedupSound 9, StringPanic 9, Race 7, UnseqSound 7, CLI 7, MachineEqb 6,
AbortObservation 4, EnumDedupCheck 3, Trace 2, PoolTrace 2, Platform 2 (docstring), EnumSpec 1,
EnumDedup 1, Syntax 1 (docstring); Tests: GoCoreEval 16, GoCoreContract 15, MethodIdentity 2,
PanicRendering 1, StringPanicMembers 1. Modules with ZERO mentions (untouched by re-typing):
`Syntax`, `Value`, `Platform` (body), `FloatBits`, `Unseq`, `Declaration`, `PanicText`,
`Admission*`, `SyntaxEqb`, `ProgramTrace`, `NativeToIR`, `NativeDeclaration`, `StrictJson*`.

### The positional-tag probe (`fun_cases stepFn s c ch` at this tip)

`probe_s0.lean.txt` (scratch; `sorry`-free; run as
`GOLEAN_MEM_MAX=32G scripts/capped lake env lean .tmp/probe_s0.lean`, EXIT=0, 2 s):
**162 goals**, tags `case1` … `case162` in order; `fun_cases-tags-before.txt` records, per arm,
the tag, the hypothesis count and the type prefix of the last hypothesis as a fingerprint.
The S2 re-run (`fun_cases stepFn ctx s c ch`) must give the same 162 tags in the same order with
every fingerprint unchanged (hypothesis counts +1 for `ctx`) — the charter's «0 positional tags
expected to move»; the named tags in `MachineSound.lean` today: `stepFn_sound` 66 tags,
`stepFn_consumption_none` 44, `stepFn_consumption_some` 15 (the `awk` over `case case[0-9]+`).

### The MEASURED warm rebuild after a `State.lean` touch (the number every estimate is conditional on)

The touch: the three-line B7 pointer comment at `State.lean:71-73` (kept by S1, so the rebuild it
triggers is S1's first, not a throwaway). Command, repo root of the lane worktree, with the parked
worktree's `.lake` copied in as the warm base (`cp -a …/park-typed-profiles/.lake .lake`; its Lean
sources are byte-identical to `7f1c1fe7`'s — `git diff <park HEAD> HEAD -- GoLean Tests lakefile.toml
lake-manifest.json lean-toolchain` empty; the no-op `scripts/capped lake build GoLean.GoCore` before
the touch: EXIT=0, 0 s, «31 jobs»):

```
LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.GoCore   # .tmp/warm-s0-measure.log
S0 WARM MEASURE: lake build GoLean.GoCore after State.lean touch EXIT=0 (104 s) LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G
✔ [31/31] Built GoLean.GoCore (159ms)   — 20 modules rebuilt (every module above State in the GoCore closure)
```

**104 s** wall (under the train's concurrent 48G `ci --diff`; `LEAN_NUM_THREADS=4` = `scripts/ci`'s
scaling for a 32G cap). Against the charter §7's conditional: ≤ 15 min → S1–S3 fit one session.
The charter's «≤ 15 min» threshold is met by a factor of ~8.5.

### The lock state at S0

`artifacts/build-lock.d/owner` in the primary: `coordinator train r38 pid 1900555 …` — the recorded
pid was gone but a live `scripts/ci --diff` (pids 3539893/3539909, 48G) was running under it; S0 ran
ONLY explicit-target builds at ≤ 32 GiB (the no-op check, the probe, the measurement).

## S2 — the positional-tag probe AFTER (`fun_cases stepFn ctx s c ch`)

`probe_s2.lean.txt` (the S0 probe with the context parameter; run the same way, EXIT=0, 2 s):
**162 goals**, `case1` … `case162` — `diff` of the tag/order columns against
`fun_cases-tags-before.txt`: IDENTICAL; `diff` of the last-hypothesis fingerprints: IDENTICAL;
the hypothesis-count delta is exactly +1 on all 162 arms (the `ctx`). **0 positional tags
moved**; `stepFn_sound` (66 named tags), `stepFn_consumption_none` (44), `stepFn_consumption_some`
(15) needed no renumbering. Commands (repo root of the lane worktree):

```
GOLEAN_MEM_MAX=32G scripts/capped lake env lean .tmp/probe_s2.lean > .tmp/probe_s2.log 2>&1   # EXIT=0
diff <(awk '{print $2,$3}' fun_cases-tags-before.txt) <(awk '{print $2,$3}' fun_cases-tags-after-s2.txt)          # empty
diff <(sed 's/hyps=[0-9]* //' fun_cases-tags-before.txt) <(sed 's/hyps=[0-9]* //' fun_cases-tags-after-s2.txt)  # empty
```

## The hypothesis census AFTER (the payoff, counted at the gate tip)

The S0 greps re-run on the assembled tree:

| site class | BEFORE | AFTER |
|---|---|---|
| field-equality atoms `\.(types\|functions\|methods\|methodSets\|typeDisplays) = …` in `StateWf.lean` | 54 (38 in statements) | **0** |
| the same in `MultiWfSound.lean` | 6 | **0** |
| `htypes` in `MachineSound.lean` | 4 hypotheses (11 mentions) | **0** hypotheses (1 mention, a tombstone comment) |
| `ExecState` in code (`GoLean/`, `Tests/`) | **31 files** (29 with CODE mentions; `Platform.lean`, `Syntax.lean` docstring-only) — `git grep -l ExecState 5955e55f -- GoLean Tests \| wc -l`; «30 modules» was wrong (audit F3, corrected 2026-09-17) | **0** code mentions (**10** prose lines in 7 files name the historical type — `MachineEqb`, `ProgramCtx`, `State`, `StepFn`, `Store`, `Tests/GoCoreContract`, `Tests/GoCoreEval`; «5 docstring mentions» undercounted) |
| `itersNormalized` in `MachineWf` | 1 conjunct | **0** (D6); the pool's `ThreadWf`/`MultiWf` twin: 1 conjunct at the first gate → **0** in the fix round (`1fafc9f2`, [USER] 2026-09-17 relayed) |
| `itersNormalized` LINES in `GoLean/` (the predicate family) — ONE spelling, one derivation (audit F4: the count had been spelled 199/198/196/195; corrected 2026-09-17) | **198 lines** (StateWf 104, MultiWfSound 92, Multi 1, MachineSound 1 comment) — derivation: `git grep -c itersNormalized 5955e55f -- GoLean`, the four per-file counts summed | **13 lines, ALL prose** after the fix round (tombstone comments and docstrings; `git grep -n itersNormalized HEAD -- GoLean` = 13, none a code line) ⇒ **0 code lines** |

The runtime commit's delta (**CORRECTED**, audit F2, 2026-09-17): `git diff --stat 66fe1092..73ad798d --
GoLean Tests` = **34 files, +3,232/−2,862** (pre-rebase `git diff --stat 7f1c1fe7 2500b434 -- GoLean Tests`
is identical). The «32 files, +3,058/−2,862» carried here and in the handoff §1 until now was wrong by two
files (the docstring-only `Platform.lean`, `Syntax.lean`) and 174 insertions; the −2,862 was right. The fix
round adds 4 files, +213/−538; the audit fix round 2 files, +5/−42. `NativeToIR.lean`,
`tools/nativefrontend/`, `scripts/check-frontend-pins` untouched (wire-neutral by construction).

## Explicit-target warms during the build (captured `EXIT=`, wall s)

Every build through `scripts/capped` at `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G` (the box lock held
only for the full default build and the gate). These are REPRESENTATIVE lines, not one line per warm:
the charter §8 asked for a line per explicit-target warm, and the dozens of compiler-guided re-index
rounds inside S1/S3 (five in `StateWf.lean` at 8–12 s, two in `MultiWfSound.lean` at 57–77 s) are
summarised rather than listed (audit F10; the fix round and the audit fix round below DO carry their
complete per-module sets). Every number reported carries its captured `EXIT=`; none is a grepped green.
Representative lines from the lane's `.tmp/`:
Store+ProgramCtx 0 s (S1); Ops 5 s; Machine 4 s; StateWf 16 s (after five fix rounds of 8–12 s);
StepFn 1 s; MachineSound+UnseqSound 62 s (after 57–77 s rounds); `lake build GoLean.GoCore` 7 s at
the last round (33 jobs; earlier rounds 2–11 s); the trace/observer trio 2 s; default `lake build`
(lib + exe) 4 s at the last round (96 jobs); `Tests.GoCoreEval` 144 s; all `Tests.*` 30 s.

## Rebase map (2026-09-17, before the fix round)

Rebased onto main `5955e55f` (one records-only commit): `fc1aa228 → 66fe1092`, `2500b434 → 73ad798d`,
`b1b25945 → a7fd0542`; Lean tree byte-identical across the rebase (`git diff 2500b434 73ad798d -- GoLean
Tests lakefile.toml lake-manifest.json lean-toolchain` empty); the warm `.lake` was reused (no-op
`lake build GoLean.GoCore` EXIT=0, 0 s). The pre-rebase SHAs in the rows above name the same trees.

## Fix round (2026-09-17) — explicit-target warms (captured `EXIT=`, wall s; `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G`)

`.tmp/fix-warm.lines`: `GoLean.GoCore.StateWf` EXIT=0 (19 s) · `GoLean.GoCore.Multi` EXIT=0 (5 s) ·
`GoLean.GoCore.MultiWfSound` EXIT=0 (76 s) · `GoLean.GoCore` EXIT=0 (16 s, 33 jobs) — first round, 0
warnings in every log.

## Gate lines (captured exit codes, never grepped greens)

| run | command | exit | wall s | SHA / tree | result |
|---|---|---|---|---|---|
| THE gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` (box lock; `LEAN_NUM_THREADS=4` by the cap) | **1** | 1068 — **from the lane's log, tail NOT tracked** (audit F5: `gate-tail.txt` ends at `RESULT: FAIL`, no «CI total wall seconds» line; the RESULT/step/drift lines it does carry match this row) | `fc1aa228` + the runtime tree, committed unchanged as `2500b434` | 3676 cases 3427 PASS / 249 expected FAIL; 394 negatives; eval 211/0; every step ok EXCEPT the two EXPECTED 5a-class items — `certificate provenance` STALE (C9: compiled inputs `build/files/GoLean/CLI.lean` changed) and the ONE cached certified row `imported-goose/channel/google-search` PASS→FAIL/membership (its cached record judged stale; NOT an observation change). No other row moved. `gate-tail.txt` has the differential summary, the drift block, the reconciler lines and the step list verbatim. |
| choice trace | `scripts/choice-trace-corpus --dump --jobs 6 --out <dir> --golean <bin> --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused` for main's binary (cold-built from `git archive 7f1c1fe7` under `.tmp/before/`) and for `2500b434`'s; sorted `dump-*.tsv` compared with `cmp` | **0 (cmp)**: BYTE-IDENTICAL — 23,679 consumption records from 21,834 (row, stream) lines over 3,639 traced rows (34 frontend refusals, 2 excluded), sha256 `5f901024…58b5a` on both sides; validator summaries identical (0 menu-invariant violations, 0 self-check alarms, 0 driver-agreement mismatches; the one ERROR row is the known frontend refusal `arrays/materialization-budget/over-budget`); each tracer run EXIT=1 (643 s) for the SAME pre-existing «FINDINGS present» depth listing. `choice-trace-summary.txt` | 643 + 643 | main `7f1c1fe7` vs `2500b434` | the whole-corpus choice trace is byte-identical (D5 (a)'s second leg) |

| THE gate, FIX ROUND | the same command under the box lock (`artifacts/build-lock.d` taken 03:38:41, released 03:54:15; owner file; trap-protected) | **1** | 934 | `a7fd0542` + the runtime tree (four core files), committed unchanged as `1fafc9f2` | 3676 cases 3427 PASS / 249 expected FAIL; 394 negatives; eval 211/0; `core build (warning-free)` ok; `core totality audit` ok; every step ok EXCEPT the same two EXPECTED 5a-class items — `certificate provenance` STALE (C9: compiled inputs `build/files/GoLean/CLI.lean`) and the ONE cached certified row `imported-goose/channel/google-search` PASS→FAIL/membership. No other row moved. `gate-tail-fixround.txt` has the tail verbatim. |
| choice trace, FIX ROUND | the same tracer command for the SAME main binary the lane used (`.tmp/golean-main`, sha256 `155df5c3…`, re-run now) and the fix-round binary (`.tmp/golean-fix` = the gate's `golean`, sha256 `1ea8f2ac…`), concurrently; sorted dumps compared three ways (`cmp`) | **0 (cmp)**: BYTE-IDENTICAL — 23,679 records on all three sides (main now / fix / the lane's `trace-before.tsv`), the ONE sha256 `5f901024…58b5a` (the lane's recorded value); tracer logs identical modulo timing/paths; validator summaries identical (0 menu-invariant violations, 0 self-check alarms, 0 driver-agreement mismatches; the one ERROR row is the known frontend refusal); each run EXIT=1 for the same pre-existing «FINDINGS present» listing. `choice-trace-summary-fixround.txt` | 661 + 646 | main `7f1c1fe7` binary vs `1fafc9f2`'s | the whole-corpus choice trace is byte-identical after the fix round |

The expected red, named: the certificate-provenance STALE verdict is the intended one for changed
compiled inputs (the step's own controls all pass); the certified row goes red as a consequence.
The train's step 5a (`ci --slow`, install the reviewed candidate) is the remedy — a records refresh,
not a re-pin and not a finding (`docs/2026-09-09_certificate-provenance-design.md`).

## Audit fix round (2026-09-17) — warms, gate, trace

The pre-merge adversarial audit (`docs/2026-09-17_b7-context-store-audit.md`, branch
`review/b7-context-store-0917` at `b51bc5c4`; its own evidence
`docs/evidence/2026-09-17_b7-context-store-audit/`) returned FIX-FIRST, narrow and records-class.
Runtime effect on this branch: **2 files, +5/−42** — F1's one-line literal revert in
`GoLean/GoCore/Machine.lean` and F7's dead `variable (ctx : ProgramCtx)` block in
`GoLean/GoCore/MachineEqb.lean` (38 lines). No theorem statement changed, no definition changed.
Whole-branch runtime delta at this tip: `git diff --stat 5955e55f HEAD -- GoLean Tests`
= **34 files, +3,311/−3,303**.

Explicit-target warms, **complete** (captured `EXIT=`, `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G`
through `scripts/capped`): `GoLean.GoCore.MachineEqb` EXIT=0 (96 s, 25 jobs — the F1 edit's rebuild
of `Machine` and its dependents is inside this number) · `GoLean.GoCore` EXIT=0 (1 s, 33 jobs).
**0 warnings** in both logs.

| run | command | exit | wall s | SHA / tree | result |
|---|---|---|---|---|---|
| THE gate, AUDIT FIX ROUND | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (`artifacts/build-lock.d` taken 04:41:47, released 04:56:27; owner file; trap-protected release; wait-retry 120 s) | **1** | **880** (in the tracked tail: «CI total wall seconds: 880») | `d0e65182` + the dirty runtime tree (the two files), committed UNCHANGED as `ee3ff01a` | 3676 cases 3427 PASS / 249 expected FAIL (the same tally as both earlier rounds); 394 negatives; eval 211/0; `core build (warning-free)` ok; `core totality audit` ok; `wire boundary` ok; `frontend pins` ok; every step ok EXCEPT the same two EXPECTED 5a-class items — `certificate provenance` STALE (reconciler C9 HIGH: «changed dependency build/files/GoLean/CLI.lean») and the ONE cached certified row `imported-goose/channel/google-search` PASS→FAIL/membership, judged stale for that reason. **ZERO other drift**; the reconciler's finding set (2 findings, 1 HIGH — the C9 above and the pre-existing C13 MEDIUM «79 doc site(s) … patch-level Go version») is IDENTICAL to the tracked fix-round tail. `gate-tail-fixround2.txt` (102 lines, the same window as `gate-tail-fixround.txt`). |
| choice trace, AUDIT FIX ROUND | `scripts/choice-trace-corpus --dump --jobs 6 --out <dir> --golean <bin> $(cat .tmp/trace-ids.txt)` on the AUDIT's own 263-id subset (1 in 14 manifest rows; the id list is in the audit's `choice-trace-subset.txt`), run concurrently for the primary's certified build at main `5955e55f` (copied read-only, sha256 `155df5c3…` — the audit's main binary, same hash) and for this tree's gated build (sha256 `231df9a9…`); sorted dumps `cmp`'d | **0 (cmp)** | — | main `5955e55f` binary vs `ee3ff01a`'s | **BYTE-IDENTICAL** — 261 rows exported both sides, 1,566 traced (id,stream) lines, **1,404 consumption records** each, sha256 of the sorted dumps `8ca0a8088598602519646c3d390c6f6b9e378d18b9061d6b4b8ff58126652b18` on BOTH sides — **the same value the audit recorded for this subset at the candidate tip `d0e65182`**, so the audit fix round moved no consumption record (neither an unreachable `.internal` text nor a binder nothing bound is visible to the tracer). Both tracer runs EXIT=0; 2 frontend refusals, 0 `--exclude`, 0 ERROR ids, 13 refusal ids all non-PASS in the tracked baseline — identical on both sides; results TSVs identical (sha256 `5d21d89e…`). `choice-trace-subset-fixround2.txt`. |

Records checks re-run at this tip, captured exits: `scripts/check-bugs.sh` EXIT=0 (110 bugs; 14
unexplained fidelity failures, wrong-answer 0/0) · `scripts/check-evidence-size` EXIT=0 (PASS; 0 new
offenders) · `scripts/check-agents-alias` EXIT=0 (PASS, symlink shape) · `scripts/check-spec-anchors`
EXIT=0 (866 spec# + 255 mem# + 26 godoc citations resolve at the pin).

The two items the audit left to the [USER] — F1's alternative (disclose-and-keep the rewritten
literal instead of the revert) and F8 (the congr trio's one-context specialisation) — are PENDING
[USER] in `docs/2026-08-31_qrow-rulings.md`, «The B7 audit fix round», with the [AGENT]
recommendations; the handoff §13 carries the full F1–F10 disposition table.

## Merge train r39 — the 5a record ([AGENT] coordinator, 2026-09-17)

[USER] Mike 2026-09-17, verbatim (relayed): «Great, merge it.» Pre-merge main `5955e55f` →
`refs/snapshots/r39/main`; B7 `55592e62` fast-forwarded (the F1 revert and the F8 one-context
specialisation RATIFIED by landing as-is); the audit branch rebased (`7050bb9c`) and fast-forwarded.
Under the lock at `7050bb9c`: `scripts/build-certified` EXIT=0, 136 s (binary
`231df9a99f45…` — the fix-round-2 gate's binary); `release-check --base refs/snapshots/r39/main`
EXIT=2 (EXPECTED — «STALE certification: changed dependency build/files/GoLean/CLI.lean»);
`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` EXIT=1, 1031 s — red on EXACTLY the 5a pair
(`certificate provenance` STALE; the single drift line `imported-goose/channel/google-search
PASS→FAIL/membership`); `core-audit` PASS (14.9 s); 3676 rows otherwise unchanged; negatives 394 no
regression. Tail: `r39-ci-slow.tail.txt`. Candidate vs tracked record: `claim` and `observations`
IDENTICAL; 29 input hashes differ (B7's core files) and the receipt (clean `7050bb9c`, binary
`231df9a9…`) — INSTALLED in this commit; a provenance refresh, not a re-pin. The green re-run is the
full `ci --diff` at the records commit.
