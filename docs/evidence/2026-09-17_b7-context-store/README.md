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
| `ExecState` in code (`GoLean/`, `Tests/`) | 30 modules | **0** (5 docstring mentions of the historical name) |
| `itersNormalized` in `MachineWf` | 1 conjunct | **0** (D6); the pool's `ThreadWf` twin remains (PENDING [USER], handoff §8) |

`git diff --stat 7f1c1fe7 -- GoLean Tests` at the gate tip: 32 files, +3,058/−2,862; `NativeToIR.lean`,
`tools/nativefrontend/`, `scripts/check-frontend-pins` untouched (wire-neutral by construction).

## Explicit-target warms during the build (captured `EXIT=`, wall s)

Every build through `scripts/capped` at `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G` (the box lock held
only for the full default build and the gate). Representative lines from the lane's `.tmp/`:
Store+ProgramCtx 0 s (S1); Ops 5 s; Machine 4 s; StateWf 16 s (after five fix rounds of 8–12 s);
StepFn 1 s; MachineSound+UnseqSound 62 s (after 57–77 s rounds); `lake build GoLean.GoCore` 7 s at
the last round (33 jobs; earlier rounds 2–11 s); the trace/observer trio 2 s; default `lake build`
(lib + exe) 4 s at the last round (96 jobs); `Tests.GoCoreEval` 144 s; all `Tests.*` 30 s.

## Gate lines (captured exit codes, never grepped greens)

| run | command | exit | wall s | SHA / tree | result |
|---|---|---|---|---|---|
| THE gate | `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` (box lock; `LEAN_NUM_THREADS=4` by the cap) | **1** | 1068 | `fc1aa228` + the runtime tree, committed unchanged as `2500b434` | 3676 cases 3427 PASS / 249 expected FAIL; 394 negatives; eval 211/0; every step ok EXCEPT the two EXPECTED 5a-class items — `certificate provenance` STALE (C9: compiled inputs `build/files/GoLean/CLI.lean` changed) and the ONE cached certified row `imported-goose/channel/google-search` PASS→FAIL/membership (its cached record judged stale; NOT an observation change). No other row moved. `gate-tail.txt` has the differential summary, the drift block, the reconciler lines and the step list verbatim. |
| choice trace | `scripts/choice-trace-corpus --dump --jobs 6 --out <dir> --golean <bin> --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused` for main's binary (cold-built from `git archive 7f1c1fe7` under `.tmp/before/`) and for `2500b434`'s; sorted `dump-*.tsv` compared with `cmp` | **0 (cmp)**: BYTE-IDENTICAL — 23,679 consumption records from 21,834 (row, stream) lines over 3,639 traced rows (34 frontend refusals, 2 excluded), sha256 `5f901024…58b5a` on both sides; validator summaries identical (0 menu-invariant violations, 0 self-check alarms, 0 driver-agreement mismatches; the one ERROR row is the known frontend refusal `arrays/materialization-budget/over-budget`); each tracer run EXIT=1 (643 s) for the SAME pre-existing «FINDINGS present» depth listing. `choice-trace-summary.txt` | 643 + 643 | main `7f1c1fe7` vs `2500b434` | the whole-corpus choice trace is byte-identical (D5 (a)'s second leg) |

The expected red, named: the certificate-provenance STALE verdict is the intended one for changed
compiled inputs (the step's own controls all pass); the certified row goes red as a consequence.
The train's step 5a (`ci --slow`, install the reviewed candidate) is the remedy — a records refresh,
not a re-pin and not a finding (`docs/2026-09-09_certificate-provenance-design.md`).
