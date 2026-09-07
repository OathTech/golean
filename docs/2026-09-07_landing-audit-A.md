> **Landing preface ([AGENT] landing chunk L6 `land/sprint-records`,
> 2026-09-07).** Landing review of branch `typed-consumer-sprint` @
> `7edc298f` by the independent auditor A (2026-09-07), landed VERBATIM from
> the sprint worktree's scratch (`.claude/worktrees/typed-consumer-sprint/.tmp/landing-review/auditor-A.md`),
> where it was untracked; it is the source of every `A-Rn` finding id in
> `docs/2026-09-07_typed-sprint-landing-plan.md` and the chunk notes.
> Nothing below is edited. It describes the branch and the sprint WORKTREE
> as they were BEFORE the landing (the dirty staged `uintptr` merge, the
> storage-maintenance overlay, the evidence payload); which findings each
> landed chunk closed, and which remain open, is recorded in the chunk notes
> (`docs/2026-09-07_land-{gate-tooling,typed-core-proofs,observer-terminal,panic-text-tape}.md`)
> and summarized in `docs/2026-09-05_master-plan.md` §7.8. Paths of the form
> `.tmp/landing-review/…` are the auditor's scratch; the evidence it cites
> under `docs/evidence/2026-09-06_*` is on the archive branch
> (`docs/evidence/2026-09-05_typed-consumer-sprint/MANIFEST.tsv`).

# Landing review — auditor A (SEMANTICS / TRUST SURFACE / GATE INTEGRITY)

Branch `typed-consumer-sprint`, tip `7edc298f`; BEFORE = main `47195683`.
All diffs read from git objects (`git show <rev>:<path>`), never from the
working tree — see R7.

## VERDICT: **DO-NOT-LAND** (semantic/gate content)

One BLOCKER (R1): the new `string-member` lane grants PASS on rows where
gc's observed panic text is **provably not a member of the modeled set**,
because gc's message bytes are transported and then discarded. Reproduced
against the pinned oracle. Everything else on the branch is unusually
well-built; R1 is a localized, cheaply-fixable defect, but it converts a
real gc/machine divergence into a green and therefore cannot land as-is.

---

## R1 — BLOCKER — the `string-member` lane never compares gc's panic text; a known divergence is green

**Where.** `tools/string_member.py:186-198` (`check_actual_member`).

```python
def check_actual_member(machine, raw_go, actual_chain):
    observation(machine, "panic")
    raw_panic(raw_go)                      # gc: schema/status/childExit==2 only
    ...
    head = actual_chain[0]                 # <-- the MACHINE's own chain
    require(machine["message"] in selected_members(bytes(head["bytes"]), head["recovered"]),
            "machine text is not a prescribed member of the actual payload/flag")
    require(text(machine["output"], "machine output") == bytes(raw_go["outputBytes"]),
            "program output changed across R-1 membership")
```

`raw_go["messageBytes"]` — gc's actual first-line panic bytes, produced by
`tools/coverageharness/observe.go:45` and validated at
`tools/string_member.py:159,162` — is **never compared to anything**.
Confirmed by exhaustive search: the only non-test, non-evidence uses of
`messageBytes` at tip are the struct field and its own type check.

The membership check therefore compares the machine's rendered text against
renderings of the **machine's own** payload. It is a self-consistency check,
not a differential. The only gc↔machine comparisons left on these rows are
terminal class, child exit 2, and program output bytes.

**Reproduction (pinned oracle go1.26.5).**
Subject `Corpus/coverage/exec/panic-recover/string-members/main.go:41-43`:

```go
func InvalidAfter() { panic("a\n\xff") }
```

| | value |
|---|---|
| gc go1.26.5 (`GOTRACEBACK=system`, first line after `panic: `) | `a` — bytes `[97]` |
| AFTER (machine, pinned in `baselines/string-members/panic-recover/string-members/invalid-after-lf.json`) | `"\x61\x0a\xff"` — bytes `[34,92,120,54,49,92,120,48,97,92,120,102,102,34]` |
| `selected_members(b"a\n\xff", recovered=False)` | `{'"\x61\x0a\xff"'}` (singleton — the direct-decode candidate is dropped, 0xff is invalid UTF-8) |
| gc's draw ∈ modeled set? | **NO** |
| baseline row at tip | **PASS** / `string-member` |

Command used: `go run` under the run's own env in
`.tmp/landing-review/gcprobe/`, `go version` = `go1.26.5 linux/amd64`.

**Second, independent reproduction — the `repanicked` collapse (worse).**
Subject shape of `string-members/{equal,multiple}` and
`repanic-same-value-abort` (recover then re-panic the same string):

```go
func Equal() {
    defer func() { if r := recover(); r != nil { panic(r) } }()
    panic("orig")
}
```

| | value |
|---|---|
| gc go1.26.5, first line after `panic: ` | `orig [recovered, repanicked]` |
| AFTER (machine, pinned in all three pins) | `orig [recovered]` |
| gc's draw ∈ `selected_members(b"orig", True)` = `{'orig [recovered]', '"\x6f\x72\x69\x67" [recovered]'}` | **NO** |
| baseline rows at tip | **PASS** / `string-member` (×3) |

This one is structural, not incidental: a chain entry carries only
`bytes` + `recovered : Bool`, so `selected_members` **cannot express the
`repanicked` marker at all**. The modeled set can never contain gc's actual
observation for this shape, under any payload.

**Demonstrated divergent rows: 5 of 9** — `invalid-after-lf`,
`invalid-before-lf`, `invalid-recovered` (escape form vs gc's raw bytes),
and `equal`, `multiple`, `repanic-same-value-abort` (`[recovered]` vs gc's
`[recovered, repanicked]`). All are PASS at tip and all sit inside the
headline `3391 PASS`.

**Why this is a BLOCKER and not a disclosure issue.** The charter's
differential contract is *observed ∈ modeled* (the lower bound). Here the
model **excludes** the actual observation, which is precisely the condition
the differential exists to detect, and the gate is structurally blind to it.
The [USER] ruling R-1 (`docs/2026-08-20_w32-re-envelope-charter.md:28-40`)
authorizes exactly a *quotient via membership* on rendered text — a quotient
still requires checking that gc's draw lands in the class. R-1 also puts
"the payload's KIND" in the forced half to be "compared exactly", and says
"the conversion must not relax them". The implementation drops the
comparison rather than quotienting it, so the lane is outside R-1's terms,
not inside them. This is not the disclosed-latitude item; the disclosure
("PASS/string-member means the reviewed R1 member, not exact gc text",
`baselines/native-full.tsv:9`) describes a *weaker* comparison, but the code
performs *no* comparison on that axis.

**Blast radius.** All 9 `string-member` rows, 5 of them demonstrably divergent today. Because the payload the
machine's text is checked against is the machine's own, a divergence in the
panicked **value itself** (not merely its rendering) also passes green on
these rows.

**Fix (small — the machinery already exists).** gc's bytes are already
transported in `rawPanicRecord`. Add to `check_actual_member`:

```python
require(bytes(raw_go["messageBytes"]) in {m.encode("utf-8") for m in
        selected_members(bytes(head["bytes"]), head["recovered"])},
        "gc's observed message is not a member of the modeled set")
```

Then re-run the 9 rows. Expect `invalid-after-lf` and `invalid-before-lf` to
go RED — which is the correct, honest outcome, and is the pre-existing
`asciiString?` refusal restated. Either widen the member set so it genuinely
contains gc's raw-byte rendering (which requires a byte-level observation
channel — `messageBytes` already is one), or keep those two rows red. Add a
mutation to `scripts/check-string-members.py:77` for the new check; the
current mutation list contains `ignore-member` but no gc-message mutation,
so the mutation suite gives false assurance of completeness here.

## R2 — HIGH — `renderPanicHead` bakes a latitude choice into evaluator recursion (charter violation)

`GoLean/GoCore/Machine.lean:2192+`. Main returned `none` (fail-closed,
BUG-004: "boxing identity unmodeled: collapse undecidable") when a
repanicked value equalled the recovered one. Tip commits unconditionally:

```lean
if first.recovered then
  match first.value with
  | .interface .string (.string _) => some (base ++ " [recovered]")
  | _ => ... (old identity refusal retained for non-strings)
```

Measured: gc go1.26.5 prints `orig [recovered, repanicked]` for this shape
(reproduced above), the machine prints `orig [recovered]`. gc's choice is
allocation-identity-dependent, i.e. genuine latitude — but the model does
not represent the collapsed member at all, so it is not a *choice* between
two modeled members; it is a single member that happens to be the one gc
did not draw here. The charter is
explicit: "Latitude Go permits is reified (**the choice tape**), not baked
in" and "No semantic choice hides in evaluator recursion". This reifies it
as a **single hard-coded representative**, not a choice-tape draw and not a
set. Combined with R1 (nothing checks gc's draw), the model silently commits
to one branch of a real nondeterminism with no oracle coverage.

This is the mechanism by which `panic-recover/repanic-same-value-abort`
went **FAIL/lean-observation → PASS/string-member**, and its
`cases.tsv` simultaneously dropped its gc text pin (`expected_reason`
`orig` → `-`) and moved lanes. A strict-lane red was retired by
reclassification to a weaker oracle, not by a semantics fix.

**Fix.** Put the collapse on the choice tape with both members, or restore
the `none` refusal for the equal-value string case.

## R3 — HIGH — `renderStringMember` replaces a fail-closed refusal with an answer known to differ from gc

`GoLean/GoCore/Machine.lean:2062-2100, 2131-2134`. The `.interface .string`
arm changed from `asciiString? s.bytes` (an `Option`, refusing on any byte
≥ 0x80 or an embedded newline) to `some (renderStringMember s)` — **total,
never refuses**. On invalid UTF-8 it emits `PanicText.escapeAllBytes`, a
quoted `\xHH` string that Go never prints.

The widening to valid UTF-8 (`utf8String?`) is a legitimate **fidelity fix**
and is gc-validated: the 9 new `panic-recover/panic-text/*` rows and the
`panic-newline-abort` FAIL→PASS sit in the **strict** lane with real gc text
comparison. That half is good work. The *invalid*-UTF-8 half is the problem:
it produces a confident non-gc answer, and the only rows exercising it were
placed in the lane that does not check text (R1). Per doctrine, "a visible
red beats a hidden wrong answer".

**Fix.** Keep `none` for the invalid-UTF-8 case (restoring fail-closed), or
adopt a byte-level observation and compare bytes.

## R4 — MED — new gating pin class `baselines/string-members/` has no re-pin guard

9 JSON pins, ~538 lines each, gating through `scripts/diff-coverage:652-671`
and `scripts/ci:561-568`. The re-pin guard loop is
`scripts/ci:912  for GUARD_BASE in baselines/native-full.tsv baselines/negative-full.tsv`
— the JSON pins are outside it. So: no BUGS.md `Cases:` obligation, no
PASS→non-PASS trace, no in-tree regenerator, no `--bless` mode either.
A changed model output can be re-blessed by hand-editing a pin with no
guard trace. Mitigated (not closed) by the fact that every pinned field is
re-derived live in the same run.

Note also `scripts/ci:997-1041` makes FAIL→PASS **report-only by design**
("This NEVER blocks") — so nothing in the gate would have stopped the R2
lane reclassification either. That is pre-existing, but R1/R2 are the first
case where it matters.

**Fix.** Extend the guard to `baselines/string-members/**` with the same
BUGS.md/`Cases:` rule, or fold the 9 pins' verdicts into the TSV ratchet.

## R5 — MED — the tip has NO fresh full-corpus run; the last re-pin ran at 32 workers against a [USER] limit of 2

`docs/evidence/2026-09-06_o2-terminal-integration/FINAL.md`: "The ordinary
CI's full 3,635-case executable and 394-case negative records remain
**cached** from the accepted R1 run. They are not fresh full-corpus evidence
for this integration." Honestly disclosed, but the merge protocol wants a
full run behind a baseline re-pin at the merged tip.

`baselines/native-full.tsv:14-15` (verbatim):
```
#   Actual run used 32 workers under the unchanged 16G cap; metadata retained.
#   This missed earlier lane coordination; future conformance explicitly uses 2.
```
`docs/2026-09-06_typed-sprint-pause-state.md`: "Limits remain 16 GiB, 3 Lean
threads, 2 coverage workers." The final R1 baseline — the pin the whole
branch rests on — was measured at 16× the ruled concurrency. Concurrency is
timeout- and schedule-relevant for the racy/confluent/membership lanes.

**Fix.** One fresh full `scripts/ci --diff` at the merged tip at 2 workers
before the re-pin is accepted.

## R6 — MED — the crash-channel "authentication" degrades silently to the raw fallback

`tools/coverageharness/crashview.go:44-54`. `crashEvidence.validate()`
returns nil when ack and report are **both empty**, so a missing hook
registration is not an error on the abort path; `checkedAbortView` falls
through to the raw-marker fallback. For `ok`/`race`,
`crashview.go:141-144` correctly *requires* a non-empty ack — the abort path
is asymmetric. Also, `oracle.crash`/`oracle.registered` live in the
subject's own CWD and are writable by the subject.

Not currently exploitable (the fallback is genuinely stricter than main's,
and no corpus program is adversarial), but the commit message claim
"Authenticate oracle panic observations with a same-run crash channel" is
stronger than the code: authentication is best-effort, not mandatory.

## R7 — HIGH (process) — the branch is not in a landable state; the gate cannot be run clean here

`/home/dev/projects/golean/.claude/worktrees/typed-consumer-sprint` is
dirty: **319 files, ~75.5k insertions uncommitted**, including *staged*
edits to `GoLean/GoCore/Machine.lean`, `GoLean/CLI.lean`,
`GoLean/NativeToIR.lean`, `baselines/native-full.tsv`,
`tools/coverageharness/main.go`. This is the deliberate, user-known parked
uintptr merge (`docs/2026-09-06_typed-sprint-pause-state.md`: "Open,
resolved/staged no-commit merge of `5f185fb3` remains in progress. Do not
reset, abort, commit or overlay it"), so it is not sloppiness — but merge
protocol step 6 requires "clean, green", and `git_dirty` would be non-clean.
I did not touch it. Consequently `scripts/ci --diff` could not be run at tip
on a clean tree in this worktree; see "Gate lines" below.

Note the staged (not yet committed) work touches `GoLean/NativeToIR.lean`;
when it lands, merge protocol **step 5a owes `scripts/ci --slow`**. For the
committed tip alone, `tools/nativefrontend/wire.go` and
`GoLean/NativeToIR.lean` are **unchanged** vs main, so `--slow` is **not**
owed for `7edc298f` as it stands.

## R8 — LOW — `grep -F` multi-line pattern semantics in the reworked classifier

`scripts/diff-coverage` now matches `grep -aqF -- "$expected_reason"` where
it previously used a shell substring test over the whole blob. `grep -F`
treats an embedded newline in the pattern as **alternation**, so a
multi-line `expected_reason` would weaken from conjunction to disjunction.
Not currently reachable (TSV fields cannot contain literal newlines), but it
is a latent relaxation if reasons ever get unescaped. Related: `grep -F ''`
matches everything, so an empty `expected_reason` would be vacuous — guarded
today only by the manifest's `-` requirement.

## R9 — LOW/INFO — the oracle program is now rewritten before compilation

`tools/coverageharness/crashhook.go` injects `zz_golean_crash.go` and splices
`_goleanSetupCrash();` as the first statement of `main()`
(`main.go:605`). Every differential oracle now performs two file opens, a
`debug.SetCrashOutput` syscall and a file write before user code. The harness
already synthesized `main`, so this is an increment on existing practice, not
a new principle — but it does add an `init`-adjacent effect to a project with
a known init-order latitude item (L-011). Collision-guarded both ways
(reserved filename and reserved identifier both refuse). Exit code 78 is a
sentinel: a subject legitimately exiting 78 would be misclassified as a setup
failure — fail-closed direction (a red), so acceptable.

## R10 — INFO — `GOTRACEBACK=system` added to the oracle environment

`scripts/diff-coverage` `go_run_oracle`. This changes the oracle's stderr for
every aborting case and is a real change to trusted surface #2's invocation.
It is recorded in the run manifest (`go_traceback system`,
`go_crash_channel same-run-setcrashoutput-v1`), it is required by the new
terminal discriminator (`abortkind.go` pins the system-trace shape), and it
does not change program semantics. Correctly provenanced; flagging for
visibility only. Cosmetic: the `go_crash_channel` printf line is indented
with a literal TAB rather than spaces (harmless).

## R11 — LOW — `scripts/check-declarations` prints hashes but never compares them

Wired as a hard `bad` at `scripts/ci:555` and fail-closed under
`set -euo pipefail`, but its `sha256sum` lines (6 Lean modules,
`declaration.go`, the fixture test, the audit script, the fresh fixture) are
**printed, never `sha256sum -c`'d**, and the fixture goes to a `mktemp`, not
a tracked baseline. The Go producer and the Lean decoder are cross-checked
against each other fresh each run, with no tracked expected bytes — a
coordinated drift in both passes green. Real cross-language check, but not a
"pin" in the `check-frontend-pins` sense despite the step name.

## R12 — LOW — `declaration.go` has a cross-channel side effect into the executable emit path

`tools/nativefrontend/declaration.go:100` calls `e.localTypeOrdinal(obj)`,
which writes into `e.badLocalTypes` (`identity.go:314-317`) — a set consumed
by the *executable* export's `checkLocalTypeOrdinals` refusal. So exercising
the declaration serializer on an unknown local type can poison the
executable emit. Direction is fail-closed (spurious refusal, not a silent
pass), but it contradicts the file's own "separate schema … not accepted by
the current executable-type decoder" claim. Also two silent-default nits at
`declaration.go:17-23` and `:99-103` (a `nil`-package object gets
`"package": ""` / skips the ordinal guard rather than refusing) — currently
unreachable from real `go/types` output.

## What is clean (verified, not assumed)

- **`scripts/capped` is byte-identical to main.** No cap/knob change.
- **Frontend is a pure addition.** `tools/nativefrontend/` gains only
  `declaration.go` + two test files; **no existing frontend file is
  modified**. `wire.go` and `GoLean/NativeToIR.lean` are hash-identical to
  main — confirming `--slow` is not owed for this tip. `declaration.go` has
  no non-test caller and emits a separate schema, so no existing program's
  wire bytes can change. Determinism verified empirically (8 independent
  emits → 1 hash); interface methods explicitly sorted by `Id()`; no map
  iteration feeding ordered output. `go test ./tools/nativefrontend` at tip
  on go1.26.5: `ok … 0.398s`, all declaration tests PASS.
- **Twin pin did not move.** `baselines/pins/`, `baselines/stdlib-pin.tsv`,
  `scripts/check-frontend-pins`, `raftsubject/`, `tools/raftsubject/`,
  `stdlib-substitutions.tsv`, `inittask-std.tsv` all byte-identical to main.
  No re-pin reason owed.
- **Corpus rows are properly enumerated and baselined.** All 37 new rows are
  in `baselines/native-full.tsv` at tip; `coverage-manifest --list`
  enumerates all 39 ids cleanly. No `unsupported`/`stuck` rows; no non-PASS
  class counted green. `Corpus/controls/` sits outside `EXEC_ROOT` so it is
  not a differential row set — but it is not self-referential either: the
  runner executes real `go run` over it for all 13 control roles, and the 8
  non-abort roles get **exact** gc equality. Only the 5 abort roles inherit
  R1's blind spot.
- **`scripts/ci`: +94 lines, 0 deletions.** All 12 new steps are
  `step/if <check>; then ok else bad` blocks; `bad()` sets `fail=1`
  (`ci:96`). Every one can only add reds. No existing step was weakened, no
  env skip-knob added. `--lean-only` narrows two *new* checks, not existing
  ones.
- **`scripts/diff-coverage` rework is a net strengthening on every axis I
  could test**: classification moved off NUL-dropping shell command
  substitution onto direct byte reads; `exit status 2` went from substring to
  whole-line (`grep -aqFx`); marker search narrowed from stdout+stderr to
  stderr; the repanic-continuation *exemption* was removed (it allowed
  `print("panic: forged\n\t")` to forge an observation); `outputLiteral` now
  refuses invalid UTF-8 instead of silently substituting U+FFFD;
  `--read-observation` adds UTF-8+JSON validation and returns bytes
  unchanged (no re-encoding, so cached certified-set byte compatibility is
  preserved). The one relaxation of an existing check
  (`expected_reason == "-"` exemption at the panic/fatal manifest gate) is
  scoped to the new lane and compensated by that lane's own manifest
  constraints — its weakness is R1, not this line.
- **Baselines**: 0 removed rows, 0 silent stage/column edits, 0 unexplained
  rows. 37 born (all PASS), 2 non-PASS→PASS, 1 PASS→non-PASS. The single
  PASS→non-PASS (`sync/mutex-unlock-fatal/during-panic-unwind`) **is** on a
  BUGS.md `Cases:` line (`docs/BUGS.md:6252`, BUG-106) — protocol satisfied.
  Header arithmetic reconciles exactly across all four re-pins; no historical
  record rewritten; `baselines/go-oracle-pin` byte-identical (`go1.26.5`);
  `certified/`, `negative-full.tsv`, `stdlib-pin.tsv` byte-identical. Nothing
  moved out of the default `--diff` run into a slow tier.
- **The ~60 new `GoCore` modules are a genuinely additive proof layer.** No
  `attribute [...]` retro-applied to any pre-existing declaration, no
  `export`, no `macro`/`notation`/`syntax`, no competing instance on the
  execution path, no redefinition of anything `stepFn` calls. Only
  `Machine.lean` imports new code (`PanicText`), and that is R3's hunk.
  Spot-checked theorems are non-vacuous over the real `Program`/`ExecState`
  with concrete lowered-Go witnesses and negative controls — except
  `StringPanic.renderStringMember_bytes_or_escape`, which is a definitional
  case split restating that the function returns one of its own two branches
  (near-tautological; should not be cited as evidence for the renderer).
  Recorded caveat: the Boolean/recovery profiles cover a very small Go
  fragment (no ints, arithmetic, slices, maps or channels).
- **Escape hatches: zero delta vs main.** No `sorry`, no `native_decide`, no
  `axiom`, no new `partial` in `GoCore/` (all hits are prose in comments,
  identical to main); +3 `getD`/`default` hits, all benign. Two new
  `decide +kernel` over `Fin 256` in `PanicText.lean` — kernel, not native,
  doctrine-permitted. `Tests/InterfaceAudit.lean` was **strengthened**
  (broader axiom sweep, and a constructive-dependency check pinning the new
  renderer to `propext`/`Quot.sound` only).
- **`lakefile.toml`**: `defaultTargets` and the `GoLean` lib are unchanged;
  the +38 lines are 10 new test libs and 4 globs. The iris customer lives in
  `spikes/iris-customer/` with its own lakefile and is not required by the
  root project — **charter boundary not breached**.

## Gate lines

`scripts/ci --diff` **was not run at tip on a clean tree** — it cannot be,
in this worktree, without violating the explicit "do not reset, abort,
commit or overlay" instruction on the parked merge (R7), and my brief
forbids modifying tracked files. I did not run it in the dirty tree, because
that would measure the unrelated in-flight uintptr arc rather than
`7edc298f`. **The gate line for landing is therefore OWED and must be
produced on a clean checkout of the merged tip.**

What I did reproduce independently, on a clean `git archive` extraction of
`7edc298f` at `.tmp/landing-review/tipbuild/`:

```
core build:  PASS
  scripts/capped lake build  -> Build completed successfully (194 jobs).
  EXIT=0
  382.87s user 14.95s system 350% cpu  1:53.65 total   (cold, default cap)
frontend pins:  not run (owed)
eval tests:     not run (owed)
bug-index:      not run (owed)
baseline diff:  not run (owed)
re-pin guard:   not run (owed)
RESULT:         not run (owed)
git_dirty:      DIRTY — 319 files / ~75,523 insertions uncommitted
                (staged: Machine.lean, CLI.lean, NativeToIR.lean,
                 baselines/native-full.tsv, tools/coverageharness/main.go)
--slow owed?    NO for 7edc298f as committed (wire.go and NativeToIR.lean
                unchanged vs main). YES once the staged uintptr work lands.
```

Build-time impact of the ~8.8k new Lean lines is modest (~2 min cold, 194
jobs) — **not** an argument for a separate Lake target.

## Landing conditions

1. **R1** — compare gc's `messageBytes` against the member set; accept the
   resulting reds, or widen the set to genuinely contain gc's rendering. Add
   the corresponding mutation.
2. **R2/R3** — put the `[recovered]` collapse on the choice tape (or restore
   the refusal), and restore fail-closed for invalid-UTF-8 string payloads.
   These are [USER] calls, not agent calls: they change the trusted machine.
3. **R4** — bring `baselines/string-members/` under the re-pin guard.
4. **R5** — one fresh full `scripts/ci --diff` at the merged tip, at the
   ruled 2 workers, on a clean tree; produce the gate lines above.
5. **R6** — make crash-channel authentication mandatory on the abort path
   except for genuine pre-`main` aborts, or soften the claim in the record.
