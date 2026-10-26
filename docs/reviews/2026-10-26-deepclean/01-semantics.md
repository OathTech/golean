# Deep-clean supporting review: executable semantics and proof claims

**Reviewer:** [AGENT Codex / semantics], 2026-10-26. **Reviewed revision:**
`62bb461463d94c9eb4f3d003aa441db653bd77c3`, branch `audit/deepclean-1026`.
This is an independent source review with targeted executable probes, not an
exhaustive proof of fidelity. Product files were read-only. Recommendations
below are proposals; no change of policy or product was made.

## Verdict

The current release candidate has an admitted, deterministic wrong answer for
ordinary Go pointer identity. The same defect breaks pointer-keyed maps and
interface equality. Separately, a still-exposed enumeration path is advertised
as backed by a correctness theorem that was removed from this tree. These are
release-relevant defects, not merely a shortage of test coverage.

The retained headline theorems sampled here depend only on the classical trio
of standard Lean axioms. That is valuable evidence about their kernel trust;
it does not establish that the interpreter implements Go correctly or restore
the missing enumeration proof.

## Method and coverage

The starting points were the executable core, memory/location representation,
goroutine scheduling, the kept sequential-to-pool bridges, and the claims made
to proof consumers. I inspected `Ops.lean`, `Machine.lean`, `Multi.lean`,
`Store.lean`, `Platform.lean`, `ExecutionStatement.lean`, the relevant proof
modules, `EnumSpec.lean`, `EnumDedupCheck.lean`, and their CLI callers. I checked
source-level expectations against the checked-out Go reference where useful.
Earlier review verdicts were not used to direct the initial inspection.

The coordinator subsequently pointed to the enumeration retirement boundary;
I independently checked the imports, declarations, public documentation, and
live command. I also sent the adjacent `sortSlice` over-refusal issue to the
frontend reviewer, who was already investigating it.

All executable probes used `capped`, the prepared worktree's frontend and
interpreter, and Go `go1.26.5`. Oracle runs set `GODEBUG=panicnil=0` and used a
review-local `GOCACHE` and `GOTMPDIR`. The Lean probes were single-file runs
against built modules, not independent clean builds. No full gate or corpus
run was started by this reviewer; shared validation belongs to the main review.
Scratch was isolated under `.tmp/deepclean-semantics/` and is not evidence that
needs to be preserved: the important reproduction sources are below.

| ID | Priority | Finding | Evidence class |
|---|---|---|---|
| S1 | High; fix before release | Equivalent Go pointers compare unequal after a legal struct-pointer conversion | New, reproduced source-Go wrong answer |
| S2 | High; settle before release | The exposed dedup enumerator claims a theorem that is absent from the release tree | Reproduced missing declaration plus live claim |
| S3 | Medium | Malformed parked core states are classified as Go deadlock after the underlying error is swallowed | Reproduced core API robustness failure; no source-Go reachability shown |
| S4 | Medium | Broad warning suppressions and resource overrides contradict the stated narrow-exception practice | Source-confirmed maintenance and assurance gap |

## S1. Pointer identity depends on the static spelling of a struct field

**Locations:** `GoLean/GoCore/Ops.lean:3746` (`valueEq`'s pointer arm),
`:2824`–`:2844` (`Loc.canon` and its rationale), `:2514`–`:2541`
(`structTagCompatible` / `loadLoc`), and `:3971`–`:3984`
(`mapEntryIndex?`).

A Go pointer conversion between two struct types with identical underlying
fields is legal; struct tags may differ. Both field addresses below refer to
the very same `int` variable. Go says they are equal. GoLean retains the static
struct `TypeId` in the `.field` location and compares the two location values
structurally, so it says they are unequal.

Save this source as `.tmp/deepclean-repro/alias/main.go`:

```go
package main

type A struct { X int `json:"a"` }
type B struct { X int `json:"b"` }

func pointerAlias() bool {
    a := A{X: 7}
    b := (*B)(&a)
    return &a.X == &b.X
}

func pointerMap() int {
    a := A{X: 7}
    b := (*B)(&a)
    m := map[*int]int{&a.X: 1}
    m[&b.X] = 2
    return 10*len(m) + m[&a.X]
}

func pointerIface() bool {
    a := A{X: 7}
    b := (*B)(&a)
    return any(&a.X) == any(&b.X)
}

func main() { println(pointerAlias(), pointerMap(), pointerIface()) }
```

From the worktree, after creating the two cache directories:

```sh
capped .tmp/nativefrontend --dir .tmp/deepclean-repro/alias \
  --out .tmp/deepclean-repro/alias.json
capped .lake/build/bin/golean native-json-run \
  --input .tmp/deepclean-repro/alias.json --function pointerAlias
capped .lake/build/bin/golean native-json-run \
  --input .tmp/deepclean-repro/alias.json --function pointerMap
capped .lake/build/bin/golean native-json-run \
  --input .tmp/deepclean-repro/alias.json --function pointerIface
GOCACHE="$PWD/.tmp/deepclean-repro/gocache" \
GOTMPDIR="$PWD/.tmp/deepclean-repro/gotmp" \
GO111MODULE=off GODEBUG=panicnil=0 \
  capped go run ./.tmp/deepclean-repro/alias
```

Observed results:

| Subject | Go 1.26.5 | GoLean | Machine classification |
|---|---:|---:|---|
| `pointerAlias` | `true` | `false` | `ok`, exit 0 |
| `pointerMap` | `12` | `21` | `ok`, exit 0 |
| `pointerIface` | `true` | `false` | `ok`, exit 0 |

The frontend exported the program successfully. No choice warning or refusal
qualified these answers. I also reproduced the equality failure with two
named structs having **no tags at all**. This is not zero-sized-object
latitude: the field is a nonzero-sized `int`, and the addresses identify one
variable. It is not a scheduling question or an observation-format mismatch.

The machine already has the relevant distinction. `Loc.canon` explains that
the field's static `TypeId` is a spelling, not an address component; BUG-111's
repair uses canonical locations for data-race and happens-before keys. The
pointer equality arm still uses `l == r`. Interface equality recursively
reaches it, and map search uses `valueEq`, explaining all three failures.
The same-type alias and distinct-allocation controls returned `true` and
`false` respectively. A write through the converted pointer was correctly
visible through the original pointer (`9`), establishing that access and
identity disagree inside the same admitted program.

**Impact:** pointer-based memo tables, visited sets, identity comparisons, and
interfaces holding these pointers can produce wrong program results with a
successful status. This is a new identity defect adjacent to BUG-111, not a
reproduction of that bug's already-repaired race-shadow comparison.

**Proposed disposition:** define physical pointer identity consistently with
the accepted location aliases, and use it for language equality and therefore
map lookup. Reusing the canonicalization may be appropriate, but its scope
must be checked rather than applied to every structural state equality:
deduplication's structural equality has a different obligation. Add the
direct, boxed, map insertion/lookup/delete, nested-field and array-element
alias cases, plus distinct-location controls. Re-run the normal trust and
differential gates. Do not represent the existing successful outputs as
intentional latitude.

## S2. The dedup path still advertises a removed correctness theorem

**Locations:** `GoLean/GoCore.lean:17`–`:20`,
`GoLean/GoCore/EnumSpec.lean:6`–`:24`,
`GoLean/GoCore/EnumDedupCheck.lean:6`–`:17`,
`GoLean/EnumDedup.lean:12`–`:17`, `GoLean/CLI.lean:1608`–`:1613`,
`:2536`–`:2543`, `:2570`–`:2577`, `:2609`, and `docs/cli.md:278`–`:281`.

The comments and public CLI reference say the dedup result passes a verified
checker and that a theorem, `checkCert_slowObs`, establishes equality with
`SlowObs`. The executable's summary still prints `certified=checkCert`.
However, the root explicitly records retirement of `EnumDedupSound`, and no
such source file or theorem is present in the tracked tree. The checker
definition remains, with no theorem in its module.

This is reproducible after importing the complete root, so it is not merely a
missing convenience import. Save the following as an ignored Lean probe:

```lean
import GoLean
open GoLean.GoCore.Machine
#check checkCert
#check checkCert_slowObs
```

`capped lake env lean <probe>` prints the type of `checkCert`, reports
`Unknown identifier checkCert_slowObs`, and exits 1. The source inventory is
also conclusive:

```sh
git ls-files '*EnumDedup*'
rg -n 'checkCert_slowObs|EnumDedupSound' GoLean GoLean.lean docs/cli.md
```

The tracked implementations found are `GoLean/EnumDedup.lean` and
`GoLean/GoCore/EnumDedupCheck.lean`; references to the missing proof persist in
comments. For a live successful certificate, run S1's wire with:

```sh
capped .lake/build/bin/golean coverage-observations \
  --input .tmp/deepclean-repro/alias.json --function pointerAlias \
  --engine dedup --expect-status ok
```

The run printed the singleton `false` observation and reported
`observations=1`, `nodes=51`, `edges=50`, `certified=checkCert`, exit 0.
The false answer in that example is S1, **not evidence that dedup computed
the wrong set of this interpreter's results**. The independent defect is
that the promised live proof connecting the certificate to that set is gone.

**Impact:** a proof consumer or differential-harness maintainer can reasonably
read the public reference and source as saying the dangerous completeness
direction is kernel checked at the candidate revision. Building and replaying
the remaining checker definition does not prove its specification. An old
proof about a historical machine does not provide a checked theorem about the
release machine. In particular, neither the green build nor the surviving
axiom checks can detect an absent theorem unless its presence is required.

**Proposed disposition:** make an explicit product decision before release.
Either restore and check the theorem and its dependencies against the live
driver and checker, or withdraw the verified-checker claim everywhere and
state that the checker itself is trusted executable apparatus. If retaining
the proof claim, add one cheap declaration-presence/use check at the existing
trust boundary; do not grow a second independent audit framework. The
relation's retirement need not be reversed wholesale merely to correct the
claim, but a downgrade of the assurance story must be visible to users.

## S3. A missing channel cell becomes an apparently legitimate deadlock

**Locations:** `GoLean/GoCore/Multi.lean:302`–`:367` (`wakeReady`),
`:370`–`:375` (`threadRunnable`), `:1716`–`:1724` (`stepMulti`), and
`:1968`–`:1970` (`execProgLoop`'s empty-runnable branch).

`wakeReady` maps channel-payload errors to `false`; the sync branch similarly
maps failed loads and unexpected cell shapes to `false`. The scheduler sees
no runnable thread and returns the Go terminal `deadlock`. The comment says
the resume operation would fail closed, but the readiness decision prevents
the resume operation from being reached.

This source is sufficient to reproduce the distinction:

```lean
import GoLean.GoCore
open GoLean GoLean.GoCore GoLean.GoCore.Machine

def absentChannel : Config :=
  .blockedSend (some (.base ⟨0⟩)) (.int 3 .int) .stop

#eval wakeReady ProgramCtx.ofTables {} absentChannel
#eval match resumeThread ProgramCtx.ofTables {} absentChannel with
  | .ok _ => "ok"
  | .error stop => reprStr stop
#eval match execProgLoop ProgramCtx.ofTables 10
    ⟨#[.running absentChannel none], {}, 0⟩ {} [] with
  | .ok _ => "ok"
  | .error stop => reprStr stop
```

`capped lake env lean <probe>` exits 0 and prints, respectively:

1. `false`;
2. a `GoLean.Stop.refusal` / `GoLean.Refusal.stuck` naming the unbound heap
   location at base address 0;
3. `GoLean.Stop.terminal (GoLean.Terminal.deadlock)`.

**Scope:** this is a deliberately malformed hand-built core state. I have
**not** shown that the production decoder and setup can produce it from a
well-typed Go program. It therefore must not be counted as another confirmed
source-Go wrong answer. It is an explicit fail-open error-classification path
on an exported semantic API, relevant to direct GoCore consumers, future
machine changes, and the stated fail-closed discipline. The distinction
matters because `deadlock` is treated as a Go behavior while `stuck` is a
model refusal.

**Proposed disposition:** propagate a fallible readiness result at the driver
boundary, or establish and enforce the required configuration invariant at
the API that accepts such states. Keep a valid nil-channel deadlock control
beside the malformed-channel refusal test. A prose assurance that a path is
unreachable is not a replacement for either mechanism.

## S4. Warning-free assurance is weaker than the working practice says

**Locations:**

- `GoLean/GoCore/StateWf.lean:64`–`:65` disables unused-simp-argument and
  unused-variable linting broadly.
- `GoLean/GoCore/PoolFacts.lean:42`–`:46` sets `maxRecDepth` to 8192 and
  disables unused-simp-argument linting for the file.
- `GoLean/GoCore/TableMonotonicity.lean:394`–`:395` and `:783`–`:784` set
  broad heartbeat limits and disable unused-simp-argument linting.
- `Tests/GoCoreAdmission.lean:6` and `Tests/GoCoreContract.lean:244`–`:245`
  contain broad resource overrides too.

Reproduce the inventory without building:

```sh
rg -n 'set_option (linter\.[A-Za-z]+ false|maxRecDepth|maxHeartbeats)' \
  GoLean Tests
```

Some neighboring suppressions and resource overrides correctly use `in` to
scope themselves to one declaration; the broad examples above do not.
`StateWf` and `PoolFacts` give a rationale for shared `simp` sets, but that
does not justify suppressing warnings in unrelated future declarations, and
the unused-variable suppression has no comparably specific explanation.
The live charter describes the challenge's per-declaration sorry-warning
suppression as its one allowed warning suppression (`CLAUDE.md:227`–`:230`).

**Impact:** these are not nonstandard axioms and do not invalidate a theorem
accepted by Lean's kernel. The problem is maintenance and the accuracy of
the assurance being offered: a green warning-free build cannot demonstrate
absence of warnings that entire files have disabled. Broad resource settings
also conceal which declarations actually require the exception.

**Proposed disposition:** remove unnecessary settings, repair warnings, and
restrict unavoidable exceptions to the relevant declaration with a specific
reason. Any retained project-level exception needs the ordinary explicit
practice-change disposition, not an undocumented inherited suppression. Do
not add a large new gate solely to police this cleanup.

## What held in this sample

The following seven headline theorem axiom probes all completed successfully
and reported only `propext`, `Classical.choice`, and `Quot.sound`:

```lean
import GoLean
#print axioms GoLean.GoCore.ExecutionStatement.run_ok_iff
#print axioms GoLean.GoCore.ExecutionStatement.classification
#print axioms GoLean.GoCore.ExecutionStatement.classification_wf
#print axioms GoLean.GoCore.ExecutionStatement.single_embedding
#print axioms GoLean.GoCore.ExecutionStatement.program_bridge
#print axioms GoLean.GoCore.Machine.execProgLoopOut_snd
#print axioms GoLean.GoCore.Machine.execProgLoopOut_acc
```

The statements inspected keep relevant boundaries visible: `Prefix` threads
choices and successful steps; `NoRefusal` is an explicit reachability premise,
not a guarantee supplied for every decoded program; the single-goroutine
embedding is not a theorem validating arbitrary concurrent Go executions.
The documentation exposes the native lowering's lack of a correctness
theorem and the fixed gc/linux/amd64 instance. Those are honest limitations
when retained prominently and not overridden by stronger surrounding prose.

Additional small runtime controls agreed with the pinned Go oracle:

| Control | Result |
|---|---|
| Same-type pointers to one struct field | `true` |
| Pointers to fields in distinct nonzero-sized allocations | `false` |
| Store via converted struct pointer, load via original | `9` |
| `min` respects negative zero in either operand order | `true` |
| `max` respects positive zero in either operand order | `true` |
| Runtime NaN compares unequal to itself and ordered comparisons are false | `true` |
| Interface containing a typed nil pointer is non-nil and equals itself | `true` |
| Range over three invalid UTF-8 bytes produces three replacement runes | `196599` |

The floating-point probes used `p := 0.0; z := -p`, reciprocal sign tests,
and `n := p/p`; the NaN was never exported as raw bits. Initial probes using
`math.Copysign` and `math.NaN` were refused as frontend-quarantined functions,
with `unsupported` status; they were not counted as passing executions.

For reproducibility, the substantive control bodies are:

```go
func floatMinZero() bool {
    p := 0.0; z := -p
    return 1/min(z,p) < 0 && 1/min(p,z) < 0
}
func floatMaxZero() bool {
    p := 0.0; z := -p
    return 1/max(z,p) > 0 && 1/max(p,z) > 0
}
func nanCompare() bool {
    z := 0.0; n := z/z
    return n != n && !(n<n) && !(n>=n)
}
func nilInterface() bool {
    var p *int; var q any = p
    return q != nil && q == any(p)
}
func badUTF8() int {
    s := "\xff\xc0\xaf"; sum := 0
    for _, r := range s { sum += int(r) }
    return sum
}
```

## Residual questions and release expectations

The latitude inventory already acknowledges the scheduling-granularity
obligation, zero-size address narrowing, missing portable-platform envelope,
allocation/materialization bounds, and several implementation-dependent
observations. I did not re-prove those boundaries or turn an existing
disclosure into a new finding. The release needs a named supported scope;
passing examples and a total interpreter do not establish the full Go
behavioral envelope.

The allocator-independence argument in the latitude inventory is explicitly
located on the parked reasoning branch and explicitly not rechecked here.
That distinction should remain visible to consumers: a historical proof is
not a live-release theorem. Unlike S2, that inventory passage already admits
the limitation.

I did not exhaustively inspect every step arm, enumerate the full scheduler,
run the full differential corpus, or independently rerun the kernel replay,
`lake check`, or comparator. I did not establish end-to-end semantic
preservation of frontend lowering, which the project itself does not claim.
The targeted controls are evidence about their particular inputs only.

The practical release work from this review is: repair S1 with regression
coverage; resolve S2's live assurance claim; disposition S3's error swallowing
without overstating its reachability; and remove or explicitly narrow S4's
maintenance exceptions. Keep the broad theoretical limitations stated even
after those fixes. None of these recommendations authorizes a merge, tag,
push, or change to the charter.
