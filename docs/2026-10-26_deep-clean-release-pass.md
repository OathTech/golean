# Deep-clean release review

2026-10-26 · [AGENT Codex, coordinating reviewer]

Reviewed source: **`62bb461463d94c9eb4f3d003aa441db653bd77c3`**.
Review branch: `audit/deepclean-1026`, in the prepared `deepclean-1026` worktree.

**Verdict: this revision is not ready to release under its advertised behavioral
and verification claims.** We found a new admitted wrong-answer class,
false-green validation paths, a seed-input resource-budget bypass, a verification
claim whose supporting theorem has been removed, and a missing third-party
notice. These are concrete findings, not a general demand for more assurance.
The owner can decide to publish a more narrowly described research snapshot;
this review does not change the release criteria or authorize a tag.

There are **19 consolidated findings**, with concrete reproductions and scoped
limitations in the supporting reports. The product tree was read-only throughout
this task. Deliverables are this
review, the [proposed release punch list](2026-10-26_deep-clean-release-punch-list.md),
and the supporting reviews below. No fix is represented as implemented.

## Review design and coverage

The initial map considered implementation surfaces and audiences. A Go
programmer needs correct source execution and honest refusals; a proof consumer
needs precise statements and assumptions; a tester needs trustworthy verdicts;
a contributor needs reproducible tools; a distributor needs the right notices;
and a release reader needs to understand what a green result establishes.

| Aspect examined | Principal starting points | Evidence and limits |
|---|---|---|
| Values, storage, conversions, identity, operations | `Value`, `Ops`, `Machine`, `StepFn`, frontend-generated programs | Pinned-Go differentials, pointer-alias counterexample, integer-sort and language-feature controls |
| Goroutines, races, channels, synchronization, latitude | `Multi`, `Race`, choice sites, latitude inventory | Source review, malformed-core probe, known sort-race controls; no general memory-model proof established |
| Proof statements and theorem trust | `Prefix`, `Finish`, pool bridges, equations, table monotonicity, comparator challenge | Sample axiom checks, shared validation, missing-dedup-theorem check; proof acceptance is not Go conformance |
| Enumeration and observation sets | DFS and dedup paths, checker, `SlowObs`, membership harness | Checker wiring and claim audit; no independent exhaustive reimplementation |
| Frontend and source admission | Native frontend, module/version policy, methods, generic lowering | Malformed-module probes and 26 successful focused language differentials |
| Wire, JSON, seed, CLI and failure protocol | `NativeToIR`, `StrictJsonParse`, `SeedFile`, `Seed`, `CLI` | Invalid observation inputs, entry/seed checks, small capped allocation counterexample |
| Differential and negative corpus | Process status, observer, timeout wrapper, manifests, causes, baselines | Fresh corpus run plus real timeout/SIGKILL controls against unmodified scripts |
| Build, kernel replay and CI | Lake targets, replay, axiom audit, check/comparator wrappers, workflow | Locked/capped full run; no hosted-runner observation or cold network installation |
| Raft subject and instruments | Derivation, pin checks, harness, probes, trace tooling | Derivation check and isolated controls; full protobuf-dependent run unavailable offline |
| Release scope and compatibility | README, release procedure, kept API, changelog, document index | Source-to-claim reconciliation; no downstream upgrade attempted |
| Packaging and third-party provenance | License inventory, imported source, setup pins, tracked artifacts | Missing goose notice established at pinned source; other generated-code notices need completion |
| Expectations and maintenance | Newcomer commands, terminology, records, working instructions | README example executed, stale claims identified, existing verbatim remarks flagged without copying them |

The first three reviewers received different starting areas and permission to
follow concerns anywhere. No prescribed verdict or earlier review conclusion
was supplied. A fourth reviewer began independently on robustness and
portability and independently rediscovered the seed-allocation issue. All
worked in the same read-only source worktree with separate scratch directories
and report files. The coordinator reconciled duplicates, checked source, and
independently reproduced the pointer wrong answers, missing theorem, oversized
seed, repaired allocation guard, and README example.

Supporting reports preserve independent judgments and reproduction details:

1. [Semantics, concurrency, and proofs](reviews/2026-10-26-deepclean/01-semantics.md).
2. [Frontend, CLI, and seed admission](reviews/2026-10-26-deepclean/02-frontend-cli.md).
3. [Validation, release machinery, and raft instruments](reviews/2026-10-26-deepclean/03-validation-release.md).
4. [Release readers, packaging, and documentation](reviews/2026-10-26-deepclean/04-release-readers.md).
5. [Independent robustness and portability pass](reviews/2026-10-26-deepclean/05-robustness.md).

These are focused reviews and finite experiments, not an exhaustive proof that
everything else is correct. The concrete new defects have short reproductions
in the reports. The 26 successful frontend spot checks are a reported one-off
sample with descriptions and outcomes, not a retained rerunnable suite. Generated
logs, caches and probes are disposable.

## Ranked findings

Priorities are **recommendations**, not new gates. P1 means address before a
release relying on the affected claim or exposing that behavior. P2 means a
concrete defect to repair or explicitly scope out. P3 is cleanup that should not
delay correctness repairs. No P0 finding alleges a contradiction accepted by Lean.

| ID | Priority | Finding | Supporting evidence |
|---|---|---|---|
| DC01 | P1 | Legal pointer aliases compare unequal and become distinct map keys | Semantics S1 |
| DC02 | P1 | Negative corpus publishes PASS after compiler timeout or kill | Validation V1 |
| DC03 | P1 | Tiny seed input allocates beyond materialization budgets before validation | Frontend FE-01; robustness corroboration |
| DC04 | P1 | Dedup still claims a proof-backed checker after its soundness theorem was retired | Semantics S2 |
| DC05 | P1 | Imported MIT-licensed source ships without its upstream notice | Release readers D1 |
| DC06 | P2 | Invalid module syntax and unsupported patch requirements pass admission | Frontend FE-03, FE-04; two repair predicates |
| DC07 | P2 | Observation comparison accepts ambiguous/malformed JSON and impossible byte values | Frontend FE-02; robustness |
| DC08 | P2 | Empty raft scenario selections report all green | Validation V2 |
| DC09 | P2 | Raft instrument counts matching output from a killed machine as agreement | Validation V3 |
| DC10 | P1 for affected tools | Ordinary `--out` use deletes unrelated existing contents | Validation V4 |
| DC11 | P2, latent core boundary | Malformed blocked state becomes Go deadlock instead of refusal | Semantics S3 |
| DC12 | P2 | Broad warning/resource overrides contradict the narrow-exception practice | Semantics S4 |
| DC13 | P1 for claims | The supported behavioral envelope is not a concise current release contract | Release readers D2 |
| DC14 | P2 | Living docs misdescribe repaired features, counts, and retained surfaces | Release readers D3; frontend FE-05 |
| DC15 | P2 | Reference setup promises pins while raft floats | Release readers D4; validation debt 1 |
| DC16 | Owner decision | Tracked guidance preserves verbatim human remarks | Release readers D5 |
| DC17 | P3 | Working guidance and live tools retain obsolete operational paths | Release readers D6; validation debts 3–4 |
| DC18 | P2 | Choice-trace corpus can let stale successes mask fresh errors; summary failure exits 0 | Robustness |
| DC19 | P2 | Comparator wrapper fails before comparison under C.UTF-8 | Release readers D7; fresh full gate |

## Findings and implications

### DC01: pointer identity is not physical-address identity

Two struct types with identical fields and different tags may legally be viewed
through converted pointers. The model permits the conversion and access, but
pointer equality compares raw `Loc` representations, which retain the owning
struct's static type. Two pointers to the same `int` field consequently compare
unequal. This propagates into interface and map-key equality. It is an admitted
source-Go counterexample, not unsafe code or a zero-size-allocation choice.

Pinned Go returned **`true 12 true`** for direct pointer equality,
`10*len(map)+lookup`, and boxed-pointer equality. GoLean returned **`false 21
false`**, all with status `ok`. The coordinator repeated all three. The pointer
arm is `GoLean/GoCore/Ops.lean:3746`; `Loc.canon` at line 2824 already documents
why the static tag is not address identity. The semantics report includes the
complete small source and commands. Repair physical identity without losing
Go's dynamic-type distinction for pointers of different types.

### DC02: a killed negative oracle can certify rejection

`scripts/coverage-negative:310–324` discards the nonzero compiler status before
looking for the expected diagnostic. If the expected text was emitted first,
timeout or SIGKILL is accepted as rejection; a normal frontend rejection then
makes the row PASS. The reviewer used the real negative fixture and frontend,
with controlled oracle subprocesses that actually timed out or killed
themselves. Both produced runner exit 0 and PASS. Normal rejection also passed.

This does not prove a historical real compiler was killed. It proves the green
cannot exclude that failure. Retain and classify process status before accepting
diagnostics. The positive runner already distinguishes non-verdicts. No baseline
re-pin should be needed for the repair.

### DC03: seed input bypasses budgets before execution begins

`SeedFile.parseTypeSpelling` permits unrestricted array lengths. `Seed.seedAllocFrom`
then creates default values before checking supplied value shapes. A seed with
an enormous array type and an empty list allocates before discovering the
mismatch. Decoder array/footprint guards do not cover this entry, and execution
fuel does not bound setup allocation.

The coordinator's `[2]int`/empty-list control returned a named `stuck` error,
exit 1. Changing only the type to `[67108864]int`, with `--fuel 0`, produced
**exit 137 and no observation** under `CAPPED_MEM_MAX=256M`. The deliberately
small cap contained the reproduction. Independent reviewers reproduced the same
class. This is an apparatus failure, not a named refusal. Validate type, value
shape and aggregate allocation cost before materialization, including unused
cells and nested types; preserve cyclic-reference support.

### DC04: the advertised dedup theorem is absent

`GoLean/GoCore.lean` explicitly lists `EnumDedupSound` among retired modules.
The executable checker remains, but `docs/cli.md:279`, `GoLean/EnumDedup.lean`
and `GoLean/CLI.lean:2537–2542` still call it verified and attribute the printed
set to `checkCert_slowObs`. A Lean file importing `GoLean` finds `checkCert`
but reports `checkCert_slowObs` unknown. Runtime still prints `certified=checkCert`.

No counterexample to the checker's computed set was established. The missing
justification for a proof-backed trust boundary is itself the defect. Choose
between restoring a theorem against the live checker/definitions and accurately
classifying the checker as trusted executable validation while removing the
proof claim. Kernel replay cannot replace an absent theorem. This choice affects
the trust statement and belongs to the owner; this review does not decide it.

### DC05 and DC13: distribution and behavioral promises need repair

The tree contains 82 imported-goose Go files with verbatim-source headers,
but the root Apache license is the only tracked license/notice file. Pinned
upstream goose is MIT-licensed; its copyright and permission notice are absent
from the tracked tree. Include the notice and a subtree mapping, and complete
the inventory for other copied/generated material. The supporting review gives
the exact pinned revision and reproducible searches. A gitignored dependency
checkout does not supply notices in a release source archive.

The release reader also needs one current behavioral contract. The README's
promise of reasoning without trusting a hand-written model conflicts with its
explicitly trusted interpreter/lowering. State the weakest-machine aim, modeled
gc instance, admitted divergences, refusal frontier and finite evidence together.
A zero untriaged wrong-answer count is not zero known wrong answers. Preserve
the release procedure's three predicates and give each its honest current state.

### DC06–DC07: admission and observation decoding are too permissive

The frontend's module scanner accepts malformed directives and unterminated
blocks that pinned Go rejects. Separately, it discards the minimum patch version
in the `go` directive: `go 1.26.99` exports successfully despite requiring a
toolchain newer than go1.26.5. These are distinct predicates and need distinct
controls, even if addressed in one module-admission change. Validate all accepted
syntax or refuse it explicitly; compare complete versions against the supported
toolchain. A successful subject function does not justify accepting an invalid
source context.

`observation-eq` uses permissive `Json.parse` before exact-key checks, losing
duplicate-key evidence and normalizing an unpaired surrogate. It returns equal
for those inputs and normalized observations. The robustness reviewer also found
that string observations accept `bytes:[256]`, an impossible byte value.
Use the existing strict parser and validate value domains. Neither reviewer
claims the current Go observer produces these malformed values; the finding
concerns the exposed comparison protocol and its advertised strictness.

### DC08–DC10: auxiliary raft verdicts and directory ownership

An unknown scenario or nonpositive iteration count causes `raftharness` to run
nothing and print success. Its exact `main.go` was compiled with a deliberately
failing fixture scenario: a real selection failed, empty selections passed.
The full harness could not run offline without protobuf, so the report clearly
limits this to an isolated CLI reproduction.

`runprobe.py` publishes agreement after a machine prints matching `ok` JSON
and dies by SIGKILL. `codeccheck.py` has the same unchecked machine-status pattern.
`tracereplay.py` also omits the machine return code from resumable records, so
later runs cannot establish whether stored matching output came from a completed
process. The Go leg of `runprobe --expect-stop` accepts any nonzero exit, including
unrelated compiler/dependency failure. Those adjacent paths were source-inspected;
the live SIGKILL control was run against `runprobe`.

Require agreement between process status and structured result on both oracle
and machine legs, and record status for resumed evidence. Old records lacking
status must be recomputed or explicitly refused. These instruments are outside
the main gate, so a green main gate does not repair or validate them.

These tools also recursively delete pre-existing `--out` contents. A foreign
scratch sentinel was removed even with `--keep`. The coordinator ranks DC10
higher than its supporting reviewer because an ordinary destination option can
destroy unrelated data. Refuse populated unowned destinations or create a private
child and delete only that child. Reproduce only in wholly owned scratch.

### DC11–DC12: core errors and broad warning exemptions

Scheduler readiness swallows channel-load errors and can classify an invalid
blocked configuration as `deadlock`, while directly resuming it reports `stuck`.
The probe uses a hand-built empty-heap state. **No path from admitted Go source
to this state was shown.** Its scope is core API robustness and diagnostics,
not another demonstrated source-Go wrong answer. Propagate failures or explicitly
state and enforce the required validity boundary.

`StateWf.lean`, `PoolFacts.lean` and `TableMonotonicity.lean` contain broad linter
suppressions and resource overrides. Explanatory comments do not satisfy the
current rule for a documented declaration-level exception. A configured
warning-free build cannot establish absence of suppressed warnings. Repair
warnings and narrow necessary exceptions; this does not call any sampled theorem
false or justify adding elaborate new gates.

### DC14–DC17: maintain current guidance without rewriting history

The release page says run-time `make` lacks a guard; current source and a fresh
execution show the named refusal. The living index calls shipped work pending.
Contract counts vary between 349, 366 and the actual 383. The semantics overview
misnumbers the sort issue and denies pool-level statements while listing retained
executable pool facts elsewhere. Reference setup leaves raft floating despite
the pinned-checkout description.

Live tooling still advertises a removed verified fast evaluator under `proofs/`.
Working guidance mixes current rules with historical amendments and obsolete
sandbox advice. Existing verbatim human remarks remain in tracked guidance;
the owner should decide publication/paraphrase treatment. This review does not
copy those remarks, delete decisions, or authorize history rewriting. Supporting
reports identify exact locations and bounded corrections.

### DC18: trace reruns can hide their own errors

The robustness reviewer exercised unchanged `choice-trace-corpus` and its
summarizer against the real tracer in an isolated scratch root. A previous
success kept as `results-99.tsv` was included in a later one-job run's glob.
The new wire failed, but the old success displaced its ERROR in the summary;
the runner exited 0 with one traced ID and zero errors. Separately, a malformed
old chunk made the summarizer fail with a traceback while the runner still
exited 0. Absolute output paths are also incorrectly prefixed with the root.

Use only chunks produced by the current invocation, check summary exit status,
and normalize paths once. Keep useful incremental caching only if explicit
and attributable; the current behavior looks like a fresh successful campaign.
This instrument is not the fresh differential gate, and no claim is made that
the gate itself reused those trace chunks.

### DC19: the comparator never starts under this session's locale

The final full gate exposed a new reproducibility failure:
`scripts/gen-contract:84` uses a Bash regular expression containing the Unicode
range `₀-₉`. Under inherited `LC_ALL=C.UTF-8`, Bash rejects the expression with
`Invalid collation character`, even for the ASCII name `prefix_comp`. The
comparator wrapper then exits 1 without comparing the contract. Its stale-contract
message misidentifies this failure. A minimal Bash-only probe fails in C.UTF-8
and passes in C. The supporting D7 gives complete commands.

This is a red speedbump rather than a gate failure under the existing rules.
The coordinator ran a separate locked/capped comparator with process-local
`LC_ALL=C` to distinguish the wrapper's locale defect from a contract mismatch;
that result is reported separately below. Fix the validator and its diagnostic,
then check both locales. No global locale setting or source workaround was made.

## Validation and scope

The coordinator ran `CAPPED_MEM_MAX=64G capped scripts/ci --diff` under the
primary checkout's atomic build lock, with an owner record and cleanup on exit.
Caches and temporary directories were project-local; package network resolution
was disabled. Product source stayed at the reviewed revision; review documents
were added during the run.

**Full gate: `RESULT: PASS`, exit 0, 964 seconds; one RED speedbump.** The red
is the comparator wrapper failure in DC19: Lake's comparator did not run in
this invocation. Do not describe this as an all-green validation run.

| Check | Fresh result |
|---|---|
| Every declared build target | 14 targets, successful, warning-free under current options (see DC12) |
| On-disk kernel replay | 53 GoLean modules replayed, exit 0 |
| Core totality/axiom audit | PASS |
| Eval tests | 414 successful checks |
| Frontend, lowering-table, coverage-harness tests; wire/declaration/method/equation/pin checks | PASS |
| Differential corpus | 4,045 rows: 3,784 PASS, 261 FAIL; exact baseline agreement, all failure causes classified |
| Negative corpus | 415 rows, all PASS; exact baseline agreement, subject to the runner defect DC02 |
| Unseq whole-space check and derived oracle artifacts | PASS / byte-identical |
| `lake check --inadvisably-no-sandbox` | PASS; default kernel accepted, only `propext`, `Quot.sound`, `Classical.choice`; 261.34 s, largest process 2,728 MB; 61 project modules in the exported environment |
| Comparator speedbump in full gate | FAILED at generator validation, exit 1; comparison NOT RUN |
| Separate process-local C-locale comparator | PASS, wrapper exit 0; generator check agrees with tracked files; all 383 statements compared and kernel-accepted; no sandbox; 24.92 s, largest process 1,902 MB |

The separate command was
`LC_ALL=C CAPPED_MEM_MAX=64G capped bash scripts/check-comparator`, under the
same primary-root lock. It confirms that the current contract can be checked
under that process-local locale. It does not erase the original red speedbump
or fix DC19. The checked set is 317 equations, 27 G11 statements, 13 G16
statements, 14 choice-consumption laws, 6 pool statements, 5 prefix laws and
one frame-entry statement, totaling 383.

The positive run recorded the reviewed commit with `git_dirty=false`; the
negative run recorded `git_dirty=true` because review documents had been added.
Tracked product source, tests, baselines and contract remained unchanged. Thus
the negative evidence is labeled as the worktree run, not a clean release-tag
certification. The existing gate deliberately reports known non-PASS corpus
rows against their baseline; its green is not 4,045 passing semantic examples.

The bwrap probe failed to create a NETLINK_ROUTE socket with `Operation not
permitted`; that output does not identify the denying policy and supplies no
file path for a capability query. **Nono sandbox unconfirmed; this permission
failure needs a non-sandbox diagnosis.** No sandbox capability change was
attempted; the recorded check used the prescribed no-sandbox form.

Seven sampled headline theorems had only standard Lean axioms. All 26 focused
ordinary lowering differentials in the frontend review matched pinned Go.
The subject derivation check passed against current local dependency files,
while visibly reporting their different repository revision. The README array
example succeeded. In particular, the initial suspicion that it needed
`--subject` was wrong: that fixture has `main`.

This work provides no outside-nono sandboxed claim-point result, no current
five-kernel paranoid run, no hosted CI observation, no cold network installation,
no alternate-architecture evidence, and no downstream re-pin result. The
previously documented nanoda crash remains unresolved; it was not rerun or
recast as success. A green baseline gate cannot invalidate the new counterexamples
or prove Go conformance.

All reviewers' probe directories and this run's generated corpus data, logs and
Go caches were removed after recording conclusions. The prepared build tree,
frontend binary and reference dependencies were retained. The build lock was
released after each full run. Only the seven review documents are new tracked
content; no baseline, runtime, test, contract, charter or workflow was edited.

## Known limitations to carry forward

The review did not discover or close these existing boundaries: fixed
gc/linux-amd64 realization; unproved source lowering; incomplete nondeterministic
envelopes including string-to-byte aliasing and zero-size identity; the abort
interleaving window; the open reduction from machine operations to Go access
granularity; init-time printing/pre-main observation limitations; enumeration
budgets and dedup fragment restrictions; raw-location/readout limits; and the
known sort footprint over-refusal (BUG-132). Keep them visible without treating
every refusal as a wrong answer, or a recorded wrong answer as fixed merely
because it has an issue number.

## Disposition

Every finding remains open; none is waived or represented as fixed. Duplicates
are consolidated in the DC identifiers while original reviewer identifiers
remain in the evidence. The punch list proposes repair slices, acceptance
checks and owner decisions. Fix concrete wrong-answer and false-green paths,
then establish an accurate trust and packaging contract. After repairs, run the
existing required checks and request independent review of changed surfaces.
Do not expand the gate merely to make the review look comprehensive.

A separate report-quality pass by the validation reviewer found that the draft
DC09/P09 closure criteria omitted the Go negative leg and status-less resumed
trace records. That finding was accepted: both the synthesis and punch list now
include those paths and distinguish static evidence from the executed control.
Two smaller findings were also accepted: P07b now explicitly preserves the
existing Go 1.26 language policy, and the 26 successful frontend checks are
identified as a one-off reported sample whose exact suite was not retained.
