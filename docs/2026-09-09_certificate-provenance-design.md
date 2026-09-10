# F8: dependency-bound certification

[AGENT] 2026-09-09. Implements the approved
[charter](2026-09-09_certificate-provenance-charter.md). This changes the
evidence required to reuse a slow observation set, not the Go semantics.

## Contract and inventory

`tools/certification.py` owns the versioned claim, dependency inventory,
validator and refresh producer. Both slow branches in `diff-coverage`, the
blocking CI check, C9 and release rule 5a use it. A successful cache read
requires equality of the saved claim and current request, equality of the
saved and current input manifests, and a matching compiled executable.
The sampled Go membership and interpreter coupling checks still run.

The claim includes the wire's SHA256, case id, entry, integer arguments,
lane, row status, literal lane parameters, exact normalized enumerator argv
and observation schema. Only the input pathname becomes `<wire>`; its bytes
remain pinned. Effective shell defaults are cross-checked against parameters;
omitted CLI defaults are covered by the CLI source fingerprint. Version 1
admits `tier=slow,engine=dedup`, requiring checker acceptance, successful
enumeration, the declared status set and cardinality. This covers all current
slow rows (one membership case, six observations). Both lanes are implemented
and tested. A future DFS, backedge or nontermination certification requires
an explicit schema extension; it cannot inherit a checked-graph claim.

Build inputs include every non-document file under `GoLean/`, `GoLean.lean`,
`Main.lean`, Lake configuration/manifest, the Lean pin, and the provenance
builder itself. The larger certification inventory adds every non-document
file under `scripts/` and `tools/`, the oracle pin, actual Go version and
Python version. Git enumerates tracked files (including missing files,
which fail) and new files, including ignored sources. Only Markdown and
Python bytecode caches are excluded. New GoLean imports must resolve within
the inventory; other project import roots and external Lake packages are
refused. Standard-library imports are covered by the installed toolchain.
The Lake configuration is restricted to the current package/target shape:
`golean` has root `Main`, the core library keeps its default roots, and extra
build/target options (including native link inputs) or a `lakefile.lean`
override require an inventory extension. Hashing the TOML alone would miss
later edits to a new external input named by that TOML.
Local sources shadowing a standard-library root are refused. Compiler,
headers, libraries and precompiled standard-library files under
the toolchain's `bin`, `include` and `lib` form a sorted path/hash aggregate.
No absolute checkout or installation path enters an identity.

Markdown, Git commit identity, artifacts, Tests and the certificate files
themselves are outside semantic identity. Tests cannot be imported into the
certified build. Documentation-only edits retain reuse. Script/tool edits
conservatively require recertification, even when an individual tool is not
on this row's execution path. This is an intentional cost, avoiding a second
hand-maintained apparatus dependency list. A new source root, dependency
package or executable data file needs an inventory extension before use.

## Binding the executable

At elaboration, `Main.lean` asks the shared inventory for the build manifest
and embeds the resulting JSON as a string literal. `golean --build-provenance`
returns that compiled value; it does not read the current checkout.
`scripts/build-certified` compares it with current inputs, invalidates only
owned Main/executable outputs when they differ, and runs Lake with `--rehash`.
Lake validates source/import traces, then builds and links the target.
The builder checks that inputs did not change and that the resulting binary
reports those inputs. Cache reads check that value again. An old executable
beside new sources therefore fails even if its wire and sampled outputs match.

The certified build refuses caller overrides for Lean import paths and
compiler/linker options. Lake's own elaboration import path is removed only
from the inventory subprocess launched by Main; it is not a public bypass.
The captured receipt includes the actual binary hash used by enumeration.
Reuse across equivalent builds compares compiled inputs, rather than requiring
byte-identical linked executables. Before/after enumeration and cache checks
also compare input manifests, the binary bytes and wire bytes for stability.

The trust assumption is the checked-in certifier, compiler/Lake build system,
and local host. This is stale-artifact protection, not a signature or a
defence against a hostile process forging compiler outputs or editing the
validator. Like other tracked baselines, a manually forged successful receipt
is a review violation. Build and enumeration exit codes are captured by the
producer, never supplied through a success flag.

## Records and deliberate refresh

The existing `.certified.tsv` keeps its observations and exact params/wire
headers. An adjacent `.certified.json` records schema, complete claim,
input manifest, observation-set digest, and producer receipt (source commit,
dirty state, timestamps, wall time, exit, binary/stats hashes and normalized
command). Duplicate fields, unknown schemas, incomplete receipts, stale input
files and changed set bytes are named refusals. No timestamp heuristic or
two-file dependency list remains in C9. CI checks that every active slow row
has exactly one record and no obsolete record survives.

For a merge train, snapshot main before merging, build at the merged tip,
and run `python3 tools/certification.py release-check --base <snapshot>`.
Exit 0 means the recorded inputs and claims did not change; exit 1 requires
the train's fresh slow run, even if the branch refreshed its own record.
Exit 2 is invalid current evidence or a failed query, also blocking release.
The command compares the previous tip's record with the validated current
record using the same inventory. An older tip without v1 metadata requires
recertification. This preserves the merged-tip obligation rather than allowing
a branch's pre-merge run to satisfy it accidentally.

Run `scripts/capped scripts/ci --slow` to generate a refresh candidate under
`artifacts/coverage/membership/<case>/certification-candidate.json`. For a
focused refresh, pass that case's normalized manifest to `scripts/diff-coverage`
with `GOLEAN_SLOW=1`. The producer first removes its old candidate, captures
the real enumeration exit, requires `certified=checkCert`, verifies exact set
equality and claim constraints, then checks stable inputs/build/wire and
atomically publishes a new candidate. Timeout, failure and changed sets
cannot publish a candidate. A fresh valid candidate does not override a
stale tracked record: that run still fails until deliberate installation.

Review the candidate and its unchanged-set result, then copy it over the
adjacent `.certified.json` and rerun the gate. Neither ordinary CI nor the
refresh command writes tracked files. For a clean-source handoff, commit the
implementation and initial metadata after a passing gate, rerun `--slow` at
that clean commit, then record that run's candidate in a records-only commit.
Metadata-only commits do not invalidate the input identity. Any observation
change is a finding requiring a changed brief, never this refresh workflow.

The record attests checked enumeration of the set. A candidate is not a
receipt for the whole differential gate: later sampled-oracle/coupling checks
can still fail, and merge acceptance still requires the entire gate green.

## Validation and costs

`scripts/check-certification` runs positive and adversarial controls, including
an actually compiled core mutation at unchanged wire and both shell cache
consumers, then checks current tracked provenance. Scratch uses worktree-local
symlink overlays and is deleted on success; failure retains a reason file.
Measured times, baseline equality and clean-source gate receipts are recorded
in the completion evidence; this note does not predict their cost.

## Review addendum (2026-09-09, [AGENT])

The independent adversarial review returned MERGE-CLEAN with small fixes.
The four dispositions below are records only; they change no bound input.
Line numbers cite `tools/certification.py` at this branch's tip.

**(a) Replay disposition (R6).** Version 1 delivers recertify-on-change
only. F8's "replay a retained proof certificate against the current checked
semantics" is OUT OF SCOPE here, because there is no retained proof object to
replay: `certified=checkCert` in the record (`:580`) is a run attestation —
the checker accepted that run's enumeration — not a re-checkable certificate,
and nothing under `baselines/certified/` can be handed back to a checker.
Rowed as a possible future extension: retain the checked state-graph
certificate and add a `replay` verb; that is an explicit schema extension,
not this refresh workflow.

**(b) Go toolchain tightening (R4).** `inputs()` hard-requires
`go version` to equal `baselines/go-oracle-pin` (`:248`). A drifted or
ABSENT Go toolchain therefore now FAILS the fast `scripts/ci` through the
certificate-provenance step, where `scripts/ci:201` (drift under
`GOLEAN_ALLOW_GO_DRIFT=1`) and `scripts/ci:206` (`go` not on PATH) still
promise only a `note`. Disclosed as a tightening in the fail-closed direction;
`GOLEAN_ALLOW_GO_DRIFT=1` no longer yields a green fast gate. The two
`scripts/ci` notes are to be reworded in the follow-up apparatus lane.

**(c) Apparatus tier consequences (R1).** `inputs()` (`:241-250`) binds
every non-`.md` file under `scripts/` and `tools/` (`:243`) — Go unit tests,
`scripts/setup-deps`, `tools/reconcile-records`, and untracked-but-ignored
stray files such as editor swap files or logs — plus
`platform.python_version()` (`:250`). Consequences, plainly: any branch that
touches any script or tool goes red until a ~20-min `--slow` run plus a
records-only record commit; a stray untracked file under `scripts/` or
`tools/` reads `added dependency files/...` (`:274`) and is RED; a host
Python upgrade invalidates every certificate; merge trains will conflict in
`baselines/certified/*.json` often. Re-pin fatigue CANNOT absorb a real
semantic change: a changed observation set refuses to mint a candidate
(`:576`). Follow-up, rowed as lane `fix/certificate-apparatus-tier`: a
two-tier manifest (semantic-critical vs. apparatus, the apparatus tier
cleared by a cheap re-attestation) or narrowing the apparatus tier to the
enumeration path. The same lane carries: R2b — `release_check` (`:657`)
resolves `--base` with a bare `git rev-parse --verify <base>^{commit}`
(`:664`) and must require it to be a strict ancestor of HEAD and ≠ HEAD;
today `--base HEAD` exits 0. R5 — slow-lane signal deaths report
`enumerator failed (exit -9)` (`:572`) instead of the named cause that
`scripts/diff-coverage`'s `signal_cause` (`:199`) gives the shell lanes.
R9 — the 61-s always-on control suite (`scripts/ci:492-497`) is an
integration test with a real oracle, a `lean` compile and enumerators inside
the fast gate; consider moving the confluent full-runner control behind
`--slow`; and the `.lake/build` symlink fixture
(`tools/test_certification.py:370-371`) has a write-through risk if Lake ever
rebuilt inside it.

**(d) Naming (R8) and the elaboration-time trust assumption (R7).**
`scripts/build-certified` builds the EXECUTABLE — it stamps the compiled
build inputs into the binary and checks the result — and never writes under
`baselines/`. The record is installed by the merge train from the reviewed
candidate (charter step 5a). R7, disclosed: `Main.lean:8-10`
(`compiledBuildInputs%`) shells out to `python3 tools/certification.py
build-identity` at elaboration with a CWD-relative path, so `lake build` now
requires `python3`, `git` and `scripts/capped` on the host. Elaborating from
another CWD either errors (`cannot bind compiled inputs`) or stamps another
checkout's inputs, which `check_build` (`:282`) then rejects — fail-closed,
but obscure.
