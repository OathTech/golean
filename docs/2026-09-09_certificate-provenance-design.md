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
