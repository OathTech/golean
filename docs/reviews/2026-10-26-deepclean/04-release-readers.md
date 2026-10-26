# Release readers, packaging, and documentation review

2026-10-26 · [AGENT Codex / coordinating reviewer]

Reviewed revision: `62bb461463d94c9eb4f3d003aa441db653bd77c3`.
This is a source and documentation review, with the README example executed
against the prepared frontend and interpreter. It is not a fresh network install,
a legal opinion, or a certification that every historical document is accurate.
Recommendations below are proposals, not changes to the charter or release policy.

## Audiences and method

I read the front door and living-document index as a first-time user; the trust
and semantics descriptions as a proof consumer; the coverage and release rules
as someone deciding what a green run warrants; the setup and operational
instructions as a maintainer on another machine; and the tracked source inventory
as a distributor. I checked claims against source, current baselines, the frozen
contract, and local pinned dependencies. I did not assume older review verdicts
were correct.

The tree contains 5,946 tracked paths, approximately 45.2 MB of file contents.
There are 1,607 paths under `docs/`, including 1,209 under `docs/evidence/`.
Those counts describe discoverability and maintenance cost; they are not a
finding that every old artifact should be deleted. Historical records and
test fixtures must be distinguished before any cleanup.

## D1 — High: the distributed imported-goose source lacks its upstream notice

**Evidence.** There are 82 Go files under
`Corpus/coverage/exec/imported-goose/`. Their headers identify verbatim upstream
bodies and the pinned goose revision
`3be88bbb4982f58e5813b6f0344302d5582c8e8a`. At that revision, goose's `LICENSE`
is MIT, names Tej Chajed as copyright holder, and requires inclusion of its
copyright and permission notice in copies or substantial portions. The tracked
GoLean tree contains only its root Apache `LICENSE`; searches for the upstream
copyright and the MIT permission notice find neither. A gitignored reference
checkout does not put that notice in a release source archive.

**Reproduce from the repository root:**

```sh
git ls-files '*LICENSE*' '*NOTICE*' '*COPYING*'
git ls-files 'Corpus/coverage/exec/imported-goose/*.go' \
  'Corpus/coverage/exec/imported-goose/**/*.go'
git -C deps/goose show 3be88bbb4982f58e5813b6f0344302d5582c8e8a:LICENSE
git grep -n -F 'Copyright 2019 Tej Chajed' 62bb4614 -- .
git grep -n -F 'Permission is hereby granted, free of charge' 62bb4614 -- .
```

The last two searches inspect the reviewed revision, so this report's own search
commands cannot become matches; they return no matches, exit 1. The file
`Corpus/coverage/exec/imported-goose/semantics/type-equality/main.go:1`
is a small concrete example of the copied-source provenance.

**Impact.** The front-door Apache-only description is incomplete for someone
redistributing the source. This is a concrete missing-notice finding, not a
general allegation about all third-party material.

**Proposed repair.** Include the pinned MIT notice and a short mapping to the
imported subtree, and qualify the root license summary. Also inspect the
protobuf-derived generated codec and copied raft material for their respective
notice requirements; their derivation provenance is present, but this review has
not established the exact notice set needed for every generated function.
Acceptance: inspect a `git archive` of the proposed release and find the required
notices without fetching `deps/`. Do not add an elaborate licensing gate.

## D2 — High for release claims: the supported behavioral claim is still not a usable contract

**Evidence.** `README.md:34–44` offers execution and reasoning without trusting a
hand-written model, while describing the hand-written interpreter and lowering
as trusted. `README.md:157` starts with the weakest-permitted-machine claim and
qualifies it only by saying it is incomplete. `docs/release.md:35–49` requires
three separate predicates, including a named supported profile and an argued
behavioral envelope. It still calls the profile ruling pending. The current
baseline contains **4,045 rows: 3,784 PASS and 261 FAIL**. The tracked untriaged
list contains 14 entries; its `wrong-answer` classification counts unexplained
failures, not all known wrong behavior. A zero there cannot establish the second
release predicate.

**Impact.** A newcomer can reasonably overread a green release as a conforming
Go implementation or a proved Go model. A proof consumer needs to know what
programs and observations are covered, which assumptions they inherit, and which
claims the Lean proofs actually establish. A list of dated amendments is not a
substitute for that contract. The new pointer-identity wrong answers in this
review make an unqualified zero-known-wrong-answers statement false today.

**Reproduce:** read the cited paragraphs together with
`baselines/native-full.tsv`, `baselines/untriaged-ids`,
`docs/2026-08-11_latitude-inventory.md` §11, and the `Status:`/`Cases:` fields of
`docs/BUGS.md`. Count baseline rows, excluding the header and comments:

```sh
awk -F '\t' '!/^#/ && $1 != "result" {n[$1]++}
  END {for (k in n) print k, n[k]}' baselines/native-full.tsv
```

**Proposed repair.** Put a short, current release contract near the front door:
Go 1.26 at gc go1.26.5/linux-amd64, admitted features and deliberate refusals,
known admitted divergences, concurrency/access-granularity limitations,
finite-test evidence, and the exact scope of the kept theorems. Describe the
model as explicit and inspectable, not as eliminating the need to trust a model.
Report the three predicates separately, with honest false/unknown states where
appropriate. Naming a profile or changing a release criterion is the owner's
decision; this report does not silently settle either.

## D3 — Medium: maintained pages contradict shipped behavior and one another

These are living documents, so their dated-record exception does not explain
the contradictions:

| Location | Current text or state | Source-grounded correction |
|---|---|---|
| `docs/release.md:160–164` | Run-time-sized `make` still dies under the cap; guard awaits approval | `Machine.lean:1702–1703` now refuses over-budget footprints; BUG-131 is fixed and has two deliberate refusal rows |
| `docs/README.md:70–73` | Seeded heap and `uintptr` repair are pending design gates | Seeded CLI support is documented in `docs/cli.md`; `IntKind.uintptr` and its repaired decoder are shipped, and the backlog records the landing |
| `README.md:142` | 349 contract theorems | `Contract/Challenge.lean` and `comparator.json` contain 383 |
| `docs/release.md:96` and `docs/semantics-overview.md:300` | 366 contract theorems | Same current count: 383 |
| `docs/semantics-overview.md:291` | Sort race-footprint issue identified as BUG-131 | The sort issue is BUG-132; BUG-131 is the allocation-budget guard |
| `docs/semantics-overview.md` §10 | No pool-level statement is in the build | Its own §5 lists kept executable pool statements; distinguish the retired pool relation from the retained executable facts |
| `docs/spec-sources.md` repository table and replication note | covmap has no public URL; `lake` pseudo-names remain usable | `scripts/setup-deps:106` supplies a URL; its argument checker rejects the removed pseudo-name |
| README cold-build comment and older operational guidance | 64 GiB described as a measured necessity | `docs/operational-lessons.md:783` records a later cold build peaking at 3.2 GiB aggregate; a 64 GiB cap is not a measured 64 GiB requirement |

**Impact.** Users avoid repaired features, chase obsolete instructions, or
misunderstand what was checked. The theorem-count drift is less serious than the
behavior and trust-scope drift; do not give every typo the same severity.

**Reproduce:**

```sh
python3 -c 'import json; print(len(json.load(open("comparator.json"))["theorem_names"]))'
rg -n '^theorem ' Contract/Challenge.lean
rg -n 'make-footprint-budget-runtime|BUG-131|BUG-132' \
  docs/BUGS.md scripts/machine-causes.tsv
rg -n 'cap \* elemLeaves > arrayFootprintBudget' GoLean/GoCore/Machine.lean
```

I also freshly lowered the existing `arrays/materialization-budget-runtime`
fixture with `--subject` and ran `makeOverBudget` through the prepared interpreter
under `capped`. It returned status `unsupported`, exit 1, naming the 33,554,432
leaf request and 16,777,216 leaf budget. The stale release limit is contradicted
by both source and current execution.

**Proposed repair.** Update maintained descriptions from the current code and
retain historical records as history. Prefer a link to the generated contract
list over copying its count into multiple pages. Refresh memory guidance only
from a new controlled measurement at the release revision; this review did not
measure a cold build. No standing cap rule should be weakened on the strength of
a documentation inconsistency.

## D4 — Medium: the advertised reference setup does not pin every dependency it names

`README.md:80` calls goose, go, and raft pinned reference checkouts.
`scripts/setup-deps:103` explicitly leaves raft floating. Meanwhile
`raftsubject/README.md` and `tools/raftsubject/derive.py` identify a particular
source revision, and `raftharness/go.mod` replaces the raft module with that local
checkout. A new user can get a different harness dependency by running the same
documented command on another day.

The derivation's upstream-file digests are a real safeguard: this is **not** a
finding that it silently accepts arbitrary changed source. The validation
review separately inspected that check. The narrower defect is an inaccurate
setup promise and a floating dependency for a shipped companion harness.

**Reproduce:** inspect the setup table, `raftharness/go.mod`, and
`PINNED_RAFT_REV` in `tools/raftsubject/derive.py`; no network fetch is needed.

**Proposed repair.** Pin the reference used to reproduce the released subject
and harness, or label the floating research checkout distinctly and give the
exact reproducible setup separately. Supply an offline-cache prerequisite for
the protobuf-dependent companion tools. Acceptance: an independent user can
identify all exact required revisions from tracked files before running a tool.

## D5 — Medium editorial/privacy decision: tracked guidance preserves verbatim owner remarks

`CLAUDE.md:28–73` contains attributed verbatim human statements. Other historical
records do too. I have not copied those statements into this review or changed
the files. Their existence conflicts with the requested practice of keeping
private, conversational text out of permanent records; whether particular
older statements were expressly approved for publication is not established by
this review.

**Proposed disposition.** The owner should decide which existing passages remain
and which current-tree passages should be paraphrased before release. Do not
rewrite history or silently delete attributed decisions. This is separate from
whether the policy expressed by a passage remains in force.

## D6 — Medium maintenance issue: the working instructions mix current rules with obsolete operations

The 323-line charter contains superseded scope statements, historical quotations,
dated landing explanations, and detailed gate timing inventories alongside the
current rules. `docs/architecture-rules.md` keeps historical instructions followed
by amendments. The maintained `docs/agent-sandbox.md` advises leaving temporary
files for OS cleanup, contains an old virtual-memory-limit recipe, and suggests
an escalation path for network failures that does not describe the present nono
workflow. Current session rules correctly take priority, but a future maintainer
following only those pages gets conflicting guidance.

**Proposed repair.** Propose a concise current charter and operational page to
the owner, linking to design history instead of embedding it. Keep provenance in
decision records; make actual standing rules easy to find. This review does not
authorize a charter rewrite, a policy change, or deletion of historical evidence.

## D7 — Medium: the comparator wrapper fails under a normal UTF-8 locale

This finding came from the coordinator's fresh full gate, after the initial
documentation review and report-quality audit. Under inherited
`LC_ALL=C.UTF-8`, `scripts/gen-contract:84` cannot compile its Bash regular
expression `^[A-Za-z0-9_.?!₀-₉]+$`: Bash reports `Invalid collation character`.
It rejects the ordinary ASCII theorem name
`GoLean.GoCore.ExecutionStatement.prefix_comp`. Thus `scripts/check-comparator`
exits 1 before running Lake's comparator. Its subsequent message blames a stale
contract or incomplete challenge, which is not the demonstrated cause.

The full `scripts/ci --diff` run ended with `RESULT: PASS`, exit 0, and exactly
one red speedbump: the comparator. This is the documented gate/speedbump split,
not a claim that the comparator passed. Runtime source and contract files were
unchanged.

**Minimal reproduction, no Lean build required:**

```sh
LC_ALL=C.UTF-8 bash -c \
  'name=GoLean.GoCore.ExecutionStatement.prefix_comp; [[ "$name" =~ ^[A-Za-z0-9_.?!₀-₉]+$ ]]'
LC_ALL=C bash -c \
  'name=GoLean.GoCore.ExecutionStatement.prefix_comp; [[ "$name" =~ ^[A-Za-z0-9_.?!₀-₉]+$ ]]'
```

Observed: UTF-8 case exits **2**, with the collation error; C case exits **0**.
The coordinator also ran the actual wrapper with process-local `LC_ALL=C` under
the same cap/lock discipline: `gen-contract --check` agreed with tracked files,
and all 383 statements passed the comparator and kernel (wrapper exit 0,
comparator 24.92 s, no sandbox). The main review records that follow-up separately
from the full gate's red result. No machine-global locale was changed.

**Proposed repair.** Make the accepted-character check locale-independent without
accidentally broadening it, for example with explicit allowed Unicode characters
instead of a locale-sensitive range. Distinguish validator failure from an
invalid name and from a stale generated contract. Acceptance: actual generator
check and comparator run in both C and C.UTF-8; valid ASCII/subscript theorem
names pass and deliberately invalid names still refuse. A process-local
workaround is diagnostic evidence, not a completed source fix.

## What held, and limits of this pass

- The README's actual array example lowers and executes correctly with the
  prepared tools, producing integer 6 and status `ok`. The initial suspicion
  that it needed `--subject` was wrong: that fixture has `main`.
- The front door states that lowering has no correctness theorem and that the
  platform is gc/linux-amd64. The problem is consistency and prominence, not a
  total absence of qualifications.
- The CLI document describes exit codes, choice defaults, refusals, and seeded
  observations in useful detail; behavioral counterexamples to its strict-input
  claim are in the independent frontend review.
- The release procedure separately records predicates and already discloses
  the unavailable sandboxed run and failed nanoda check. This review does not
  count a no-sandbox run as a completed release claim-point gate.
- A simple literal-link scan found no confirmed broken Markdown destination in
  the sampled living pages. Its apparent failures were syntax examples, not
  real links, and are not findings.
- No fresh network install, alternate OS/architecture build, package-registry
  publication, downstream consumer upgrade, or remote CI observation was done.
  Optional missing metadata such as a citation file or contribution guide is a
  usability opportunity, not a release blocker without an audience need.

## Suggested order

Address the concrete missing notice and behavioral/trust failures first. Then
publish one accurate release contract and synchronize the living pages. Keep
historical cleanup and a shorter charter as deliberate, separately approved
work; do not turn a deep clean into a mass deletion or a new collection of gates.
