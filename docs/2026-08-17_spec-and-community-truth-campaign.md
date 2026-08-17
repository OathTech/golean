# Spec-and-community truth campaign — plan (2026-08-17)

Status: PLAN (no execution yet). Lane: `spec-truth` (docs-only until P2).
Companion doctrine: `docs/2026-08-11_essence-of-go-doctrine.md` (the two
bounds), `docs/2026-08-11_latitude-inventory.md` (the per-point census).

## 1. Why this campaign

The differential against gc is the LOWER bound and is well-mechanized:
corpus, baseline pinning, `scripts/ci --diff`. The UPPER bound — what a
conforming Go implementation may ever do — is argued from the spec text,
the memory model, proposal archaeology, and cross-implementation
observation. The doctrine doc already ranks these evidence classes
(§"Evidence classes for the upper bound") but today they are consulted
**ad hoc, from memory, uncited and unpinned**. Nothing checks that a
latitude-inventory envelope argument cites real spec text; no pinned
copy of the spec exists in the repo; the community record (spec
clarifications, gc-vs-spec bug reports) has never been mined.

This campaign makes the upper-bound evidence classes first-class:
pinned, citable, lintable, and mined — the same treatment the lower
bound already gets. Three additional payoffs fall out:

- **Spec and gc bugs become findable by us.** Every mature
  formalization effort surveyed below (SpecTec, JSTAR/JEST, CH2O,
  Cerberus) found errors in the standard it formalized. A divergence
  ledger gives those findings a home and an upstream path.
- **The spec's own examples are free conformance vectors** written by
  the spec authors — a corpus slice we have never extracted.
- **The versioning question gets answered.** Go's semantics are
  versioned (the `go` directive in go.mod selects language semantics
  since 1.21; the 1.22 loop-variable change is a real semantic change
  gated on it). GoCore currently models an unpinned "Go"; the machine
  needs a recorded language-version stance.

Non-goal, stated up front: the spec does not become the model of
record. The machine is the artifact; spec/community/prior-art are
evidence lanes feeding its upper bound. We are *consumers* of the Go
spec, not its authors — no SpecTec-for-Go spec-generation project.

## 2. Source inventory and acquisition (P0)

All checkouts go to gitignored `deps/` via new rows in
`scripts/setup-deps` (existing pins-table format, fail closed,
`--from` for offline). Non-git artifacts (PDFs) go to gitignored
`deps/papers/` with a tracked manifest (`docs/spec-sources.md`: URL,
DOI, sha256) so any clone can replicate. Exact revs are pinned during
P0 execution; the table below records the source and why.

### Primary sources (normative or near-normative)

| Source | Where | Why |
|---|---|---|
| The Go Language Specification | `golang/go` → `doc/go_spec.html` (rendered: go.dev/ref/spec) | THE upper-bound text. Pin the whole `golang/go` repo at a release tag → one pin covers spec + memory model + test suite + go/types. The file's **git history is itself a source**: every clarification commit marks a spot the text was once ambiguous, usually with an issue link. |
| The Go Memory Model | same repo, `doc/go_mem.html` (go.dev/ref/mem; 2022 revision) | Governs the concurrency envelope. Rationale: Russ Cox's memory-model series (research.swtch.com/gomm). |
| gc's semantic test suite | same repo, `test/` (thousands of small programs, many named `issueNNNNN.go`) + `src/go/types/testdata` + `src/internal/types/testdata` | A curated historical map of gc semantic bugs — each issue-tagged test is a spec-vs-gc divergence that actually happened. Corpus-seed goldmine. |
| Release notes, language-change sections | same repo, `doc/go1.*.html` / go.dev/doc/go1.x | The delta record between spec versions; the versioning stance (§5.4) is decided against this. |
| Proposal + issue archaeology | github.com/golang/proposal (git); golang/go issues labeled `Proposal`, `LanguageChange`, `Documentation` (mined via `gh`, snapshots into `deps/` as JSONL) | Committee-intent reconstruction — the doctrine doc already names this lane "Cerberus-style". |

### Community / de-facto sources (lower authority, explicitly so)

| Source | Where | Why |
|---|---|---|
| Go 101 (Tapir Liu) | github.com/go101/go101 | The community's most detail-obsessed catalog of corner cases and gc-vs-spec quirks. Not authoritative; excellent divergence-ledger *seed* — every claim gets independently checked against spec + oracle before entering the ledger. |
| gccgo (gofrontend), TinyGo | github.com/golang/gofrontend, github.com/tinygo-org/tinygo | Cross-implementation observation (doctrine §evidence-classes). A behavior two independent implementations exhibit is strong envelope-membership evidence; a behavior they *disagree* on is a located latitude point. Caveats recorded per-implementation: gccgo lags the spec; TinyGo diverges deliberately in places — neither is an oracle, both are witnesses. |
| golang-nuts / golang-dev threads | linked from ledger entries as URLs, not mirrored | Where spec ambiguity is litigated in public. Pointer-only; no bulk mirror. |

### Prior-art formalization efforts (reading copies)

`deps/spectec` (github.com/Wasm-DSL/spectec), `deps/esmeta`
(github.com/es-meta/esmeta); papers to `deps/papers/`: SpecTec
(PLDI 2024, doi 10.1145/3656440), JISET (ASE 2020), JEST (ICSE 2021),
JSTAR (ASE 2021), JSAVER (ESEC/FSE 2022), JSCert/JSRef (POPL 2014),
CH2O (Krebbers, thesis + papers), Cerberus (PLDI 2016 + de-facto-C
papers), Sail/RISC-V golden-model note, Featherweight Go
(arXiv:2005.11710, OOPSLA 2020), Fava/Steffen/Stolz "Operational
semantics of a weak memory model with channel synchronization",
Sulzmann/Wehr dictionary-passing FG papers. Already in `deps/`:
goose/perennial, gobra (Go verifiers — compare their spec-fidelity
stances too).

## 3. Prior-art study (P1) — what each effort is FOR

One dated reading note per effort (or cluster), each ending in an
explicit **adopt / adapt / reject** verdict recorded against our
mechanisms in §4. Parallelizable across reading lanes. The hypotheses
to test, per effort:

- **SpecTec (Wasm)** — single DSL source generating typeset prose,
  formal rules, and a meta-interpreter that passes 100% of the official
  test suite; found errors in shipped spec text and in five in-flight
  proposals. *Expected verdict:* reject the spec-generation frame (we
  don't own Go's spec); adopt the **coverage discipline** — their
  "interpreter ⟷ official test suite" loop is our differential gate,
  and their "formalization finds proposal bugs" is our divergence
  ledger with an upstream path.
- **ESMeta line (JISET → JEST → JSTAR → JSAVER, KAIST PLRG)** —
  mechanized spec *extracted* from ECMA-262's algorithmic prose, then:
  JEST does N+1 differential testing where a divergence is classified
  as *engine bug or spec bug* (found both); JSTAR type-checks the spec
  itself (92 type bugs across 864 spec versions); plus PLDI 2023
  feature-sensitive coverage for conformance-test synthesis.
  *Expected verdict:* extraction doesn't transfer (Go's spec is prose,
  not pseudocode — there is nothing to extract an interpreter from);
  adopt **JEST's divergence-classification discipline** (a red
  differential case is not automatically our bug — the ledger needs a
  `gc-bug` and a `spec-bug` verdict, not just `ours`) and study their
  **coverage-guided test synthesis from the mechanized semantics** —
  generating Go programs from GoCore's own branch structure is the
  inverse of grossmith's seed-generation and complementary to it.
- **JSCert/JSRef** — hand-written Coq semantics + extracted
  interpreter, with "eyeball closeness": every rule annotated with the
  prose clause it mirrors. *Expected verdict:* adopt — this is the
  clause-anchor scheme (§4.1) in its original form; ours is the same
  idea one level up (anchors on latitude/envelope arguments and
  interpreter regions, not per-rule, since our semantics is not
  prose-shaped).
- **CH2O + Cerberus (C)** — the closest analog of "formalize a prose
  standard that deliberately underspecifies". CH2O treats unspecified
  evaluation order as genuine nondeterminism (= our envelopes) and fed
  defect reports back to WG14 (= our upstream loop precedent).
  Cerberus's de-facto-vs-ISO distinction *is* our two-bounds doctrine
  independently reinvented — including surveys of practitioners as a
  rigorous community-evidence method. *Expected verdict:* adopt the
  defect-report workflow and the de-facto/ISO vocabulary alignment;
  read their evaluation-order treatment against our E1–E6 latitude
  entries specifically.
- **Sail / RISC-V** — a formal model that the standards body adopted
  as its official golden model. *Expected verdict:* endgame framing
  only; records what "the community recognizes the machine" would
  even mean. No near-term action.
- **Featherweight Go + successors** — core calculus that shaped Go's
  generics; dictionary-passing papers note FG's dynamic semantics
  differs from what gc implements. *Expected verdict:* park until the
  generics arc; its method-resolution treatment becomes a primary
  source then. The FG-vs-gc dynamic-semantics gap is itself a
  divergence-ledger entry.
- **Fava/Steffen/Stolz** (Go-inspired weak memory with channels, K
  mechanization) — read when the memory-model lane opens (§5.5);
  records prior art on exactly our channel-synchronization envelope.

## 4. Integration mechanisms — how sources change the repo

These are the campaign's actual products. Each is small, fail-closed,
and lands via the normal merge protocol.

### 4.1 Clause anchors + lint (the citation spine)

A spec citation becomes a machine-checkable object: `spec#Anchor`
(e.g. `spec#Order_of_evaluation`, `spec#Select_statements`) resolving
into the pinned `doc/go_spec.html`, plus `mem#...` for the memory
model. Then:

- The latitude inventory's envelope arguments, the
  simplifying-assumptions register, and new corpus cases that pin
  spec-forced behavior carry anchors.
- `scripts/check-spec-anchors` verifies every cited anchor exists in
  the pinned spec copy (fail closed, wired into `scripts/ci`'s
  preflight). Anchor spelling drift across spec versions is caught at
  re-pin time by the same lint.

This is deliberately *shallow* — it checks citations resolve, not that
they support the claim. Claim-support stays with the audit dimension
("nondeterminism-envelope fidelity ... argued against the Go SPEC
TEXT"), which the anchors make executable-adjacent: an auditor can now
jump from claim to pinned text in one step.

**Candidate implementation: covmap (see §8).** OathTech's covmap is a
strictly stronger mechanism than the bare anchor lint — content-hashed
segments detect when the *cited text itself* changed at a re-pin, not
merely whether the anchor still exists. §8 records the assessment and
the feature gaps; the P0 pilot decides which implements 4.1.

### 4.2 Spec-example corpus extraction

`doc/go_spec.html` contains hundreds of `<pre>` example blocks written
by the spec authors. Extractor script → classify each block
(runnable program / fragment needing a standard wrapper / declaration
-only / intentionally-invalid), wrap the wrappable, and land them as a
corpus slice with anchors back to their clauses. Intentionally-invalid
examples become negative cases (must fail to compile — checks the
frontend's rejection behavior, which nothing exercises today).
Expected yield: a few hundred cases; every red is triaged before
landing (fail-closed classification per house rules — a case the tool
can't run is visibly blocked, never skipped). Same treatment later for
`golang/go/test/` (much larger; issue-tagged; start with a curated
sample, not a bulk import).

### 4.3 The divergence ledger (tracked, dated)

`docs/spec-divergence-ledger.md` — one entry per known or discovered
gap between spec text, gc behavior, and/or our machine. Fields: id,
sources (anchors + issue/CL links), kind — one of `spec-ambiguity`,
`spec-bug`, `gc-bug`, `gc-divergence-tolerated` (de-facto pin),
`ours` — our stance, which bound it affects, corpus case ids, upstream
status. Seeds, in order of yield per effort:

1. `git log --follow doc/go_spec.html` — every clarification commit,
   with its issue.
2. `golang/go/test/issue*.go` sampled by area we model.
3. Go 101's details lists, each independently verified before entry.
4. Our own latitude inventory's `known ≠ gc` entries (E3/E5 already
   are ledger entries in spirit — migrate them in).

The ledger is also where JEST-style verdicts live: a differential red
that survives triage as *gc's fault* or *the spec's fault* is a
first-class outcome, not an embarrassment to make green.

### 4.4 Language-version pin (a decision, not a tool)

Record in the doctrine doc: **GoCore models the Go X.Y language**
(proposal: the latest stable at pin time, with the 1.22 loopvar
semantics explicitly called out since it is the one recent change that
moves observable sequential behavior). The corpus's go.mod `go`
directive, the spec pin, and the oracle toolchain version must agree —
one preflight check. Version-skew behaviors (pre/post 1.22 loopvar)
are ledger entries, not corpus ambiguity.

### 4.5 Cross-implementation observation lane (optional, decide at P5)

A `scripts/diff-one`-style runner against gccgo and/or TinyGo for a
curated corpus slice. Divergences between implementations are located
latitude evidence for the inventory; agreements are envelope-membership
witnesses. Cost: toolchain install + result-classification caveats per
implementation. Not a gate — an evidence generator. Decide after P1
whether the yield justifies it; record the decision either way.

### 4.6 Upstream feedback loop (policy)

When the ledger accumulates a confirmed `spec-bug`/`spec-ambiguity` or
`gc-bug`: file upstream (golang/go issue), with Mike's explicit
sign-off per filing (outward-facing action). CH2O/JSTAR precedent says
a formalization effort that files good reports earns standing; that is
also the long game of §3's Sail note. Ledger tracks upstream status.

## 5. Phasing

Sized S/M/L; each phase is a mergeable slice with the usual gate
(docs-only slices: `GOLEAN_ALLOW_NO_DIFF=1` per CLAUDE.md; runtime- or
corpus-touching slices: `--diff` and deliberate, explained re-pins).

- **P0 — acquire & pin (S).** setup-deps rows (`go` at a release tag,
  `go101`, `spectec`, `esmeta`, gofrontend/tinygo as `named`),
  `deps/papers/` manifest, `docs/spec-sources.md` pointer doc. Verify
  spec-anchor stability across two adjacent Go releases while at it
  (informs 4.1's lint strictness).
- **P1 — prior-art reading notes (M, parallelizable).** Six dated
  notes per §3, each with adopt/adapt/reject verdicts. Reading lanes
  are docs-only and disjoint — safe to parallelize per the worktree
  discipline.
- **P2 — anchors + lint (M).** Mechanism 4.1; retrofit the latitude
  inventory and assumptions register with anchors (that retrofit is
  itself a fidelity re-read of every envelope argument — the real
  point; the lint is the cheap byproduct that keeps it true).
- **P3 — spec-example corpus (M).** Mechanism 4.2. NOTE: touches
  `Corpus/` + `baselines/` — must run as the single lane owning them
  (worktree-discipline rule), sequenced against any semantic-core arc.
- **P4 — divergence ledger seeded (M).** Mechanisms 4.3 + 4.4. History
  mining is scriptable; verification of each candidate entry is the
  work. Ship with ≥20 verified entries or a recorded reason why fewer.
- **P5 — decision point with Mike (S).** With P1–P4 evidence in hand:
  cross-implementation lane (4.5)? machine-side conformance-test
  synthesis (JEST/PLDI-2023-style, coordinated with grossmith so the
  two generators don't duplicate)? memory-model deep-dive (Fava et
  al., research.swtch.com/gomm) beyond current doctrine? upstream
  filing cadence (4.6)? Each gets a written decision.

P0+P1 first and cheap; P2 before P3/P4 so the ledger and corpus slices
are born citing anchors rather than retrofitted. P3 and P4 are
independent of each other.

**Branch topology (Mike, 2026-08-17): `spec-truth` is the campaign's
integration branch.** Sub-lanes (P1 reading notes, etc.) fork as
sub-worktrees off the `spec-truth` tip — not off `main` — so they see
the plan without a `main` landing; they own disjoint files, rebase
onto `spec-truth`, and land into it ff-only (the main-merge
discipline, applied one level down; snapshot rule per sub-worktree;
`deps/` via `setup-deps --from` the spec-truth worktree). `main`
landings happen at milestones via the unchanged merge protocol —
first one proposed after P0 + pilot + P1, so the audit surface stays
reasonable. P3/P4 fork from `main` after that landing, not from the
aged campaign branch: baseline re-pins and `Corpus/` ownership want a
fresh base, and drift in `scripts/setup-deps` is the known conflict
file with other arcs.

## 6. Risks and refusals

- **Authority inversion.** The spec is upper-bound evidence, not the
  model of record; a spec sentence never overrides a differential red
  without a ledger entry explaining which of the two is wrong. The
  two-bounds doctrine stays the frame; this campaign only feeds it.
- **Community sources are unverified by default.** Go 101 / mailing
  lists seed hypotheses; nothing enters the ledger or corpus without
  independent spec+oracle verification.
- **Scope creep toward spec-generation.** Building a Go SpecTec is
  explicitly out; anchors + ledger + extracted examples are the whole
  mechanization surface.
- **Corpus ownership races.** P3 is the known conflict point with
  mainline semantic arcs; it is sequenced, not parallelized.
- **Anchor rot across spec versions.** Mitigated by the pin (one
  version at a time) and the lint at re-pin; never cite the live
  go.dev page.

## 7. Open questions for Mike (pre-P0)

1. Language-version pin: latest stable Go at pin time — agreed?
2. Issue-tracker snapshots via `gh` into gitignored JSONL: fine, or
   pointer-only (URLs in the ledger, no mirror)?
3. P5's upstream-filing policy: per-filing sign-off is assumed; any
   standing constraints (e.g. never file from this identity)?
4. Scale check on P1: six reading notes ≈ six worker-agent lanes
   (Fable per the worker-model rule) — or trim the list?
5. covmap (§8): ~~CIP timing~~ DECIDED (Mike, 2026-08-17): CIP drafts
   are written AFTER the pilot — the pilot may surprise us in ways
   that change the requests. (Handover of any draft to the covmap
   repo remains a separately signed-off action.)

## 8. Addendum (2026-08-17): covmap assessment

github.com/OathTech/covmap (Rust, v0.3 experimental, Apache-2.0) — a
CLI that partitions text files into content-addressed **segments**
(`(file, range, label)`, identity = first 64 bits of sha256(content),
labels/names outside the hash), records **connections** (many-to-many
links between two coverings, cross-repo), and reports **drift** when
either side's bytes change — repairable via `recut`/`recut --remap`
(boundaries carried through unchanged regions, `@name`s survive),
terminal `broken` state healed only by explicit relink or drop.
`iter` freezes a covering into a resumable per-segment worklist.
Assessed from README, SKILL.md, GLOSSARY.md, and — since 2026-08-17 —
the live checkout at `deps/covmap` (rev `2978393` at assessment time;
internal repo, so its setup-deps row gets a `-` URL, `--from`
required). §8.3's gaps are grounded to `file:line` in that rev. Not
yet *run* — that is the pilot.

### 8.1 Verdict: strong fit — candidate backbone for 4.1/4.2/4.3

The design decisions are the ones we would have asked for: content-only
hashes (relabeling never causes drift), broken-as-terminal (fail
closed, heals only explicitly), plumbing-first CLI, agent-oriented
workflow doc. Where it slots in:

- **4.1, upgraded.** Covering A = pinned `doc/go_spec.html` cut at
  section boundaries, `@name`s = spec anchors; covering B = latitude
  inventory + assumptions register (+ interpreter regions later);
  connection = "this envelope argument rests on this clause text". At
  a spec re-pin: `recut --remap` on side A, and the drift/broken
  report **is** the re-review worklist — which the bare anchor lint
  cannot produce (an anchor can survive a re-pin while the text under
  it changes meaning; content hashes catch exactly that).
- **P2 retrofit.** `iter` over the latitude-inventory covering is the
  natural worklist for the envelope-argument re-read, resumable across
  agent lanes.
- **4.2/4.3 coverage accounting.** Corpus cases and ledger entries
  link to their clause segments; "which spec sections have zero
  witnesses" is an unlinked-segment query — the SpecTec-style
  coverage number, for free.
- **Beyond this campaign** (noted, not scoped): paper-to-proof
  alignment is a listed covmap use case — `compat/verdi` ↔
  `deps/verdi` theories, raftharness ↔ `deps/raft` are the same shape.

Doctrine fit: covmap is bookkeeping/speedbump class, not trust
surface — a broken link is a review prompt, never a correctness claim.
And it is OathTech's own tool, so the trust-tools never-modify rule
does not apply; feature work on it is in-family.

### 8.2 The workflow it enables (target state)

spec re-pin (deliberate, §4.4) → `recut --remap` on the spec covering
→ `status` lists changed clause segments + every connected envelope
argument / corpus case / ledger entry → `iter` worklist for the
re-review → all links healed = re-pin complete. Drift events are rare
and meaningful because the spec side only changes at re-pins.

### 8.3 Feature gaps — GROUNDED in `deps/covmap` @ `2978393`
(ordered; 1–3 are adoption blockers)

Code-verified 2026-08-17; each cite is to that rev. Two of the seven
originally-hypothesized gaps dissolved on reading the code (see the
"already right" list below) — the survivors:

1. **`status` exit code + machine-readable output.** `cmd_status`
   returns `Ok(0)` unconditionally (`src/cli.rs:357` ff., the final
   `Ok(0)` after the connections loop) — drift and broken-link counts
   are printed but never reflected in the exit status, and there is no
   JSON/TSV mode anywhere in `src/`. Not wirable into `scripts/ci`
   preflight as a fail-closed gate; this is the difference between a
   tool we run by hand and a gate. (Precedent in-tree: `iter next`
   already exits non-zero on exhaustion "so a shell loop stops",
   `src/cli.rs:2207` — the same contract on `status` is the ask.)
2. **Worktree-safe, rev-aware cross-repo references.** The connection
   file format stores `# target_repo=<abs/path>` (`src/connection.rs:4-8`,
   `:40`), and `cmd_status` builds the target `Repo` straight from
   that string. Hostile to the worktree-per-lane discipline (every
   lane resolves a different absolute path — a connection created in
   one lane is broken in all others and in every fresh clone) and
   unpinned (status compares against whatever bytes are on disk; no
   rev is recorded anywhere). Wanted: git-remote-style repo aliases
   resolved via per-checkout config, plus an optional recorded rev
   with loud mismatch failure.
3. **Structural segmentation.** `split` takes exactly one cut:
   `split <covering>:<hash> <line> [<label_top>] [<label_bot>]`
   (`src/cli.rs:1397-1402`), addressed by segment hash — so scripted
   bulk cutting must re-resolve addresses after every call (each
   split re-hashes the halves). No regex anywhere in `src/`
   (consistent with the sha2-only dependency policy). Cutting ~100+
   spec sections per spec version this way is toil. A format-agnostic
   plumbing form suffices: split-at-regex with `@name` from a capture
   group (for `go_spec.html`: cut at `<h[234] id="(...)">`, name from
   the id — which also makes 4.1's anchor names fall out
   automatically), or a batch form taking a precomputed cut-list file.
4. **Typed links.** `Link { a, b, note }` — free-text note only
   (`src/connection.rs:20-24`). We want kinds (`cites` / `witnesses` /
   `disputes` / `implements`) filterable in status/coverage queries.
   Note-conventions are a workable stopgap; first-class link labels
   make the coverage claims queryable.
5. **Coverage breakdown + emission.** Downgraded from the original
   hypothesis: per-connection coverage *already exists* — `status`
   prints distinct-resolving-endpoints over covering size, source and
   target ("the theory-defined source/target coverage",
   `src/cli.rs:~430-452`), and `ls --linked|--unlinked [--label]`
   lists the unmapped remainder (`src/cli.rs:1033-1052`). Remaining
   ask folds into 1 and 4: machine-readable emission, and breakdown
   by link type once types exist.
6. **Bulk link plumbing.** `link` is one pair per call
   (`src/cli.rs:1730`); hundreds of corpus-case→clause links want a
   stdin-TSV batch with all-or-nothing validation. A shell loop works
   meanwhile — lowest priority.

Resolved positively by the code (no request needed): **store
reviewability** — coverings and connections serialize as sorted text
(`src/connection.rs:110`, `src/covering.rs:435,854`), so a tracked
`.covmap/` is deterministic and git-diffable; single-lane ownership
covers the merge story. Whitespace/markup normalization was considered
and dropped: cosmetic churn only bites at re-pins, which are rare and
deserve review anyway.

### 8.4 Deliverable: CIP drafts (the grounded request set)

covmap has an in-repo proposal process (`cips/0001-iterators.md` …
`0004-content-only-hash.md`) — requests to its developers are
delivered in that format, not as an issue list. **A campaign outcome
is a set of CIP drafts** covering §8.3 items 1–4 (6 as a paragraph in
one of them), each grounded in: the `file:line` evidence above, the
pilot's concrete transcript (the exact command sequence our workflow
needs and where it breaks today), and the workflow story of §8.2.
Drafts live at `docs/covmap-cips/` in this repo until handed over;
handing them over is an outward-facing action with its own sign-off.
Items 1–3 can be drafted immediately after the pilot; 4–6 should cite
pilot experience to earn their priority claims.

### 8.5 P0 pilot (small, decides 4.1's implementation)

setup-deps row for covmap (`-` URL, internal; pin the assessed rev)
+ `cargo build`; record in `docs/spec-sources.md`. Pilot: segment the
channel/select clauses of the pinned spec, connect them to latitude
entries C1–C11 (working around gap 2 by running both coverings inside
one repo checkout if needed — itself evidence for the CIP), simulate
a re-pin by advancing the spec one Go release, and check the drift
report against the hand-derived list of affected envelope arguments.
Exit criteria: the §8.2 workflow demonstrated or refuted end-to-end;
CIP drafts (§8.4) written from the transcript; go/no-go on covmap as
4.1's implementation (fallback: the bare anchor lint, which remains
sufficient for citation-resolution alone).
