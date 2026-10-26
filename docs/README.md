# docs/ — the index

Written 2026-10-12 ([AGENT], lane `docs/release-docs-1012`; release-readiness item 7). `docs/`
holds about 330 top-level files. Most of them are dated records, and about fifteen documents
are maintained. The maintained documents are listed below by role, followed by the rule for
reading everything else.

## The living documents

**Start here**

- `../README.md`: the front door. It covers what GoLean is, how to build and run it, and its
  limits.
- `semantics-overview.md`: the semantics for someone who will reason against it (the machine,
  the executable step, drivers, labels, the choice tape, stops, the kept customer surface, limits;
  the relation retired 2026-10-20), with each claim pointing at its Lean name.
- `release.md`: what a release is (the tag, the pins, the gate, the frozen changelog, the stated
  limits, the three predicates), who tags, the procedure, and the stated limits ruled so far.
- `cli.md`: the `golean` subcommands, the wire format `golean-native-v3`, the observation
  format `golean-observation-v1`, and three deliberate escape hatches.
- `../THIRD_PARTY_NOTICES.md`: the third-party material carried in the tree, each piece with
  its license and where its notice lives.

**Rules and charter**

- `../CLAUDE.md` (`AGENTS.md` is its alias): the working charter. It sets out what is built,
  what is trusted, the gates, and the merge protocol.
- `architecture-rules.md`: the architecture rules (GoCore at the centre, fail closed, latitude
  reified, evidence on main).
- `2026-08-11_essence-of-go-doctrine.md`: the doctrine that the semantics is the weakest
  machine Go permits.
- `stdlib-admission-register.md`: the standing rule for which standard-library code is
  admitted, and how.

**Fidelity and coverage**

- `BUGS.md`: the single index of known fidelity bugs, open and fixed.
- `2026-08-11_latitude-inventory.md`: every point where Go permits several behaviours, and how
  the machine resolves it. §11 states the two contracts.
- `language-coverage-ledger.md`: the whole-language bar, the refused-construct frontier
  (FR rows) and the TODO rows.
- `coverage-ledger.md`: the differential coverage accounting.
- `coverage-suite-structure.md`: how the corpus is laid out, the lanes, case metadata, and how
  to add a case.
- `spec-sources.md`: the pinned spec, memory-model and library documents that claims cite.

**Consumers, decisions, operations**

- `changelog/`: what changed for consumers. `61958f2e-WINDOW.md` is the frozen 2026-10-03
  offer, and `20d3946d-WINDOW.md` is every consumer-visible change since.
- `2026-08-31_qrow-rulings.md`: the decision log of [USER] rulings (the Q-rows and later
  rulings, appended).
- `operational-lessons.md`: build, memory and tool incidents, with their measured remedies.
- `ARCHIVE.md`: the index of parked branches and era archives; since 2026-10-20 also the
  design-donor library of the retired relational line (what is parked where, in what state,
  none of it for use).
- `agent-sandbox.md`: scratch-directory conventions for sandboxed sessions.

## Dated files are records

A file named `docs/2026-MM-DD_<topic>.md` is a **record** of the lane that wrote it. It was
correct at its commit and is not maintained afterwards. When a dated record and a living
document disagree, the living document (or the code) wins. A record is superseded by a later
record or by a living document, never by being edited. Banners such as HISTORICAL or SUPERSEDED
are a courtesy and do not always appear. The same rule applies to `archive/`, `evidence/`,
`assessment/`, `census/`, `codex-briefs/` and the per-arc `*-log.md` files.

A few dated files are still the **plan of record or a live design**:

- `2026-10-12_release-readiness.md`: the release-readiness backlog, the current plan. Each item
  carries its status.
- `2026-10-12_gate-cull-plan.md`: the gate's current shape and its follow-ups.
- `2026-10-03_offer-to-logic-team.md`: the last re-pin offer to the logic repository, whose §4
  lists the stated limits.

Two designs that sat in that list shipped and are records now: the seeded-heap design
(`2026-10-09_seeded-heap-design.md`; the `--seed` mode of `native-json-run` and `choice-trace`,
`cli.md` §2.1.1) and the `uintptr` repair design (`2026-10-12_uintptr-repair-design.md`;
`IntKind.uintptr`, BUG-124 fixed, release-readiness item 26).

The release passes so far, each a record: `2026-10-12_release-trust-review.md` (the first
fresh-context trust review), `2026-10-13_fresh-eyes-fail-closed-pass.md` (the fail-closed pass),
`2026-10-13_codex-zero-context-pass.md` (the zero-context pass; its brief is
`codex-briefs/2026-10-13_zero-context-release-pass.md`) and `2026-10-26_deep-clean-release-pass.md`
(the deep-clean pass, with its punch list `2026-10-26_deep-clean-release-punch-list.md` and the
five reports under `reviews/2026-10-26-deepclean/`).

The pinned-statement design notes (`2026-09-24_execution-statement.md`,
`2026-09-28_step-label.md`, `2026-10-04_pool-relation-spec.md`) are records too. What they
designed went into the Lean source up to tag `relational/last-main-2026-10-20`; the relational
line (the `Step` relation, its coherence proofs and the pool half) was retired 2026-10-20 and is
indexed as design donors in `ARCHIVE.md`. The `Prefix`/`Finish` closure and the `stepFn_eqns`
library stay live on main; `semantics-overview.md` says what remains.

The batched-window charter (`2026-09-23_batched-window-charter.md`) and its window plan
(`2026-09-24_window-plan.md`) closed with the 2026-10-03 offer. The earlier master plan
(`2026-09-05_master-plan.md`) is history.
