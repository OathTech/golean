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
  the relation, drivers, labels, the choice tape, stops, the pinned set, limits), with each
  claim pointing at its Lean name.
- `release.md`: what a release is (the tag, the pins, the gate, the frozen changelog, the stated
  limits, the three predicates), who tags, the procedure, and the stated limits ruled so far.
- `cli.md`: the `golean` subcommands, the wire format `golean-native-v3`, the observation
  format `golean-observation-v1`, and three deliberate escape hatches.

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
- `ARCHIVE.md`: the index of parked branches and era archives.
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
- `2026-10-09_seeded-heap-design.md`: the seeded-heap entry for function-level runs, a design
  gate pending [USER].
- `2026-10-12_uintptr-repair-design.md`: the `uintptr` runtime-identity repair (release-readiness
  item 26, the REPAIR half of D6), a design gate pending [USER].
- `2026-10-12_gate-cull-plan.md`: the gate's current shape and its follow-ups.
- `2026-10-03_offer-to-logic-team.md`: the last re-pin offer to the logic repository, whose §4
  lists the stated limits.

The release passes so far, each a record: `2026-10-12_release-trust-review.md` (the first
fresh-context trust review) and `2026-10-13_fresh-eyes-fail-closed-pass.md` (the fail-closed pass);
the brief for the next one is `codex-briefs/2026-10-13_zero-context-release-pass.md`.

The pinned-statement design notes (`2026-09-24_execution-statement.md`,
`2026-09-28_step-label.md`, `2026-10-04_pool-relation-spec.md`) are records too. What they
designed is now in the Lean source and summarised in `semantics-overview.md`.

The batched-window charter (`2026-09-23_batched-window-charter.md`) and its window plan
(`2026-09-24_window-plan.md`) closed with the 2026-10-03 offer. The earlier master plan
(`2026-09-05_master-plan.md`) is history.
