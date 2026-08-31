# Reviving the reasoning product: the beginner's guide

For any future agent (or human) picking the verification/reasoning
threads back up. Written at the repo split (2026-08-31,
[USER]-directed; the decision record is
`docs/2026-08-31_repo-split-plan.md` — read it first for WHAT moved
and why; this note is HOW to resume).

## What happened, in three sentences

This repo used to hold two products: the executable Go semantics
(differentially validated) and an Iris-based reasoning stack proving
theorems over it. On 2026-08-31 the reasoning product was parked
whole — code, gates, docs, all green — on branch
`park/reasoning-2026-08-31`, and main was slimmed to the semantics
product only. The intended end state is a SEPARATE reasoning repo
that consumes this one as a pinned dependency; that migration has
NOT happened yet and all its decisions (name, dependency mechanism,
history strategy) are the user's.

## Where everything is

- **`park/reasoning-2026-08-31`** (= `7440bf70`, also
  `refs/snapshots/pre-repo-split-main`): the complete last
  everything-together state. On it you will find:
  - `proofs/` — the Lake package `golean-proofs`: the Iris layer
    (Laws/, Frame/, Sym/, TotalWp), the relational-semantics
    language instances (`Lang*.lean`, `Adequacy.lean`,
    `Lifting.lean`), the corpus proofs (`Specs/`, `Examples/`),
    `Audit.lean` (the in-build axiom/non-vacuity gate + the
    51-theorem designated list), and the judge pair
    `Challenge.lean`/`Solution.lean`.
  - `compat/` — the Verdi Raft-spec port and the Gobra backend
    (exploratory lanes, lower bar, own gates).
  - The proof-side gates and scripts: the full pre-split
    `scripts/ci` (proofs steps 1b2/1c/1c3/1c4/1d/1e/3/3b0/3b/3c/
    3d/3v and friends), `scripts/comparator-judge` +
    `comparator-setup`, the A-TRIP pair (`wp-veneer-lint` +
    `WpVeneerClosure.lean`, scope `wp-lint-scope.txt`),
    `check-golden` + `baselines/golden/`, the goose R2-pin guards.
  - The proof-era docs: the plan of record
    (`docs/2026-08-28_iris-corpus-plan.md`), the charter as it was
    (that branch's `CLAUDE.md`), the era archive index (that
    branch's `docs/ARCHIVE.md`), the arc logs, the post-mortems.
- **`raft-proof-campaign`** — the unmerged campaign decision log
  (206 commits not on main, 153 of them touching
  `docs/raft-campaign-log.md` — the [AGENT]/[USER] provenance
  trail; its worktree was `.claude/worktrees/campaign`).
- **`archive/callspec-era`**, **`archive/fixed-trajectory-era`** —
  the two killed eras (cautionary reading; indexed by the park
  branch's ARCHIVE.md).

## State of the product at the park (do not re-derive this)

Phase A of the corpus-first Iris plan (hygiene slice H, U0 —
Lean 4.32.2 + iris-lean `e7a0a438` pin, validated by a full
2475-case differential, TotalWp inhabited — and A-TRIP, the veneer
tripwire, live in-build) was COMPLETE and merged, PLUS the first
phase-B structural unit: G-BIND (the bind rule `wp_plug_bind`/
`wp_bind_plug` via Löb induction) with its gate-instance corpus
case C-05 (callchain) closed THROUGH the WP calculus, negative twin
and first-order sentence exports included. Honest note on A-TRIP:
its first in-build enrollment FAILED on scope gaps (the outsider
review's R2, "the A-TRIP scope cannot hold its first customer");
the enrollment was rebuilt and the gate went green at `7440bf70` —
the scope config is young, treat it with care. An outsider review
judged the layer "genuine Iris" (MINOR REVISIONS; record:
`raft-proof-campaign` branch, `docs/raft-campaign-log.md`, the
"OUTSIDER LEGITIMACY REVIEW" entry — NOT on the park branch), with
two residuals that must travel with the verdict: R1, the
grandfathered `allStreamsOk` enumeration tier (~35 theorems, 4 of
them designated/judge-shipped, labeled in docs rather than
artifacts); and the economics finding — 892 proof lines per 32 Go
lines with G-AUTO unbuilt ("Yes, if it survives its own
economics"). The last comparator-judge landmark: 51 theorems,
like-for-like.

Next on the ladder (per the plan of record — a PARTIAL order:
G-EXIT can land any time after U0, and the G-AUTO probe gates after
the first two structural units): **G-REPR** (the big design unit —
real per-field points-to, route (b) re-keyed heap, with a
pre-registered sibling-field-write-under-frame discriminating
test), G-CALLS, G-MAPITER, G-TOTAL's corpus rows, G-EXIT, G-SORT,
the G-AUTO throughput probe; then phase C — the ~11 corpus members
not already closed as gate instances (C-05 is done; several others
close inside phase B); raft is the FINAL corpus member. Named owed row: a
σ-conditioned `wp_plug_bind` variant (the `hdrain` premise is FALSE
at drain sites with ≥2 live defers — trigger: G-MAPITER/G-CALLS or
the first ≥2-defer corpus member).

## How to resume work (before the migration exists)

1. Branch off the park, in a worktree — never work on the park
   branch itself:
   `git worktree add .claude/worktrees/<lane> -b <lane> park/reasoning-2026-08-31`
2. Use THAT branch's scripts, not main's: its `scripts/setup-deps`
   still knows the reasoning reference checkouts (iris-lean,
   perennial, verdi family) and populates `proofs/.lake/packages`
   offline via `--from <a sibling checkout>`.
3. Build ONLY via `scripts/capped` (cgroup cap — uncapped Lean
   builds have killed this box; see that branch's
   `docs/operational-lessons.md` for warm/threads/build-lock
   discipline). The gate is that branch's `scripts/ci`.
4. The comparator judge runs at landmarks only, needs the external
   trust tools under `deps/` (comparator, lean4export, landrun —
   NEVER modified; version pins are chosen with the user; the
   binary build has needed the user to run it), and cannot run
   from a lane worktree.
5. Re-read that branch's `CLAUDE.md` before proving anything: the
   veneer ban (WP-stated theorems reach the machine only through
   Laws/lifting/adequacy — A-TRIP enforces it), the quantifier
   audit, and the bounded-techniques ban are the law of that
   product. Of its [USER] hard-stop design gates: N-2 (trust-tool
   pins) and N-7 (charter amendment) are already DISCHARGED
   (recorded in `park:proofs/lakefile.toml` and the park CLAUDE.md
   respectively); still LIVE ahead of you: N-3 (corpus design
   sign-off), N-4 (G-INV — the re-run W2.5 invariant gate), N-5
   (designation acts), N-6 ("is the layer real?" at 2-3 corpus
   closures).

## The migration, when it happens (all [USER] decisions)

Sketch as discussed at the split (nothing pre-committed): a new
repo ([AGENT]-proposed working name `golean-logic` — the user has
not chosen a name) created as a FULL CLONE of this
one (so every SHA cited in the logs resolves there), stripped to
the reasoning product, with `[[require]] GoLean` rewired from
`path=".."` to a PINNED git require on this repo. Known technical
risk to solve at that point: the reflection chain — `check-golden`
and the golden pins read fixture bytes and run the frontend from
this repo, so path resolution must be re-anchored through the
pinned dependency checkout, fail-closed. Also owed from this side:
the GoCore relational-module extraction (see the split plan) —
`Machine.lean`/`MachineSound.lean`/`Multi*`-soundness/`NPDRF`/
`Race` are ruled reasoning-side but are interleaved with the
executable interpreter; moving them needs a design slice and a full
`--diff` revalidation here.

## The one rule that outranks the rest

Main makes no verification claims now, and the park is a frozen
green state: whatever revives it must resume THROUGH its own gates
(its ci, its Audit build, its judge cadence, its audit protocol) —
not by cherry-picking artifacts onto main, and not by rebuilding
proof machinery inside the semantics repo.
