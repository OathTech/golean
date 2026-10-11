# GoLean

**Plan of record: `docs/2026-09-05_master-plan.md` (+ its §7 addendum,
the 2026-09-05 review dispositions); charter: `CLAUDE.md` (`AGENTS.md`
is a git-tracked symlink alias of it); architecture rules:
`docs/architecture-rules.md`.** The pointers further down are
historical unless they say otherwise.

This is the project repo for the Go-to-Lean tool.

## Getting started on a fresh clone

A reasonable setup is enough; nothing is bound to a particular machine.

- **Lean** via [elan](https://github.com/leanprover/elan): `lean-toolchain` pins the
  version (currently `v4.32.2`); elan installs it on first use.
- **Go `go1.26.5` exactly** — the differential oracle (`baselines/go-oracle-pin`); any
  other patch level is a red gate by design, never a silent drift.
- **Python 3.11 or newer** (standard library only), `git`, `jq`.
- **A memory cap**: `capped` if your box has the Oath wrapper, else `scripts/capped`
  (the same mechanism; needs cgroup v2 delegation or `systemd-run --user`). An
  uncapped Lean build has taken a machine down before; the gate refuses to run
  uncapped unless you opt out by name (`CAPPED_MEM_MAX=none`).

```
scripts/setup-deps                 # goose, go, raft reference checkouts at the pinned revs (gitignored deps/)
capped -m 64G -- lake build        # the cold build needs ~64 G; later builds run at the default cap
capped scripts/ci --diff           # the gate plus the differential corpus; records the baselines it then checks
```

The first `scripts/ci` without `--diff` reports two «NO recorded run» failures: it
has not seen the corpus yet. That is the fail-closed design, not an error in your
setup; `--diff` records the runs. Everything the gate checks is pinned in the
repository (sources, scripts, the toolchain and oracle versions), so a clone on
another machine with the same pins is fresh, not stale.

The [2026-09-11 whole-project review](docs/2026-09-11_project-review.md)
assesses executable coverage, semantic fidelity, relational and Iris customer
readiness, experiments, and validation at `bf721a4c`. It includes fresh
counterexamples, evidence limits, completion criteria, and a proposed roadmap.
This is the current dated assessment; its recommendations are proposals, not
an adopted replacement for the plan of record. [AGENT; publication requested
by USER, 2026-09-11.]

The parent workspace contains research notes and reference dependencies under
`../deps`. This subdirectory is intentionally its own git repository so the tool
can grow independently of those reference checkouts.

Direction:

- A native Go frontend (`tools/nativefrontend`, built on `go/parser` +
  `go/types`) type-checks Go and emits a clean typed wire schema that
  `GoLean/NativeToIR.lean` lowers into a GoCore deep embedding. (Gobra was an
  earlier temporary frontend accelerator and has been removed.)
- GoCore is the semantic center; frontend-specific concerns stay in the
  lowering adapter and fail closed.
- Differential tests compare ordinary Go execution (`go run`) against Lean
  execution of GoCore.
- The Iris proof layer built on this semantics lives on branch
  `park/reasoning-2026-08-31`, pending migration to its own repo (the repo
  split, 2026-08-31 — `docs/2026-08-31_repo-split-plan.md`, with its
  2026-09-05 addendum: the semantic relation and its coherence proofs stay
  HERE; this repo makes no verification claims about Go programs).

The Gate A1 consumer-contract experiment (`spikes/gate-a1`), the Iris customer spike
(`spikes/iris-customer`), the `GoLean/Interface.lean` facade and the typed-admission
profile family were PARKED on 2026-09-16 ([USER] ruling; audit fix F1): preserved at tag
`typed-profiles/last-main-2026-09-16`, revival recipe and inventory in
[docs/2026-09-16_typed-profiles-parked.md](docs/2026-09-16_typed-profiles-parked.md); their
future home is the reasoning repository under gitignored `deps/`. Their historical review is
[docs/2026-09-05_gate-a1-review-and-next-phase.md](docs/2026-09-05_gate-a1-review-and-next-phase.md).

Design and roadmap docs (HISTORICAL — superseded as current direction by
the plan of record above; kept for their design rationale):

- `docs/architecture.md`: project layers and ownership boundaries.
- `docs/semantics.md`: GoCore semantics design.
- `docs/roadmap.md`: phased implementation roadmap.
- `docs/archive/differential-testing.md`: differential testing plan and generator notes.
- `docs/agent-sandbox.md`: scratch directory and temp-cache conventions for
  sandboxed agent sessions.
- `TODO.md`: tactical backlog.

Useful commands:

```sh
lake build
lake exe golean --help
lake exe gocore-eval-tests
scripts/coverage
scripts/diff-coverage
scripts/coverage-negative
scripts/diff-one litmus/if-return
```

Use `scripts/coverage run ...` or `scripts/diff-one ...` for Go-vs-Lean
equivalence during semantics work (native frontend by default).

`Corpus/coverage` is the source of truth for small coverage litmus tests.
`scripts/coverage` runs both executable differential coverage and static
compile-negative coverage. The executable lane runs the same canonical Go files
with `go run` and through the native frontend / Lean path.
