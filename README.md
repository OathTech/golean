# GoLean

GoLean is an executable semantics for Go, written in Lean 4. It aims to be
trustworthy and portable, and it is validated by differential testing.

- **A Go semantics defined through the core language GoCore.** A native frontend
  (`tools/nativefrontend`, built on `go/parser` + `go/types`) type-checks a Go
  package and lowers it to a typed JSON wire. `GoLean/NativeToIR.lean` decodes
  the wire into a GoCore program, and a total Lean interpreter runs it (`stepFn`
  and its drivers, `GoLean/GoCore/`).
- **Validated against real Go.** Every corpus case runs under both `go run` at a
  pinned toolchain (go1.26.5, linux/amd64) and the Lean interpreter, and the two
  observations are compared.
- **A proof-level surface over the interpreter, for the raft-proofs repository.**
  `Prefix`/`Finish` (the counted, choice-threaded prefix closure of `stepFn` and
  the driver's five endings — `GoLean/GoCore/ExecutionStatement.lean`, proofs in
  `Prefix.lean`) and the `stepFn_eqns` rewrite library (one proved equation per
  `stepFn` arm, `GoLean/GoCore/Equations.lean`, gated by `scripts/check-equations`).
  The fuel-free relation and its coherence proofs were retired from the build on
  2026-10-20; the last main carrying them is the tag `relational/last-main-2026-10-20`
  (`docs/ARCHIVE.md`).
- **No higher-level reasoning is shipped.** Program logics, weakest preconditions
  and program proofs are not provided here.

The authoritative statement of what the repository provides is `CLAUDE.md`,
«What this repo provides, and does not». For a newcomer's tour of the semantics,
see [`docs/semantics-overview.md`](docs/semantics-overview.md).

## Who it is for

- **The GoLean logic repository** (`golean-logic`, a sibling checkout). It builds an Iris
  program logic on this semantics and consumes it at a pinned commit (currently
  the tag `logic-offer/2026-10-03`).
- **Anyone who wants a Go semantics** to execute programs against, or to state
  and prove facts about, without having to trust a hand-written model.

## The trust story

Two things are trusted. The first is the interpreter together with the native
frontend lowering. The second is the differential apparatus that checks them
against `go run`: the coverage runners, the tracked `baselines/`, and the go1.26.5
oracle pin. Everything else in the repository is untrusted tooling. The lowering
Go → GoCore has **no correctness theorem**; it is trusted only because the corpus
validates it. A consumer of a GoCore program inherits that assumption. (The full
list is in `CLAUDE.md`, «The trusted surface».)

## Getting started on a fresh clone

Nothing is bound to a particular machine: a clone on an ordinary Linux x86-64
box builds and checks with the commands below and no further setup. The
modeled instance is **gc on linux/amd64**: the interpreter realizes that platform
(`GoLean/GoCore/Platform.lean`, `gcAmd64`), the decoder refuses a wire lowered
for any other target (`decodeBuildContext`), and the differential oracle is
`go run` on that platform, so the corpus runs are Linux-only by nature. This
is the complete list of what the machine needs:

- **Lean** via [elan](https://github.com/leanprover/elan): `lean-toolchain` pins the
  version (currently `v4.35.0`); elan installs it on first use.
- **Go `go1.26.5` exactly** — the differential oracle (`baselines/go-oracle-pin`); any
  other patch level is a red gate by design, never a silent drift.
- **Python 3.11 or newer** (standard library only; it also hosts the differential
  runner's timeout wrapper, `scripts/run-with-timeout.sh`, whose exit-code contract
  coreutils' `timeout` does not keep — measured in `docs/operational-lessons.md`,
  «Box-independence»).
- **git**, **bash 5 or newer** (the runner's per-row timer reads `EPOCHREALTIME`),
  and **GNU coreutils or a compatible implementation** (`realpath -m`,
  `shuf --random-source`, `sha256sum` and `nproc` are used; the project is measured
  against uutils 0.8 as well as GNU), plus the usual Unix text tools: **findutils**
  (`find`, `xargs -0 -P`), **diffutils** (`diff`, `cmp`), **awk**, **sed** and
  **grep**. Two GNU-only `sed` uses sit outside the gate: `\l` in
  `scripts/import-goose` and `-i` in `scripts/cedar-census` and
  `scripts/test-import-goose`.
- **Optional, detected at run time, never required:** `capped`, the Oath devbox
  memory cap — every heavy step of the scripts runs through it when it is on PATH,
  sized by `CAPPED_MEM_MAX` (default 32G), and runs uncapped where it is absent;
  `bwrap` with unprivileged user namespaces, for `lake check`'s sandbox;
  `/usr/bin/time`, for peak-RSS figures in the gate's output.

```
scripts/setup-deps                       # goose, go, raft reference checkouts at the pinned revs (gitignored deps/; needs the network)
lake build                               # the cold build of the default targets (the libraries `lake check` verifies); on an Oath box: CAPPED_MEM_MAX=64G capped lake build (64 G is the measured cold need); the gate builds every target by name, the `golean` binary among them
CAPPED_MEM_MAX=64G scripts/ci --diff     # the gate plus the differential corpus; records the baselines it then checks
```

`CAPPED_MEM_MAX` sizes Lean's thread pool (cap/8G) whether or not `capped` is
present; where it is present it is also the cgroup limit, and
`CAPPED_MEM_MAX=none` is its loud opt-out. The first `scripts/ci` run without
`--diff` reports two «NO recorded run» failures, because it has not seen the
corpus yet. That is the fail-closed design, not a problem with your setup;
`--diff` records the runs. Reference checkouts live in the in-repo, gitignored
`deps/` directory (`scripts/setup-deps`; `deps/go` is a full clone, about
470 MB of history — a shallow clone at the tag, 37 MB, would satisfy the gate
but not `scripts/mine-spec-archaeology`, so the script clones in full).

## Run a program and read the result

There are three steps: lower a package to a wire, run one function of it, and
read the observation. Using a real corpus case:

```sh
GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend
.tmp/nativefrontend --dir Corpus/coverage/exec/arrays/array-len-cap --out .tmp/wire.json
.lake/build/bin/golean native-json-run --input .tmp/wire.json --function arrayLenCap
```

```json
{"output":"","schema":"golean-observation-v1","status":"ok","values":[{"kind":"int","tag":"int","value":6}]}
```

- `status` says how the run ended. `ok` is normal completion. `panic`, `fatal`,
  `deadlock` and `race` are Go behaviours. `unsupported`, `stuck` and `error` are
  refusals: the model declining, never a pass. `fuel-out` means the step budget
  ran out.
- `values` holds the function's results, each tagged by kind.
- `output` holds the bytes the program wrote with `print`/`println`.

The exit code is 0 for `ok` and 1 for every other status. Entry arguments are
passed with `--arg-int`/`--arg-bool`. A package with no `func main` is refused by
the frontend, as gc would refuse to build it; most corpus cases are such packages
(the differential harness supplies `main` around the subject), and the frontend
exports one as a subject with `--subject` (`docs/cli.md`). The subcommands, the wire and
observation formats, the refusal classes, and three deliberate escape hatches are
documented in [`docs/cli.md`](docs/cli.md). To run a corpus case through the whole
differential (Go and Lean, compared), use
`scripts/diff-one arrays/array-len-cap`.

## Add a corpus case

Each case is a Go package under `Corpus/coverage/exec/<area>/<case>/` with a
`cases.tsv` naming the subject function, its arguments and the expected status. Lanes, metadata and
the source contract are described in
[`docs/coverage-suite-structure.md`](docs/coverage-suite-structure.md).

## The gate

The gate has two tiers. `scripts/ci` is the fast tier, run before any commit
that touches runtime code: build, escape-hatch scans, the kernel replay, eval
tests, the wire and frontend checks, plus report-only speedbumps. `scripts/ci
--diff` is the merge tier, which adds a fresh differential run of every corpus
row against the tracked baselines and the `lake check` speedbump (the
toolchain's export and kernel replay of the default targets, about four
minutes; `--inadvisably-no-sandbox` where `bwrap` cannot start, and the line
says so). The owner's `lake check` outside any sandbox is the gate at claim
points, `lake check --paranoid` at a release. Each heavy step goes through the
memory cap when the box has one (`scripts/cap.sh`). The standing rule is
`CLAUDE.md`, «The gates».

## Limits

The semantics is the weakest machine Go permits, but not everywhere yet. Every
point where Go allows several behaviours is classified in the latitude inventory
([`docs/2026-08-11_latitude-inventory.md`](docs/2026-08-11_latitude-inventory.md)):
enveloped by the choice tape, pinned to one point, forced, or unknown. Its §11
states the two contracts: portable Go, and the gc/linux/amd64 instance. The limits
stated to the consumer are those of the 2026-10-03 offer
([`docs/2026-10-03_offer-to-logic-team.md`](docs/2026-10-03_offer-to-logic-team.md)
§4) as amended since in the post-offer changelog
([`docs/changelog/20d3946d-WINDOW.md`](docs/changelog/20d3946d-WINDOW.md)).
Open fidelity bugs are tracked in [`docs/BUGS.md`](docs/BUGS.md), and constructs
the frontend refuses are listed in
[`docs/language-coverage-ledger.md`](docs/language-coverage-ledger.md).

## License

Apache License 2.0 (`LICENSE`), copyright Oath Technologies, 2026.

## Where the documentation is

[`docs/README.md`](docs/README.md) indexes the living documents by role and
explains how to read the dated records. The working charter is `CLAUDE.md`
(`AGENTS.md` is a git-tracked symlink alias of it), and the architecture rules are
[`docs/architecture-rules.md`](docs/architecture-rules.md).

## Historical pointers

These are history, not current direction. They are kept for their design
rationale.

- `docs/2026-09-05_master-plan.md` (and its §7 addendum): the roadmap of
  2026-09-05, superseded as plan of record by the batched-window charter
  (`docs/2026-09-23_batched-window-charter.md`). That charter in turn closed
  with the 2026-10-03 offer.
- [`docs/2026-09-11_project-review.md`](docs/2026-09-11_project-review.md): the
  whole-project review at `bf721a4c`. Its recommendations were proposals;
  dispositions are in `docs/2026-09-11_review-dispositions.md`.
- The Iris proof layer that was built on this semantics is on branch
  `park/reasoning-2026-08-31`. Its successor is the separate logic repository (the
  repo split, `docs/2026-08-31_repo-split-plan.md`).
- The Gate A1 consumer-contract experiment, the Iris customer spike, the
  `GoLean/Interface.lean` facade and the typed-admission profiles were PARKED on
  2026-09-16 ([USER] ruling). They are preserved at tag
  `typed-profiles/last-main-2026-09-16`; see
  [`docs/2026-09-16_typed-profiles-parked.md`](docs/2026-09-16_typed-profiles-parked.md).
- `docs/architecture.md`, `docs/semantics.md`, `docs/roadmap.md`: early design
  documents (they describe a pipeline that has since been replaced).
  `docs/archive/differential-testing.md`: the original differential-testing plan.
- `TODO.md`: the tactical backlog as of 2026-09-15, not maintained since
  2026-10-12.
- `docs/agent-sandbox.md`: scratch-directory conventions for sandboxed agent
  sessions (still in use).
