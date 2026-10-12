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
- **A relational semantics proved coherent with the interpreter.** A fuel-free
  step relation (`Step`, and `StepML` for the goroutine pool) is proved equivalent
  to the interpreter per step in both directions, and for the drivers' traces,
  runs and observations (`GoLean/GoCore/BridgeSet.lean` pins the statements).
- **No higher-level reasoning is shipped.** The relation is meant to be useful
  for reasoning, but program logics, weakest preconditions and program proofs are
  not provided here.

The authoritative statement of what the repository provides is `CLAUDE.md`,
«What this repo provides, and does not». For a newcomer's tour of the semantics,
see [`docs/semantics-overview.md`](docs/semantics-overview.md).

## Who it is for

- **The GoLean logic repository** (`~/projects/golean-logic`). It builds an Iris
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

A reasonable setup is enough; nothing is bound to a particular machine. The
modeled instance is **gc on linux/amd64**: the interpreter realizes that platform
(`GoLean/GoCore/Platform.lean`, `gcAmd64`), and the decoder refuses a wire
lowered for any other target (`decodeBuildContext`). The toolchains are pinned, and builds need a memory
cap.

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

The first `scripts/ci` run without `--diff` reports two «NO recorded run»
failures, because it has not seen the corpus yet. That is the fail-closed design,
not a problem with your setup; `--diff` records the runs. Reference checkouts live
in the in-repo, gitignored `deps/` directory (`scripts/setup-deps`).

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
passed with `--arg-int`/`--arg-bool`. The subcommands, the wire and
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

The gate has two tiers. `capped scripts/ci` is the fast tier, run before any
commit that touches runtime code: build, escape-hatch scans, eval tests, the wire
and frontend checks, plus report-only speedbumps. `capped scripts/ci --diff` is
the merge tier, which adds a fresh differential run of every corpus row against
the tracked baselines. The standing rule is `CLAUDE.md`, «The gates».

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
