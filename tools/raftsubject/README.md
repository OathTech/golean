# `tools/raftsubject/` — the subject-tree derivation toolkit

Produces and validates `raftsubject/`, the vendored etcd-io/raft subject tree.
Lives here rather than in `scripts/` because `scripts/` is the gate surface and
this is subject engineering (raft lane W2); nothing in `scripts/ci` calls it.

| tool | what it does | when to run |
|---|---|---|
| `derive.py` | Derives `raftsubject/` from `deps/raft`. Three modes — verbatim (import-path rewrite), plainpb (strip the protobuf runtime out of the generated `raft.pb.go`), overlay (hand-written replacement behind a pinned upstream digest). Fails closed on any declaration it has no rule for. | after any `deps/raft` pin move, or any change to the rules/overlays |
| `derive.py --check` | Re-derives to a temp dir and diffs against the tracked tree; exit 1 on drift. | to prove the tree is still the derivation's output |
| `derive.py --print-digests` | Prints the upstream SHA-256 table to paste into `DIGESTS`. Refreshing the pin is deliberately a human act — there is no `--update-digests`. | when a pin move has been READ and accepted |
| `difftest.py` | The DIFFERENTIAL OBLIGATION: builds a throwaway module linking BOTH upstream raftpb (real protobuf runtime) and the derived plainpb, and compares `CloneMessage`/`EqualMessage`/`ConfState.Equivalent` against `proto.Clone`/`proto.Equal`/upstream `Equivalent` over a value battery. | after any change to the generated clone/equality or the confstate overlay |
| `frontier.py` | The REFUSAL INVENTORY instrument: walks the frontend's refusals over the subject tree, replacing one declaration body per step (or applying a recorded PROBE DELTA — `$drop-import`, `$rewrite`, `$add`), and checks each step against the recorded expectation. | after any frontend or subject change |
| `reachability.py` | The LIVENESS primitive (W2.2). Since methods quarantine per declaration, a refusal no longer blocks the export — it lands as a stub that refuses when CALLED. This walks the exported wire's call graph from a named entry set and reports each quarantined declaration LIVE (with the path) or dead. `dead` is the sound direction; see its docstring for the two approximations. **On its own it UNDER-reports**, because a quarantined declaration is a sink — use `sweep.py` for a number to quote. | ad hoc, against one wire |
| `sweep.py` | The HEADLINE instrument. Runs the walk, censuses it, then re-exports a probe tree with the sinks OPENED (dead declarations neutralised, live causes flattened) and re-censuses — to a FIXPOINT, since neutralising a declaration cuts its own edges. Prints the live/quarantined headline, a residual-sink report (the check behind "nothing hides behind a refusal"), and the standalone G-1 probe for the one gap the walk's own probe delta masks. Fails closed on a stale plan, a flattening that stops type-checking, and a `crypto/rand` that has become modeled. | after any frontend or subject change — this is the number to quote |

Supporting tracked inputs: `overlay/**` (the hand-written replacements),
`probe/**` (probe-only files the walk injects — never derived into the subject
tree), `probe-main.go` (the harness-shaped entry points the frontier walk
exports against), and TWO walk plans:

ONE walk plan, `frontier-plan.tsv`: 14 action rows + terminal, written against
the mainline frontend and re-pinned 2026-08-20 onto `main` @ `7ca8908e`.

There used to be two — a 71-row plan for a frontend without per-declaration
method quarantine, and a 14-row one for a frontend with it. H-3 landed
(`c7938b25`), so the second is simply the plan and the first is retired
(`docs/raft-w3-log.md` H-16, discharged). The difference between them — 35
method-body replacements and 22 further import drops — IS the measurement of
what the merge bought, and it lives in the log's §2.2 rather than in a file
that would now be red.

The ruling these implement, and every delta they introduce, are recorded in
`docs/2026-08-15_raft-push-p0-scoping.md` §8.6 and `docs/raft-w2-log.md`.

`frontier.py` and `sweep.py` need `artifacts/nativefrontend`
(`GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend`);
`reachability.py` needs an exported wire from it; `difftest.py` needs the Go
module cache. None is capped, so none should be pointed at anything but this
small tree.
