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
| `reachability.py` | The LIVENESS instrument (W2.2). Since methods quarantine per declaration, a refusal no longer blocks the export — it lands as a stub that refuses when CALLED. This walks the exported wire's call graph from a named entry set and reports each quarantined declaration LIVE (with the path) or dead. `dead` is the sound direction; see its docstring for the two approximations. | after any frontier walk, to turn refusals into a work list |

Supporting tracked inputs: `overlay/**` (the hand-written replacements),
`probe/**` (probe-only files the walk injects — never derived into the subject
tree), `probe-main.go` (the harness-shaped entry points the frontier walk
exports against), and TWO walk plans:

| plan | frontend it is written against |
|---|---|
| `frontier-plan.tsv` | the PRE-merge frontend (`main` today): 71 action rows, because every unlowerable METHOD blocks the whole export |
| `frontier-plan-postmerge.tsv` | a frontend carrying H-3 (per-declaration method quarantine): 14 action rows, standing for exactly 3 gaps |

When H-3 lands, the post-merge plan becomes the default and the pre-merge plan
is retired (`docs/raft-w3-log.md` H-16). The difference between the two plans
IS the measurement of what the merge buys.

The ruling these implement, and every delta they introduce, are recorded in
`docs/2026-08-15_raft-push-p0-scoping.md` §8.6 and `docs/raft-w2-log.md`.

`frontier.py` needs `artifacts/nativefrontend`
(`GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend`);
`reachability.py` needs an exported wire from it; `difftest.py` needs the Go
module cache. None is capped, so none should be pointed at anything but this
small tree.
