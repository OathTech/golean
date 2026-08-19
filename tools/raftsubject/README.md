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
| `frontier.py` | The REFUSAL INVENTORY instrument: walks the frontend's refusals over the subject tree, replacing one declaration body per step, and checks each step against the recorded expectation. | after any frontend or subject change |

Supporting tracked inputs: `overlay/**` (the hand-written replacements),
`probe-main.go` (the harness-shaped entry points the frontier walk exports
against), `frontier-plan.tsv` (the recorded walk).

The ruling these implement, and every delta they introduce, are recorded in
`docs/2026-08-15_raft-push-p0-scoping.md` §8.6 and `docs/raft-w2-log.md`.

`frontier.py` and `difftest.py` need `artifacts/nativefrontend`
(`GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend`)
and the Go module cache respectively; neither is capped, so neither should be
pointed at anything but this small tree.
