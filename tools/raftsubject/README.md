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
| `sweep.py` | The HEADLINE instrument. Runs the walk, censuses it, then re-exports a probe tree with the sinks OPENED (dead declarations neutralised, live causes flattened) and re-censuses — to a FIXPOINT, since neutralising a declaration cuts its own edges. Prints the live/quarantined headline, a residual-sink report (the check behind "nothing hides behind a refusal"), and the standalone G-1 CROSS-CHECK probe (since W4.0 nothing is masked — the plan has no body-replacing deltas — so the probe must AGREE with PASS 1's own Intn row). Fails closed on a stale plan, a flattening that stops type-checking, and a `crypto/rand` that has become modeled. | after any frontend or subject change — this is the number to quote |

Supporting tracked inputs: `overlay/**` (the hand-written replacements),
`probe-main.go` (the harness-shaped entry points the frontier walk exports
against), and ONE walk plan, `frontier-plan.tsv` — since W4.0 the TERMINAL ROW
ALONE: the tree exports clean with zero probe deltas (H-9 fixed as BUG-064,
errors.New modeled as the E5 shim; the plan header records exactly what
retired the previous 14 action rows). `probe/` is gone with them — the
errors.New probe body was lifted into the frontend shim
(`tools/nativefrontend/stdlibshim.go`).

The plan's history, for the difference measurements: 71 action rows against a
frontend without per-declaration method quarantine, 14 against one with it
(H-3, `c7938b25` — the 35-body/22-import difference is `docs/raft-w3-log.md`
§2.2), one terminal row against the W4.0 frontend (the 14-row difference is
the W4.0 export unblock, `docs/raft-w4-log.md`).

The ruling these implement, and every delta they introduce, are recorded in
`docs/2026-08-15_raft-push-p0-scoping.md` §8.6 and `docs/raft-w2-log.md`.

`frontier.py` and `sweep.py` need `artifacts/nativefrontend`
(`GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend`);
`reachability.py` needs an exported wire from it; `difftest.py` needs the Go
module cache. None is capped, so none should be pointed at anything but this
small tree.
