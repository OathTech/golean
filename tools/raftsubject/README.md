# `tools/raftsubject/` — the subject-tree derivation toolkit

Produces and validates `raftsubject/`, the vendored etcd-io/raft subject tree.
Lives here rather than in `scripts/` because `scripts/` is the gate surface and
this is subject engineering (raft lane W2); nothing in `scripts/ci` calls it.

| tool | what it does | when to run |
|---|---|---|
| `derive.py` | Derives `raftsubject/` from `deps/raft`. Modes — verbatim (import-path rewrite, plus the RECORDED `SUBJECT_PATCHES`: exact-text-keyed deltas like D-11's jitter choice site, refused on upstream drift), plainpb (strip the protobuf runtime; also generates the clone/equality AND the W4.1 wire codec from the parsed field lists), select (declaration subset), overlay (hand-written replacement behind a pinned upstream digest). Fails closed on any declaration it has no rule for. | after any `deps/raft` pin move, or any change to the rules/overlays/patches |
| `derive.py --check` | Re-derives to a temp dir and diffs against the tracked tree; exit 1 on drift. | to prove the tree is still the derivation's output |
| `derive.py --print-digests` | Prints the upstream SHA-256 table to paste into `DIGESTS`. Refreshing the pin is deliberately a human act — there is no `--update-digests`. | when a pin move has been READ and accepted |
| `difftest.py` | The DIFFERENTIAL OBLIGATION vs the REAL protobuf runtime: a throwaway module linking upstream raftpb and the derived plainpb; compares clone/equality/Equivalent (sections 1-6) and, since W4.1, THE WIRE CODEC (section 7: Marshal bytes, Size, both cross-unmarshals). Needs the Go module cache/proxy — OWED where a sandbox denies them (run with normal GOPROXY). | after any change to the generated clone/equality/codec or the confstate overlay |
| `frontier.py` | The REFUSAL INVENTORY instrument: walks the frontend's refusals over the subject tree, replacing one declaration body per step (or applying a recorded PROBE DELTA — `$drop-import`, `$rewrite`, `$add`), and checks each step against the recorded expectation. | after any frontend or subject change |
| `reachability.py` | The LIVENESS primitive (W2.2). Since methods quarantine per declaration, a refusal no longer blocks the export — it lands as a stub that refuses when CALLED. This walks the exported wire's call graph from a named entry set and reports each quarantined declaration LIVE (with the path) or dead. `dead` is the sound direction; see its docstring for the two approximations. **On its own it UNDER-reports**, because a quarantined declaration is a sink — use `sweep.py` for a number to quote. | ad hoc, against one wire |
| `sweep.py` | The HEADLINE instrument. Runs the walk, censuses it (subject quarantines AND imported stubs — the W4.1 done criterion's clause 2), then re-exports a probe tree with the believed-dead declarations neutralised and re-censuses — to a FIXPOINT. The CAUSE-FLATTEN TABLE IS EMPTY since W4.1 item 5 (every cause modeled; an empty table is the fail-closed direction — a reappearing cause surfaces as a residual sink instead of being flattened over). The G-1 probe is retired (the D-11 derivation patch makes the jitter draw plain Go); a tripwire EXITS if `lockedRand.Intn` ever reappears quarantined. | after any frontend or subject change — this is the number to quote |
| `codeccheck.py` | The W4.1 codec battery (H-1): 38 checks — round trips, Size=len∘Marshal, hand-computed goldens, decode-only paths, the stepLeader/entsSize shapes — over the DERIVED codec, under BOTH `go run` and the machine, verdicts compared. The in-sandbox half of the codec differential (difftest.py section 7 is the upstream-runtime half). | after any codec, frontend, or machine change |
| `runprobe.py` | THE-MOMENT instrument (W4.1): runs a tracked probe main (default `rawnode-probe-main.go`, the minimal single-node RawNode drive) over the subject tree under BOTH oracles and compares the observation; a machine stop is printed VERBATIM (its job is an honest first-stop report). First agreement recorded 2026-08-20: go=111035, machine=111035. Since W4.2: `--expect-stop SUBSTR` (negative-probe mode — PASS iff both oracles refuse loudly and the machine's first stop names SUBSTR; the logger-teeth probe's mode), and string observations decode from the `bytes`/`tag:"string"` form. | after any subject/frontend/machine change; the smoke test that raft RUNS |
| `twin-lib.go` + the `twin-*-main.go` thin mains | THE MACHINE-TWIN HARNESS v1 (W4.2): n RawNodes, the message multiset, the event vocabulary (tick/campaign/propose/deliver + drain macros), the bundled harvest (the recorded §2 narrowing), S1-S3 per step + S4 as the end condition, the exercise floor, named hand SCHEDULES as the input — all in `twin-lib.go`. Run a group: `runprobe.py --main twin-elect-main.go --lib twin-lib.go --function probeTwinElect --fuel 4000000000` (groups: single / elect / perturb / ticks; `twin-main.go` is the combined probeTwin, interpreter-slow — prefer the split). | after any subject/frontend/machine change; the n=3 smoke test |
| `logger-teeth-probe-main.go` / `logger-installed-probe-main.go` | The W4.2 logger-census probe pair: the same drive WITHOUT the harness logger (both oracles refuse loudly; machine stops verbatim at `DefaultLogger.Infof` — run with `--expect-stop DefaultLogger.Infof`) and WITH it through BOTH seams (green, 1111035 — includes a recovered `getLogger().Panicf` teeth check of the registry seam). Together they make the dead-DYNAMICALLY census argument machine-checkable. | after any logger/seam/frontend change |
| `tracereplay.py` + `replayenv.go` | The datadriven-trace ok-tier differential (W4.2 item 3): parses `deps/raft/testdata` into blocks, replays each trace's SUPPORTED PREFIX through a faithful InteractionEnv mirror under BOTH oracles, compares traces byte-for-byte, and scores the literally-`ok` expectation blocks. Measurement instrument — no corpus rows land from it. | after any subject/frontend/machine change touching the replayed surface |

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
