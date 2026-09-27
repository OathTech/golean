# Adversarial audit evidence — window packet A, the contract (2026-09-27)

[AGENT] auditor, for `docs/2026-09-27_packet-a-audit.md`. Candidate `window/packet-a-contract-0927` @ `209a1833`
(the tree was clean for every run; each probe mutation was reverted from a byte copy before the next step).
Host: linux/amd64, 32 cores, other agents' jobs possibly running (the box-wide lock was held for every Lean batch and
for the gate). Toolchains: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); `leanprover/lean4:v4.32.2`.
Absolute paths in captured outputs are rewritten to `<worktree>/` / `<primary>/`.

| File | What |
|---|---|
| `StrayPanic.lean` / `.out` | F1: the non-abort panic witness; Lean proofs of `¬ finish_abort_step_stmt`, `¬ run_panic_iff_stmt`, `¬ classification_stmt`, `¬ classification_wf_stmt` (the witness satisfies `StateWf`, `MachineWf`, `NoRefusal`) |
| `NoRefusalVacuous.lean` / `.out` | F2: `not_noRefusal_of_completes`; F5: `program_bridge_stmt`, `silent_projection_stmt`, `single_embedding_stmt` proved in one line each |
| `PinMutation.lean` / `.out` | stable set: a mutated pin and a drifted theorem fail (`Type mismatch` ×2); a same-type changed definition passes (the documented limit) |
| `srcmut.out` | stable set: a REAL source mutation of `Trace.erase` fails `lake build GoLean.GoCore.BridgeSet` at `BridgeSet.lean:58` |
| `mem-callsites-probes.txt` | the inventory probes (header lists each mutation) |
| `ci-diff.tail.txt` | `ci --diff` at `209a1833`: RESULT FAIL on exactly the 5a pair |

## Reproduction (from the root of a worktree of `review/packet-a-contract-0927`, warm `.lake`)

```sh
scripts/setup-deps --from /home/dev/projects/golean
GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean.GoCore.ExecutionStatement GoLean.GoCore.BridgeSet
GOLEAN_MEM_MAX=16G scripts/capped lake env lean docs/evidence/2026-09-27_packet-a-audit/StrayPanic.lean
GOLEAN_MEM_MAX=16G scripts/capped lake env lean docs/evidence/2026-09-27_packet-a-audit/NoRefusalVacuous.lean
GOLEAN_MEM_MAX=16G scripts/capped lake env lean docs/evidence/2026-09-27_packet-a-audit/PinMutation.lean   # expect EXIT=1, 2 errors
# srcmut: add `(_hn : True)` after `(h : Trace ctx n s c ch sf cf chf)` in GoLean/GoCore/Trace.lean's Trace.erase,
#   prefix the proof with `clear _hn`, run `GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean.GoCore.BridgeSet`, restore
# mem probes: append each mutation in the probe file's header to GoLean/GoCore/ExecutionStatement.lean, run
#   scripts/check-mem-callsites, restore
GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff     # under artifacts/build-lock.d at the primary root
```

## Re-verification at `09c7fb0a` (2026-09-27; this branch rebased onto it)

| File | What |
|---|---|
| `reverify-Proofs.lean` / `.out` | the F1 witness now REFUSES (`#eval` + `step0_not_panic`); `noRefusal_sound` (the corrected `NoRefusal` excludes every refusing run, at every fuel); `finish_replay` (a PROOF of `finish_replay_stmt`); EXIT=0, classical trio only |
| `reverify-StrayPanic-rerun.out` | the ORIGINAL `StrayPanic.lean` re-run: it now FAILS (its `rfl` panic facts no longer hold), EXIT=1 |
| `reverify-ci-diff.tail.txt` | `ci --diff` at `09c7fb0a` + this audit's docs commit: RESULT FAIL on exactly the 5a pair |

Build: `.lake/build` rsynced from the packet-a worktree (identical `git ls-tree` of `GoLean`, `GoLean.lean`,
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`), then `GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean`
EXIT=0. Reproduce: `GOLEAN_MEM_MAX=16G scripts/capped lake env lean docs/evidence/2026-09-27_packet-a-audit/reverify-Proofs.lean`.
