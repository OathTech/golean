# Packet D — the semantic equations, the pool projections, the client and the gate: gate tails (2026-10-03)

[AGENT packet D worker]. Consuming doc: `docs/2026-10-03_packet-d-handoff.md` (§5–§6 cite this dir). Tree: branch
`window/packet-d-equations-1003` off `main` @ `3bb8f4fc` (train r60 close); the gates ran on the working tree whose
tracked content is the proofs commit `5335ee03` (the records commit adds this dir, the handoff and the changelog
line only). Host: linux/amd64, the shared 125 G box, under the box-wide build lock (`artifacts/build-lock.d`, never
taken over), `GOLEAN_MEM_MAX=48G`. Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); Lean
`leanprover/lean4:v4.32.2` (`lean-toolchain`).

| File | What | Producer (repo root) |
|---|---|---|
| `ci-diff-tail.txt` | the `ci --diff` summary and result: EXIT=1, red on exactly the 5a pair (`certificate provenance` STALE — changed dependency `GoLean.lean`; the one certified row `imported-goose/channel/google-search` PASS→FAIL/membership judged stale), 3821 cases = 3583 PASS / 238 FAIL (237 + the 5a row), negative baseline 394 matched, core build warning-free, the new `semantic equations` step ok, 1261 s | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (ANSI stripped; the summary block) |
| `check-equations.txt` | the equation gate's PASS: client PASS, 229 equation theorems pinned, 7 facts, the no-unfold guard, the two self-tests (an `unfold stepFn` mutant trips the guard; deleting `Pin.storeTarget_inv_panic` fails the enrollment check by name) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/check-equations` (the non-build lines) |
| `core-audit-tail.txt` | `check-core-audit` PASS: the closure now holds `Equations`, `EquationsAttr`, `PoolProjection`; 263 theorems added to the required list; classical trio only | `scripts/capped scripts/check-core-audit` |
| `elaboration-ab.tsv` | the per-module elaboration A/B against a detached worktree at `main` @ `3bb8f4fc` (fresh `.lake`), alternating sides, two reps each, the module's own artifacts deleted before each single-target build; the lane-only modules as absolute figures | `.tmp/elab-ab.sh` (the script is quoted in the handoff §5) |

Conclusion: the additions change no behaviour (no baseline row moved beyond the 5a line; the whole-corpus numbers are the preprint lane's), every new module is in the audited closure with no axiom beyond the classical trio, the equation gate passes with both self-tests, and no existing module's elaboration got slower (PrefixFacts 0.67×); the one ratio over the G-C3 1.5× line is BridgeSet's additive growth from 263 pinned rows (1.0 → 1.9 s), reported, not a proof-cost regression. Run 2026-10-03 06:56–07:55 UTC.
