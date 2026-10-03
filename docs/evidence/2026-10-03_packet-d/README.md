# Packet D — the semantic equations, the pool projections, the client and the gate: gate tails (2026-10-03)

[AGENT packet D worker]. Consuming doc: `docs/2026-10-03_packet-d-handoff.md` (§5–§6 cite this dir). Tree: branch
`window/packet-d-equations-1003` off `main` @ `3bb8f4fc` (train r60 close); the gates ran on the working tree whose
tracked content is the proofs commit `5335ee03` (the records commit adds this dir, the handoff and the changelog
line only). Host: linux/amd64, the shared 125 G box, under the box-wide build lock (`artifacts/build-lock.d`, never
taken over), `GOLEAN_MEM_MAX=48G`. Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); Lean
`leanprover/lean4:v4.32.2` (`lean-toolchain`).

| File | What | Producer (repo root) |
|---|---|---|
| `ci-diff-tail.txt` | the `ci --diff` summary and result at the WINDOW-REVIEW round's code commit `43624b55` (the pre-landing round's run had the same verdict at 1261 s): EXIT=1, red on exactly the 5a pair (`certificate provenance` STALE — changed dependency `GoLean.lean`; the one certified row `imported-goose/channel/google-search` PASS→FAIL/membership judged stale), 3821 cases = 3583 PASS / 238 FAIL (237 + the 5a row), negative baseline 394 matched, core build warning-free, the `semantic equations` step ok, 1215 s | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (ANSI stripped; the summary block) |
| `check-equations.txt` | the equation gate's PASS at the WINDOW-REVIEW round (replacing the pre-landing round's tail): client PASS, 293 equation theorems pinned, 12 facts and 15 client-owned helpers, «none unfolds stepFn» (the Lean-level proof-term check over the client-owned closure), the regex pre-filter, TWELVE self-tests at R1 (the `unfold stepFn` regex mutant; deleting `Pin.storeTarget_inv_panic` fails the enrollment check by name; each of the audit's seven unfolding spellings — `exact rfl`, `simp only [stepFn]; rfl`, `delta stepFn; rfl`, `simp_all [stepFn]`, `simpa [stepFn]`, `rw [stepFn]; rfl`, `unfold …stepFn; rfl` — REFUSED by name; the indirect private helper REFUSED naming fact and helper; the imported `rfl`-theorem and the foreign import, R1) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/check-equations` (the non-build lines) |
| `core-audit-tail.txt` | `check-core-audit` PASS at the WINDOW-REVIEW round (replacing the pre-landing round's tail): the closure holds `Equations`, `EquationsAttr`, `PoolProjection`; 329 theorems in the required list (536 total); classical trio only | `scripts/capped scripts/check-core-audit` |
| `elaboration-ab.tsv` | the per-module elaboration A/B against a detached worktree at `main` @ `3bb8f4fc` (fresh `.lake`), alternating sides, two reps each, the module's own artifacts deleted before each single-target build; the lane-only modules as absolute figures | `.tmp/elab-ab.sh` (the script is quoted in the handoff §5) |

| `elaboration-roundc.txt` | the WINDOW-REVIEW round's timings: `Equations.lean` NEW (the law by `rfl`) vs the file at `9c14fef1`, 1.00×; the first `simp` proof's 2.1× that was replaced; `BridgeSet.lean` +1 row | `/usr/bin/time … scripts/capped lake env lean <module>` ×2 under the lock |

RE-VERIFICATION R1 (code commit `6fb3ac16`; handoff §11): `check-equations.txt`, `core-audit-tail.txt` and `ci-diff-tail.txt` are
REPLACED again by that round's tails — 12 self-tests (11 = the imported `rfl`-theorem `stepFn_next_frame`, REFUSED naming fact
and theorem; 12 = the foreign `AuditSupport` import, REFUSED by the whitelist by name), 536 required, `ci --diff` on the CLEAN
committed tree: EXIT=1 on exactly the 5a pair, 3821 = 3583/238, 971 s. The witnesses' lines, reproduced outside the gate:
«fact Tests.EquationClient.fact_via_imported_rfl REFUSED — its proof unfolds stepFn in its helper
GoLean.GoCore.Machine.stepFn_next_frame (it closes rfl by reflexivity)»; «Equation client: import AuditSupport is NOT WHITELISTED
— the client may import only [Init, Std, Lean, GoLean.GoCore.Equations, GoLean.GoCore.EquationsAttr, GoLean.GoCore.Prefix,
GoLean.GoCore.ExecutionStatement, GoLean.GoCore.PoolProjection, GoLean.GoCore.BridgeSet]».

WINDOW-REVIEW ROUND (F1/F2/F4, code commit `43624b55`; `docs/2026-10-03_packet-d-handoff.md` §10): `check-equations.txt` and
`core-audit-tail.txt` are REPLACED by the round's tails (10 self-tests; 536 required theorems); `ci-diff-tail.txt` is the
round's `ci --diff` summary (EXIT=1 on exactly the 5a pair, 3821 = 3583/238, 1215 s). The F2 reproducer, rebuilt from the gate's
recipe outside the gate (`.tmp`, deleted), fails with: «`Equation client: fact Tests.EquationClient.fact_usage_simp_set
REFUSED — its proof unfolds stepFn in its helper Tests.EquationClient.returnViaReduction (it closes Eq.refl …`».

Conclusion (the pre-landing round; the window-review round changes none of it): the additions change no behaviour (no baseline row moved beyond the 5a line; the whole-corpus numbers are the preprint lane's), every new module is in the audited closure with no axiom beyond the classical trio, the equation gate passes with both self-tests, and no existing module's elaboration got slower (PrefixFacts 0.67×); the one ratio over the G-C3 1.5× line is BridgeSet's additive growth from 263 pinned rows (1.0 → 1.9 s), reported, not a proof-cost regression. Run 2026-10-03 06:56–07:55 UTC.
