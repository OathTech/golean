# Packet B, the execution bridges — gate tails (window row 2b, 2026-09-28)

[AGENT packet B worker]. Consuming doc: `docs/2026-09-28_packet-b-handoff.md` (§5 cites this dir). Tree: branch
`window/packet-b-bridges-0928`; the gate ran on the working tree whose tracked content is the proofs commit
`f7b15450` PLUS the records commit's two comment-only Lean edits (audit F3: `ExecutionStatement.lean`,
`Machine.lean`) — i.e. exactly the records commit's Lean content. Base: `core/step-label-0928` @ `61bdc65d`. Host:
linux/amd64, the shared 125 G box, under the box-wide build lock. Toolchain: `go version go1.26.5 linux/amd64`
(= `baselines/go-oracle-pin`); Lean `leanprover/lean4:v4.32.2` (lean-toolchain).

| File | What | Producer (repo root) |
|---|---|---|
| `ci-diff-tail.txt` | the `ci --diff` tail: EXIT=1, RED ON EXACTLY THE 5a PAIR (`certificate provenance` STALE — compiled inputs changed; the one cached certified row `imported-goose/channel/google-search` judged stale for that reason), 3768 cases = 3531 / 237 (the reshape lane's numbers), every other step ok (core build warning-free, core totality audit, memory-module inventory, eval tests 295 ok, negative baseline 394 matched, frontend pins); reconciler 2 findings, both standing (C9 = the 5a STALE; C13 doc versions) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (from the baseline diff to the end, ANSI stripped, worktree prefix removed; the summary line appended) |
| `core-audit-tail.txt` | `check-core-audit` PASS: 50 modules (41 under `GoLean.GoCore`, incl. the three new ones), 85 required theorems (audit round F6), classical trio only | `scripts/capped scripts/check-core-audit` |
| `core-audit-mutation.txt` | the fail-closed control: `noRefusal_step` renamed in scratch (its BridgeSet row dropped) → `check-core-audit` EXIT=1 naming the missing constant; reverted | `scripts/capped scripts/check-core-audit` on the mutated tree |
| `mem-callsites-tail.txt` | `check-mem-callsites` PASS, 73 rows (no raw site added) | `scripts/capped scripts/check-mem-callsites` |

Conclusion: the proofs add no behaviour — no baseline row moved beyond the expected 5a line — and every new module is
in the audited closure with no axiom beyond the classical trio.

Audit round (handoff §8): `ci-diff-tail.txt` and `core-audit-tail.txt` were regenerated on the audit-round tree (rebased onto `main` @ `fd1135ff`): same result, 738 s.
