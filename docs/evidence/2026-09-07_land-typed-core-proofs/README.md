# Gate tail for landing chunk L1 `land/typed-core-proofs` — the typed-consumer sprint's additive layer on main (2026-09-07)

[AGENT] landing worker, 2026-09-07. Consuming doc:
`docs/2026-09-07_land-typed-core-proofs.md` §7 (which cites this directory).

Tested commit: `bfcd3d77d9b0b2fae58ca182bed56966aa1cc5f5` (`refs/snapshots/land-typed-core-gated`), a CLEAN
tree: `full.meta.tsv` and `negative.meta.tsv` (the run's own records) carry
`git_commit	bfcd3d77d9b0b2fae58ca182bed56966aa1cc5f5`, `git_dirty	false`, `jobs	2`. The final landing commit
(the commit carrying this directory; `git log -1 -- docs/evidence/2026-09-07_land-typed-core-proofs`) differs from it ONLY by this evidence directory and §7.6–§7.7 of
the note (documentation-only amend, the same practice as
`../2026-09-05_semantic-interface-integration/`). The tested tree's
`GoLean/GoCore/{Machine,Ops,StepFn,Multi,MachineSound}.lean`, `GoLean/CLI.lean`
and `GoLean/NativeToIR.lean` are byte-identical to main `47195683`; the
oracle pin (`baselines/go-oracle-pin` = go1.26.5) and every baseline file are
byte-identical to main; ZERO baseline drift was the expectation and the result.

Contents (gate tails only; no archives, no source copies, every file < 256 KiB):

- `ci-diff.log` — `scripts/capped scripts/ci --diff` at the tested commit, complete stdout+stderr.
- `spike-gate-a1.log`, `spike-iris-customer.log` — the two opt-in spike gates (outside the default build and the ci graph), same tree.
- `probes.log` — the ad hoc landing probes quoted in the note §7.3–§7.5 (axiom prints, non-vacuity `#eval`s, fresh-artifact comparison, fixture differentials, the eight audit harnesses).
- `full.meta.tsv`, `negative.meta.tsv` — the differential and negative runs' meta records (`git_commit`, `git_dirty`, `jobs`, timeouts, oracle pin).
- `SHA256SUMS` — binds this directory (excluding itself).

Reproduce from the repository root at the tested commit (Go `go1.26.5 linux/amd64`
= the pin; Lean per `lean-toolchain`; host linux/amd64, 32 cores / 125 GiB,
load ≈ 3 with no other heavy lane; every Lean/Lake invocation via `scripts/capped`):

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 scripts/capped scripts/ci --diff
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash spikes/gate-a1/check
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 bash spikes/iris-customer/check
```

The envelope (16 GiB / 3 Lean threads / 2 coverage workers) is the sprint's
recorded lane-coordination limit, applied as the safe reading of a
[USER]-relayed constraint auditor A cites; main's previous full pin (BUG-103)
ran with `jobs 8`. Worker count affects duration and timeout exposure, not
what is compared.

Conclusion: `scripts/ci --diff` RESULT: PASS at the tested commit — core build warning-free, 202/202 eval tests, `differential coverage summary: cases=3598 pass=3353 fail=245`, `baseline diff FULL (3598/3598, no regression)`, negative baseline diff no regression, reconciler 3 findings / 0 HIGH (report-only), wall 2265.30 s. ZERO baseline drift: the shipped machine is unchanged, so no row moved and no re-pin is owed. Both opt-in spike gates PASS (gate-a1 17.80 s; iris-customer 134.27 s, 136 exports, 15,212 constants, 25 compiled poison controls rejected by name, both fresh native artifacts equal the proved programs, 5/5 fixture differential). The probe log records the axiom prints (standard trio; the two `_iff` checkers on `propext`/`Quot.sound` only), the non-vacuity `#eval`s, the fresh-artifact equalities and the eight post-import audits, all exit 0. Absolute scratch paths inside the transcripts are the gates' own output and are left verbatim.
