# Typed-contract design-review evidence

[AGENT] independent reviewer, 2026-09-05. Source baseline:
`10fefeb3e6fbb3f7cb6630b8b559a9a7e7915e97`; its `GoLean/` tree is unchanged
from main `471956831251e428df3a64c5b8fc7fb79cbebbfc`. This evidence checks
specific contract counterexamples over that machine; it is not the final
sprint build, a full differential gate, or an implementation approval.

Run from the `typed-contract-review` worktree root:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env lean \
  docs/evidence/2026-09-05_typed-contract-design-review/ContractProbes.lean
python3 docs/evidence/2026-09-05_typed-contract-design-review/check-go.py
```

Both commands exited 0. The Lean command freshly elaborated eleven named
theorems against a reviewer-owned build directory. A separate capped
`lake build` rebuilt unchanged baseline modules and passed (76 jobs;
[build.log](build.log)); the probe file was freshly elaborated again after
that build. No runtime source was changed. Its `#print axioms` output
is in [probes.log](probes.log); only `propext` and `Quot.sound` occur. The
proofs include no native evaluation or additional axiom assumptions.

The Python script runs the five standalone Go files individually, with
`GO111MODULE=off` and `GOCACHE` in this worktree's `artifacts/go-build-cache`.
Each `go run` exits 1 after a real Go panic, as expected; the script requires
a first-line panic report and succeeds only when each probe supplies it.
[go-probes.json](go-probes.json) records the original first-line bytes as
hex, plus a human-readable UTF-8 view. The `\\xff` display is escaped for
readability; the hex bytes are authoritative. These commands do not run the
GoLean frontend or compare a complete GoLean driver execution.

The local oracle was `go version go1.26.5 linux/amd64`, GOROOT `/usr/local/go`.
The reviewed spec/runtime source hashes are in [source-hashes.json](source-hashes.json),
along with the relevant current-machine source and inspected reference files.
`SHA256SUMS` seals this evidence directory's files other than itself.

The containing [review report](../../2026-09-05_typed-contract-design-review.md)
states the findings, candidate contracts and remaining proof obligations.
