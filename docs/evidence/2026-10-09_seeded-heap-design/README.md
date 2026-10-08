# Evidence: seeded-heap design probes (2026-10-09, [AGENT] design worker, lane design/seeded-heap-1009)

Small, tail-only; the bulk (`.tmp/seed-probe/`: the wire, the Go build cache) was pruned at lane close. gc-verified's
`p0b/subject.go` was COPIED from `~/projects/gc-verified/worktrees/integration/next/tools/mem0-probes/p0b/` (read-only;
not committed here — its subjects `inc`, `swap2`, `sum2`, `add3`, `addNaive` are quoted in the note).

| file | what |
|---|---|
| `prologue-main.go` | hand-written prologues (aliased vs distinct `addNaive`, cyclic `sum2`, aliased `swap2`) — P1's Go side |
| `p1-p2-go-and-machine-twins.txt` | P1 `go run` output; P2 the same package through the pinned frontend + `golean native-json-run` (identical); the wire's named-type keys (`main.cell`, `main.Node`) and the pointer parameter types |
| `probe-seeded-store.lean` | P3: a two-phase hand seed (zero cells, then stores) after `runPkgInitM`, through the EXISTING `bindParams`/`allocDecls`/`pinResultLocs`/`runConfig`; plus the bind-only `StateWf` checks |
| `p3-seeded-store.txt` | P3's output: `inc` 41→42; aliased 12 19 vs distinct 12 12 / 5 7; cyclic result 5 with raw `.addr` ids in the cells; the two gaps (dangling `.addr` passes `bindParams`, entry store NOT `StateWf`; `.int` at `*int` passes normalization) |
