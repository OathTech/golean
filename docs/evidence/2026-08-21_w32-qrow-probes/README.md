# Q-row memo probes (2026-08-21, W3.2 slice 2)

Probes run for `docs/2026-08-21_w32-qrow-memos.md`. Oracle: gc
go1.26.5 linux/amd64 (the CI pin), `GOCACHE` repo-local per the
sandbox convention.

## probe_initspawn.go — during-init execution of an init-spawned child

Question it discriminates (Q-INITSPAWN): does gc run a goroutine
spawned by `init` WHILE initialization code is still running (i.e.
before `main` starts), or only after init completes? The case-in-hand
(`goroutines/spawn-in-init/in-init`) cannot discriminate this — its
main blocks on a channel the child fills, which is satisfied whenever
the child eventually runs.

Shape: `init` spawns a child that sends on a buffered channel, burns
~2·10⁸ iterations of registry-free work, then polls the channel with
`select`+`default` BEFORE init returns. Output `observedInInit byMain`
where `observedInInit`=1 means the child ran during init.

Result:

| config | runs | `1 1` (child ran during init) | other |
| --- | --- | --- | --- |
| default GOMAXPROCS | 20 | 20 | 0 |
| GOMAXPROCS=1 | 20 | 20 | 0 |

Reading (two-bounds discipline): a lower-bound fact — gc EXHIBITS the
during-init member, in both configs (at GOMAXPROCS=1 via async
preemption of the registry-free loop). Consequence for the memo: any
model that parks init-spawned children until `main` starts excludes an
observed behavior (`observed ∉ modeled` — definitionally a bug), so
the deferred-release implementation shortcut is FORECLOSED. The spec
side (upper bound) is argued in the memo from
spec#Package_initialization's "may launch other goroutines, which can
run concurrently with the initialization code".
