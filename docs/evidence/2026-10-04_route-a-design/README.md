# Evidence — protobuf route A design (2026-10-04)

[AGENT] design worker, lane `design/route-a-protobuf-1004`, `main` @ `450412a7`. The small witnesses behind
`docs/2026-10-04_route-a-protobuf-design.md` §1 and §3. Scratch programs kept as `.go.txt` (no Go tool picks them up);
reproduce from the repo root in `.tmp/`. Nothing here is a gate input; every file opens with or is a record of a
DIAGNOSTIC or a probe run.

## Files

- `lower-diagnose-twin-head.txt` — the head of `scripts/lower-diagnose .tmp/twin-prog --json --tsv` over the twin assembly
  (`raftsubject/{quorum,raftpb,tracker,proto,confchange,raft}` + `tools/raftsubject/twin-lib.go`, `twin-chdriver.go`,
  `twin-chdriver-main.go` — the program `scripts/check-frontend-pins` emits): EXPORT OK; static 690/696; `raftpb` 250/250,
  `proto` 6/6; refused keys `os.Exit` ×2, `log.Logger.Panic`/`Panicf`, `math/rand.Intn` (static-pass staleness — the dynamic
  pass lowers it through the `rand-intn` primitive); may-refuse `!with_tla`; 31 stdlib wire quarantines, none protobuf.
- `lower-diagnose-proto-a-head.txt` — the same over the 2026-09-30 prototype codec
  (`docs/evidence/2026-09-30_protobuf-route-a/proto-a.main.go.txt` copied to `.tmp/proto-a/main.go`): 35/36, the one refusal
  `errors.Is` (FR-14, `reflectlite.TypeOf`).
- Upstream `raftpb` verbatim (`deps/raft/raftpb/*.go` minus tests, copied to `.tmp/upstream-raftpb`): `lowerdiag: the program
  does not type-check (3 error(s))` — `google.golang.org/protobuf/proto`, `…/reflect/protoreflect`, `…/runtime/protoimpl`
  unresolvable (GOROOT/GOPATH only). Recorded here as text; no report file is produced for a non-type-checking target.
- `dispatch-probe/{proto.go.txt,pb.go.txt,main.go.txt}` — the A1-shape probe: `proto` dispatches through an interface
  (`m.(methods)`) and does NOT import the generated package; `pb` imports `proto`; `prefixError` + `Unwrap()` to the sentinel;
  the init pick `var prefix = pickPrefix()` over a two-key map range (U+00A0 spelled ` `); `probePanic` does
  `panic(err)` with the `*prefixError` payload. Layout for `go run`: a GOPATH scratch (`.tmp/gopath/src/{dispatch,pb,proto}`).
- `dispatch-probe/runs.txt` — both oracles. `go run`: `-5 45` then `panic: proto: cannot parse invalid wire-format data`
  (exit status 2). Machine (`GO111MODULE=off go run ./tools/nativefrontend --dir .tmp/dispatch --out …`, wire 129,578 B;
  `golean native-json-run --function F --fuel 5000000`, the `main` binary built 2026-10-03 21:26, GoLean/ last changed at
  `43624b55`): `probeDispatch` → `-5`, `probePrefixLen` → `45`, `probePanic` → `status: panic`, message
  `proto: cannot parse invalid wire-format data`. Reading: checks 1–4 (retention + re-encode order, Size, Clone/Equal) pass
  on both legs; check 5 returns −5 on BOTH because an `AppendMessage`-style dispatch answers `[]byte{}` for a TYPED-NIL
  message where protobuf-go answers `nil` (`proto/encode.go:141-146`) — today's `proto.go` `nonNil` has the same answer;
  design D2 adds `IsNilMessage()` and §5 births the `typed-nil-*` rows. 45 = the U+00A0 member on both legs this run (the
  machine's slot 0 = first key in cell order; gc's draw happened to agree). The abort line renders: BUG-004 item 4 (unit 6b)
  has landed, so the feasibility note's C3 is discharged.

## Commands (2026-10-04, go1.26.5, protobuf-go v1.36.11 read from `/home/dev/go/pkg/mod`, no network)

```
scripts/lower-diagnose .tmp/twin-prog     --json --tsv --out artifacts/lower-diagnose/route-a-twin
scripts/lower-diagnose .tmp/proto-a       --json --tsv --out artifacts/lower-diagnose/route-a-proto
scripts/lower-diagnose .tmp/upstream-raftpb           --out artifacts/lower-diagnose/route-a-upstream   # does not type-check
GOPATH=$PWD/.tmp/gopath GO111MODULE=off go run dispatch
GO111MODULE=off go run ./tools/nativefrontend --dir .tmp/dispatch --out .tmp/dispatch.wire.json
.lake/build/bin/golean native-json-run --input .tmp/dispatch.wire.json --function probeDispatch --fuel 5000000   # and the other two
```

The worktree had no `deps/`; `deps/go` and `deps/raft` were symlinked (inside the gitignored `deps/` directory) to the primary
checkout's reference clones at the pins. Scratch under `.tmp/` and `artifacts/lower-diagnose/route-a-*` deleted at the lane's end.
