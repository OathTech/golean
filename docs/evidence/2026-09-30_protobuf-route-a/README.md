# Evidence — protobuf route A feasibility (2026-09-30)

[AGENT] worker, lane `records/raft-deltas-0930`, `main` @ `883ebc36`. The witnesses behind
`docs/2026-09-30_protobuf-route-a.md` §2–§4. Scratch programs, kept small (`.go.txt` so no Go tool
picks them up as packages); reproduce in `.tmp/` from the repo root. Nothing here is a gate input.

## Files

- `proto-a.main.go.txt` — the stdlib-only prototype codec (ConfChange / ConfChangeSingle /
  ConfChangeV2): unknown-field retention, depth-limited group skipping, the `prefixError` value with
  the sentinel, the prefix spelling picked once at package init by the map-range idiom; the 26-entry
  raft-proofs corpus inlined; probes `routeAProbe` / `routeAPrefixLen` / `routeAErrText` / `routeAPanic`.
- `protoref.main.go.txt` + `protoref.go.mod.txt` — the REFERENCE leg: real protobuf-go v1.36.11 over
  upstream `raftpb` (`replace go.etcd.io/raft/v3 => deps/raft`), same corpus; built from the module
  cache with `GOPROXY=off GOSUMDB=off GOFLAGS=-mod=mod`, `go.sum` copied from `raftharness/go.sum`.

## Runs (2026-09-30, go1.26.5, protobuf-go v1.36.11 from `/home/dev/go/pkg/mod`)

Reference leg (`cd .tmp/protoref && GOPROXY=off GOSUMDB=off GOFLAGS=-mod=mod go run .`), abridged —
16 `ERR`, all `is-sentinel=true len=44 text="proto: cannot parse invalid wire-format data"
type=*errors.prefixError` (this binary's `detrand` bit realized U+0020); the 10 decodes:

```
v1-varint-ten-bytes-max OK size=11 len=11 re=08ffffffffffffffffff01
v1-type-as-bytes OK size=3 len=3 re=120100
v2-changes-as-varint OK size=2 len=2 re=1005
v1-unknown-varint OK size=2 len=2 re=2801
v2-unknown-all-wire-types OK size=31 len=31 re=120608011002180148015101020304050607085a0161630802646d0a0b0c0d
v1-unknown-field-number-max OK size=6 len=6 re=f8ffffff0f01
v1-nil OK size=0 len=0 re=
v1-empty OK size=0 len=0 re=
v2-nil OK size=0 len=0 re=
v2-empty OK size=0 len=0 re=
panic: proto: cannot parse invalid wire-format data
```

Prototype under `go run` (`cd .tmp/proto-a && GO111MODULE=off go run .`): the same 16/10 split, the
same ten `size=/len=/re=` lines byte for byte, `is-sentinel=true`; error length 45 — this process's
init pick realized U+00A0 (both members of the latitude exhibited across the two legs);
`panic: proto: cannot parse invalid wire-format data` (the U+00A0 spelling), exit status 2.
The probe build: `probe 0 prefixlen 8 errtext 91`.

Prototype on the MACHINE (`artifacts/nativefrontend --dir .tmp/proto-a --out .tmp/proto-a.wire.json`,
then `.lake/build/bin/golean native-json-run --input .tmp/proto-a.wire.json --function F --fuel 30000000`,
the `main` @ `883ebc36` binary):

```
routeAProbe      {"status":"ok","values":[{"kind":"int","tag":"int","value":0}]}      all 26 verdicts + sizes = reference
routeAPrefixLen  {"status":"ok","values":[{"kind":"int","tag":"int","value":8}]}      slot-0 member = U+00A0
routeAErrText    {"status":"unsupported","message":"normalizing frontend-quarantined: errors.Is: package-selector call reflectlite.TypeOf (package \"internal/reflectlite\" surface not modeled)"}
routeAPanic      {"status":"unsupported","message":"panic abort rendering for payload GoLean.GoValue.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined 3)) (GoLean.GoValue.addr (GoLean.Loc.base { id := 14 })) (dynamic type *main.prefixError)"}
```

`scripts/lower-diagnose .tmp/proto-a`: `EXPORT OK (rc 0)`, «declarations demanding nothing refused:
30 / 30 (100.0%)»; the one quarantined declaration is `errors.Is` (FR-14, `reflectlite.TypeOf`).

`difftest.py` section 7, offline: `TMPDIR=$PWD/.tmp GOPROXY=off GOSUMDB=off GOFLAGS=-mod=mod python3
tools/raftsubject/difftest.py --out .tmp/difftest --keep` → `ok  Codec  72 values: bytes, Size, and
both cross-unmarshals across all 9 message types` / `PASS plainpb agrees with upstream raftpb on
every probed value` (19 `NOTE codec-nil` lines: `AppendMessage(nil)` of an empty message is nil where
`proto.Marshal` is a non-nil empty slice — the `proto.go` dispatch's `nonNil` fixup covers raft's
call; invisible to `proto.Equal`).

Twin wire pin after the comment fix: fresh emit `0b58402a7699e7bba9ce3ee3c232e8850489e88595557ce9c3548e6baa1e4c14`
= `baselines/pins/twin-chdriver.wire.json`; `hidden-dep-order` observation and `stdlib-pin.tsv` (61 rows)
reproduced unchanged (the three steps of `scripts/check-frontend-pins` run by hand with the `main`
binary — the worktree has no Lean build).
