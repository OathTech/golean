# `raftsubject/` — the vendored raft SUBJECT TREE

The etcd-io/raft source the machine verifies, vendored at the frontend's
short dot-free import paths and **entirely derived** by
`tools/raftsubject/derive.py` from `deps/raft` @ `56e3200`.

**Do not edit anything under this directory.** Every file is regenerated;
edit the derivation (`tools/raftsubject/derive.py` — its rules, its
recorded `SUBJECT_PATCHES`, or its codec generator) and re-run it. `derive.py --check` fails if the
tree and the derivation have drifted.

```
raftsubject/
  raftpb/     plainpb — raft's wire types DECLARED, protobuf runtime stripped
              (unknownFields kept), plus the generated route A codec
  quorum/     upstream verbatim (import paths rewritten)
  tracker/    upstream verbatim (import paths rewritten)
  confchange/ upstream verbatim (import paths rewritten)
  proto/      generated — the subject-local protobuf stand-in (route A:
              interface dispatch into the generated codec, since 2026-10-04)
  raft/       the root package (W2.2+): verbatim, plus node_decls.go (a
              declaration subset of node.go) and the recorded subject
              patches D-11 (the jitter draw — since 2026-09-30 one
              call into the machine's general [0, n) pick site,
              math/rand.Intn; docs/raft-w42-log.md) and D-12 (logger
              initializers — logger.go is upstream verbatim since W4.2;
              the harness supplies the Logger through both seams)
```

## Why the packages sit at short paths

`quorum`, `raftpb`, `tracker` rather than `go.etcd.io/raft/v3/...`: the native
frontend resolves local packages case-relatively and the path is the package's
identity key, so `path == name` is what makes rendering exact and lets one
tree feed both the machine and the `go run` oracle
(`docs/2026-08-18_multipackage-identity.md` §4/§6). The rewrite is the ONLY
change made to a `verbatim` file.

## What is NOT upstream

Four things, each argued and itemised in `docs/raft-w2-log.md`'s
subject-delta ledger (continued in the W3, W4.1 and W4.2 logs) and in the
header comment of the file itself:

1. **`raftpb/raft.pb.go`** — mechanically stripped: wire types, field
   numbers, enums, every getter and (since route A, D3) the `unknownFields
   []byte` store KEPT; the runtime's `state`/`sizeCache` fields, the
   file-descriptor machinery and `ProtoReflect` gone;
   `String`/`Descriptor`/`EnumDescriptor`/`UnmarshalJSON` are fail-closed
   panics; enum `String` is real.
2. **`raftpb/plain_wire.go`, `plain_codec.go`, `plain_clone.go` +
   `proto/proto.go`** — GENERATED, not upstream: protobuf route A
   (`docs/2026-10-04_route-a-protobuf-design.md`, ratified 2026-10-04; slice
   S1): a reflection-free codec decomposed function-for-function after
   protobuf-go v1.36.11's `protowire`/`internal/impl` (each function names its
   twin by file:line; the FuncId/footprint table is
   `tools/raftsubject/codec-funcids.tsv`), dispatched from the subject-local
   `proto` package through an interface; the `*prefixError` value with its
   `Unwrap` sentinel; the per-binary prefix spelling as ONE init-time
   `rand.Intn(2)` pick. Validated EXACTLY against the real runtime by
   `difftest.py` sections 7-8 and under both oracles by `codeccheck.py`. The
   2026-09-30 deltas U-1 (the error value), U-2 (unknown groups) and U-3
   (unknown fields) are resolved by this codec (`docs/raft-w42-log.md`, the
   2026-10-04 ledger continuation).
3. **`raftpb/confstate.go`** — upstream text plus the recorded exact-text
   patch D-3: its two `fmt.Errorf` lines become `errors.New` over the fixed
   text (the verdict is upstream's; the `%+#v` dumps are a PERMANENT stated
   inexactness). `raftpb/confchange.go` is upstream VERBATIM since route A
   (the W2 overlay retired). `raft/logger.go` is upstream verbatim plus the
   recorded D-12 initializer patch (`docs/raft-w42-log.md`).
4. **`raft/raft.go`** — the recorded D-11 patch (the jitter draw, one
   `math/rand.Intn` call on the machine's pick site).

Everything else — including the parts the frontend cannot lower yet
(statement-position `copy`, `panic(fmt.Sprintf(...))`, the `String`/`Describe`
rendering methods) — is upstream text, unaltered, so those refuse honestly
instead of being papered over. The current refusal inventory is in
`docs/raft-w2-log.md`; reproduce it with `tools/raftsubject/frontier.py`.

## Reproduce

```
tools/raftsubject/derive.py --check    # tree matches the derivation
tools/raftsubject/difftest.py          # plainpb + proto agree with upstream raftpb + protobuf-go (sections 1-8)
tools/raftsubject/frontier.py          # the refusal inventory
```
