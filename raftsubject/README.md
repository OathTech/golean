# `raftsubject/` — the vendored raft SUBJECT TREE

The etcd-io/raft source the machine verifies, vendored at the frontend's
short dot-free import paths and **entirely derived** by
`tools/raftsubject/derive.py` from `deps/raft` @ `56e3200`.

**Do not edit anything under this directory.** Every file is regenerated;
edit the derivation (`tools/raftsubject/derive.py`, or an overlay under
`tools/raftsubject/overlay/`) and re-run it. `derive.py --check` fails if the
tree and the derivation have drifted.

```
raftsubject/
  raftpb/     plainpb — raft's wire types DECLARED, protobuf runtime stripped
  quorum/     upstream verbatim (import paths rewritten)
  tracker/    upstream verbatim (import paths rewritten)
  raft/       logger.go only: the W2.2 no-op Logger injection
```

## Why the packages sit at short paths

`quorum`, `raftpb`, `tracker` rather than `go.etcd.io/raft/v3/...`: the native
frontend resolves local packages case-relatively and the path is the package's
identity key, so `path == name` is what makes rendering exact and lets one
tree feed both the machine and the `go run` oracle
(`docs/2026-08-18_multipackage-identity.md` §4/§6). The rewrite is the ONLY
change made to a `verbatim` file.

## What is NOT upstream

Three things, each argued and itemised in `docs/raft-w2-log.md`'s
subject-delta ledger and in the header comment of the file itself:

1. **`raftpb/raft.pb.go`** — mechanically stripped: wire types, field
   numbers, enums and every getter KEPT; `Marshal`/`Unmarshal`/`Size` absent
   entirely (marshal-avoidance); `String`/`Descriptor`/`EnumDescriptor`/
   `UnmarshalJSON` are fail-closed panics; the file-descriptor machinery and
   `ProtoReflect` are gone.
2. **`raftpb/plain_clone.go`** — GENERATED, not upstream: plain-Go
   `CloneMessage`/`EqualMessage` standing in for `proto.Clone`/`proto.Equal`,
   which raft calls on its normal paths. Differentially validated against the
   real protobuf runtime by `tools/raftsubject/difftest.py`.
3. **`raftpb/confstate.go`, `raftpb/confchange.go`, `raft/logger.go`** —
   overlays (upstream digests pinned in the derivation, so a pin move fails
   loud).

Everything else — including the parts the frontend cannot lower yet
(statement-position `copy`, `panic(fmt.Sprintf(...))`, the `String`/`Describe`
rendering methods) — is upstream text, unaltered, so those refuse honestly
instead of being papered over. The current refusal inventory is in
`docs/raft-w2-log.md`; reproduce it with `tools/raftsubject/frontier.py`.

## Reproduce

```
tools/raftsubject/derive.py --check    # tree matches the derivation
tools/raftsubject/difftest.py          # plainpb agrees with upstream raftpb
tools/raftsubject/frontier.py          # the refusal inventory
```
