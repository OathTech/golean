# The quorum-pilot subject: REAL etcd-io/raft source

`main.go` vendors the quorum decision procedures from
`deps/raft/quorum/{quorum.go,majority.go}` with function bodies
VERBATIM (compare with `diff` against upstream). Delta from upstream,
per `docs/2026-07-30_quorum-extern-policy.md`:
- package clause `quorum` → `main`;
- import block reduced to the vendored subset's needs (`math`,
  `slices`);
- `String()`/`Describe()` (fmt/strings rendering), `VoteResult` (own
  case later), and the generated stringer file omitted.

Drivers encode etcd's own `testdata/majority_commit.txt` rows; `go run`
on this file IS the oracle (running the real code), and the phase-4
proof pins this file's lowering.
