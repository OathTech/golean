<!-- VERBATIM COPY for GoLean's records. Source: raft-proofs (~/projects/raft-proofs, read-only), branch docs/golean-response-0930, commit f3d857f36c9085003e4788b512709cdb7dc8f754, file docs/2026-09-30_note-to-golean-subject-deltas.md, sha256 65d939359cf7a32e94dd82c7c9ae66b08fd5653a85bf36669d9ef3cd4f4d6920 (88 lines). Relayed by the [USER] 2026-09-30; copied unchanged by the [AGENT] worker, lane records/raft-deltas-0930. The [USER]'s rulings on it: docs/2026-08-31_qrow-rulings.md, «The raft-proofs team's subject-delta note (2026-09-30) — RULED»; the feasibility note it asked for: docs/2026-09-30_protobuf-route-a.md. -->

# raft-proofs note to GoLean: `raftsubject` deltas and a route to real raft

2026-09-30. From the raft-proofs orchestrator to the GoLean team. A
proposal for our user to relay. It authorizes nothing on your side.

**[USER]** raft-proofs' user: "The ideal here is that they target the *real*
raft, but there may be profound reasons that won't work." golean-logic's
user added an executability condition: "we want GoLean to be executable.
So our contract *can't* just treat protobuf as abstract."

**[AGENT]** golean-logic's census and reply
(`golean-logic docs/cluster3-census-0930` @ `61a0b69`) find nothing in their
logic that blocks targeting the real etcd-io/raft at `56e32004`. The
subject deltas live in your `raftsubject/` and
`tools/raftsubject/derive.py`, so golean-logic suggested we raise them with
you directly. The facts below come from a mechanical diff of every
`raftsubject/**/*.go` file (GoLean `883ebc36`) against upstream, after
import paths were rewritten. Please correct anything we misread.

## 1. What we found

About 95% of `raftsubject/` is upstream text with only import paths
rewritten. The substantive deltas, using your ledger's ids:

| Delta | What | Possible route to upstream |
| --- | --- | --- |
| D-6/7 | Import paths `go.etcd.io/raft/v3/X` become `X` | A module-path mapping in the frontend |
| D-8, D-10 | `node.go` reduced to `node_decls.go`; `state_trace.go` not vendored | Keep. These are scope cuts that our mirror shares (RawNode level, default build). |
| D-1/2/4/9 (+JC-13/14/15) | protobuf-go runtime replaced by a plain generated codec | An exactly faithful executable protobuf route (§2) |
| D-3 | ConfState errors: `fmt` `%+#v` dumps become fixed errors | `%+#v` lowering, once D-1 is resolved |
| D-11 | `lockedRand.Intn`: `crypto/rand` becomes map-`range` choice | A native `Intn` pick site (§2) |
| D-12 (H-20) | `log.New(...)` defaults become `&DefaultLogger{}` | Your H-20; until then, a "Logger installed" premise |

**Three behavior differences, visible through RawNode, that we could not
find in your ledger:**

- **U-1.** Malformed ConfChange proposal data. `raft.go:1314,1320` panic
  with the Unmarshal error **value**. The subject returns
  `"plainpb: malformed wire input"` (`plain_codec.go:39`), while protobuf-go
  returns `"proto: cannot parse invalid wire-format data"`, whose spacing
  (a non-breaking space) varies by build. The `plain_codec.go:35–38`
  header says raft observes only whether the error is nil.
  `raft.go:1314` contradicts that, and the header should be corrected.
- **U-2.** Unknown groups (wire types 3/4) are rejected
  (`plain_codec.go:82`). protobuf-go skips them, and upstream accepts such
  proposal data.
- **U-3.** Unknown fields are dropped. Upstream retains them, re-encodes
  them, and `proto.Size` counts them.

## 2. Proposals: routes that keep GoLean executable

- **Election draw.** A **native choice-tape pick site** for
  `(*lockedRand).Intn(n)`, returning some `v ∈ [0, n)` and panicking if
  `n ≤ 0`. That replaces D-11 and keeps upstream's `raft.go` text. The
  census shows exactly one call site, `resetRandomizedElectionTimeout`
  (upstream `:2054`), executed on every run. golean-logic needs one step
  rule for it and estimates 1–2 sessions after the re-pin.
- **Protobuf.** Either:
  1. a lowered Go codec that is **exactly faithful** to protobuf-go where
     raft can observe it: unknown fields retained and counted, unknown
     groups skipped, protobuf-go's error values, and the per-build spacing
     as a build parameter or tape choice; or
  2. a **GoLean-native executable definition** of
     `Clone`/`Equal`/`Marshal`/`Unmarshal`/`Size` over the nine raft
     schemas.

  Either would be validated differentially against protobuf-go. The
  census gives the scope: `Clone`/`Equal`/`Size`/`Unmarshal` over the
  reached messages, and `Marshal` only for ConfChange on the auto-leave
  path. golean-logic's view is that route 2 is likely cheaper for its
  proofs. The choice is yours.
- **Smaller items.** A module-path mapping (D-6/7), `%+#v` (D-3), and H-20
  (D-12), as convenient.

## 3. What we can supply

Our executable Lean mirror follows upstream behavior exactly on these
paths: protobuf-go's decode errors including the spacing bit, unknown-field
and group handling, and the `%+#v` ConfState dump. We also have a native
differential harness with a malformed-bytes corpus (26 entries). Both can
serve as reference evidence for whichever protobuf route you choose.

## 4. What changes if a delta must stay

If you find a profound reason a delta cannot be removed, we would like to
record it as a fundamental delta with its justification. The end-to-end
claim would then carry it as an explicit premise, in golean-logic's §2.4
form: a hypothesis about the program's actual callee, discharged later.
