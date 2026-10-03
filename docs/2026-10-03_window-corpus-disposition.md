# Window corpus lanes CL1–CL5: disposition (2026-10-03)

[AGENT] worker, branch `records/window-corpus-cl-1003`. Answers the window review's F3
(`docs/2026-10-03_window-review.md` on `review/window-1003` @ `66d09ab5`): every corpus
commitment of charter §4 (`docs/2026-09-23_batched-window-charter.md`; window plan row CL;
origin: the logic team's response §5) is split into its stated subconditions, each mapped
to case IDs whose fixture body was read to confirm it exercises the subcondition. Rows were
added ONLY for the uncovered subconditions (39 rows, all born PASS; baseline 3821 → 3860 =
3623 / 237). Status = `baselines/native-full.tsv` at this branch. Every row is a
differential row against go1.26.5. A miniature fixture is NEVER «a proof of Raft» (§5).
The customer's own code (`raftsubject/`) also runs under the machine in the twin
(`tools/raftsubject/twin-*`); that is end-to-end evidence, not per-subcondition coverage.

## CL1: direct methods + multi-field records (`Progress.MaybeUpdate`)

| Subcondition | Case IDs | Status | Note |
|---|---|---|---|
| Customer shape (first row) | `methods/maybe-update-shape/{advance-then-stale,advance-twice,equal-unchanged}` | PASS (born) | body copied from `tracker/progress.go:205` |
| Pointer receiver, ≥3 fields, direct call | the above; `imported-goose/semantics/structs/struct-updates`; `multipkg/mini-raft-twin/elect-propose-commit` | PASS | |
| Field paths (nested read/write) | `imported-goose/semantics/structs/nested-struct-updates`; `structs/nested-field-write`; `structs/pointer-hop-field-write` | PASS | |
| Field / record copies independent | `methods/maybe-update-shape/widths-field-copy` (born); `noodler/structs/struct-copy-deep`; `structs/copy-value` | PASS | born row: a nested struct field copied, then mutated |
| Declared integer widths | `methods/maybe-update-shape/widths-field-copy` (born: `uint8`, `int32` fields wrap); `imported-goose/semantics/shortcircuiting/*` | PASS | |
| `uint64` wrap (`n+1` at 2^64−1, in `max`) | `methods/maybe-update-shape/uint64-wrap` (born); `imported-goose/semantics/operations/add64-equals`; `ints/wrap-width-boundaries` | PASS | |
| `max` on `uint64` | the born rows; `imported-goose/semantics/builtin/max-uint64` | PASS | |
| Stale/equal input unchanged, `false` | `methods/maybe-update-shape/{advance-then-stale,equal-unchanged}` (born) | PASS | was uncovered |
| Unrelated state framed | the born rows (untouched fields + a second instance); `multipkg/cross-type-method` | PASS | |
| Two successive calls, observed after each | the born rows; `methods/recv-implicit-addr-deref/non-nil-control`; `imported-goose/unittest/struct-pointers` | PASS | |

## CL2: byte-slice reads + `encoding/binary` + nil map (`readOnly.recvAck`)

| Subcondition | Case IDs | Status | Note |
|---|---|---|---|
| Customer shape (first row) | `binary/recv-ack-shape/*` (17, born) | PASS | body copied from `raft/read_only.go:65`, real `encoding/binary` |
| Nil context → no-op | `binary/recv-ack-shape/nil-ctx` | PASS (born) | was uncovered |
| Empty non-nil context → no-op | `binary/recv-ack-shape/empty-ctx` | PASS (born) | was uncovered |
| Exactly 8 bytes, little-endian | `binary/recv-ack-shape/{len8-existing,len8-missing-key}`; `binary/little-endian/{heartbeat-ctx-shape,roundtrip}`; `stdlib-source/binary-order/le-roundtrip-64` | PASS | born rows `depth=64` (w = 15) |
| > 8 bytes: first 8 read | `binary/recv-ack-shape/{len9-first-eight,len16-first-eight}` | PASS (born) | was uncovered |
| Lengths 1–7: EXPLICIT panic | `binary/recv-ack-shape/len{1..7}-panics`; `binary/little-endian/short-read` (3 only) | PASS | full matrix, gc's `[7] with length N` text compared |
| Missing key → zero | `binary/recv-ack-shape/len8-missing-key`; `examples/histogram/miss`; `quorum/committed-index/unacked` | PASS | |
| Nil map: read zero; write panics | `binary/recv-ack-shape/{nil-map-empty-ctx,nil-map-len8-panics}`; `maps/nil-value-comma-ok`; `maps/map-nil-assign` | PASS | born: the read in `max` succeeds, the store panics |
| Max update, both directions | `binary/recv-ack-shape/{len8-existing,keeps-larger}` | PASS (born) | was uncovered |
| Input bytes + unrelated entries preserved | every `recvAckLen` row (checksum delta, entry 9) | PASS (born) | was uncovered |
| Byte-to-word shifts by hand | `binary/recv-ack-shape/hand-decode` | PASS (born) | was uncovered |

## CL3: call/return/unwind (`Progress.SentEntries`)

| Subcondition | Case IDs | Status | Note |
|---|---|---|---|
| Customer shape (first row) | `panic-recover/sent-entries-shape/{normal-path,write-survives-recovered,write-survives-abort}` (born) | PASS | `Next` written, `Inflights.Add` panics on a full window |
| Write-call-panic: the field write survives | the born rows; `spec-examples-decl/recover-protect/panics`; `control-flow/switch-case-expression-panic` | PASS | receiver-field form was uncovered |
| Later update does not execute | born rows (`MsgAppFlowPaused` unchanged); `builtins/make-map-hint-eval/panic-map-never-created` | PASS | |
| Observation before failure | `panic-recover/sent-entries-shape/write-survives-abort` (born); `panic-recover/panic-text/output-prefix`; `panic-recover/panic-preprint/recovered-not-called` | PASS | output prefix is part of a panic observation |
| Return value observed, then failure | `panic-recover/sent-entries-shape/write-survives-abort` (born); `multi-assign/call-write-back/nil-field-store` | PASS | |
| Deferred cleanup under Go control | born abort row (two frames' deferred prints, unrecovered); `panic-recover/repanic-recovered-by-outer`; `noodler/defers/nested-recover-levels`; `panic-recover/panic-preprint/post-defer-state` | PASS | multi-frame unrecovered was uncovered |
| Go `error` returned and handled | `panic-recover/sent-entries-shape/error-not-panic` (born); `fmt/errorf/sentinel-classify`; `errors/new-sentinel/classify` | PASS | |
| `error` vs panic on one path | `panic-recover/sent-entries-shape/{error-not-panic,panic-not-error,value}` | PASS (born) | was uncovered |
| Refusal distinct from panic | `strings/trimspace-repeat/repeat-bound-refused` (FAIL by design, refused by name; `recover` cannot catch it) | FAIL (design) | apparatus-level: a refusal is a separate outcome type and never a PASS; no row can EXPECT a refusal (`docs/coverage-suite-structure.md`) |

## CL4: slices / ring buffers (`tracker.Inflights`)

| Subcondition | Case IDs | Status | Note |
|---|---|---|---|
| Customer shape (first row) | `slices/ring-buffer-shape/{wrap,stale-slots,clone-vs-alias}` (born) | PASS | `Inflights` bodies kept (`tracker/inflights.go`) |
| Header copies share backing | `slices/ring-buffer-shape/clone-vs-alias` (born); `slices/slice-header-by-value`; `noodler/structs/struct-copy-deep` | PASS | |
| `append` reuse vs replace | `noodler/slices/{append-shares-within-cap,append-reallocates-at-cap,header-copy-independence}`; `slices/gotcha-append-aliasing` | PASS | |
| Reslice aliases | `noodler/slices/nested-reslice-shares`; `arrays/array-slice-alias`; `slices/reslice-capacity` | PASS | |
| Overlapping `copy` | `slices/copy-overlap-backward`; `builtins/copy-edge/forward-overlap`; `slices/slice-copy` | PASS | |
| Nil vs empty | `slices/slice-nil-empty`; `noodler/slices/nil-vs-empty-append`; `noodler/bounds/nil-slice-slicing` | PASS | |
| Bounds failures | `noodler/bounds/{nested-index-panic,slice-high-past-cap,three-index-max-past-cap}`; `slices/full-slice-bounds` | PASS | gc's exact texts |
| Length/capacity | `slices/append-self`; `slices/append-spill-size-class` (membership: growth is latitude) | PASS | |
| Wrapping cursor, stale slots, growth | `slices/ring-buffer-shape/{wrap,stale-slots}` | PASS (born) | was uncovered |
| Access labels | `race/negative/slice-elem`, `race/free/slice-disjoint` (the only differential projection) | PASS | STATED LIMIT 3 |

## CL5: callbacks / Storage / timers

| Subcondition | Case IDs | Status | Note |
|---|---|---|---|
| Customer shape (first row) | `functions/callback-dispatch-shape/stored-dispatch` (born) | PASS | `r.step(r, m)` + `r.tick()`, reassigned by `becomeLeader` |
| Function-value dispatch identity | the above; `functions/composite-function-values/struct-reassign` | PASS | owner-argument form was uncovered |
| Interface dispatch identity | `functions/callback-dispatch-shape/iface-dispatch` (born); `imported-goose/semantics/interfaces-complex/double-pointer-interface` | PASS | one site, two callees: was uncovered |
| Callback mutates; effect boundary on failure | `functions/callback-dispatch-shape/{visitor-panics-mid,visitor-completes}` (born); `noodler/frontier2/callback-method-value` | PASS | panic at element k: was uncovered |
| Storage-like `(value, error)` identity | `functions/callback-dispatch-shape/storage-{compacted,value,unavailable}` (born); `errors/new-sentinel/identity` | PASS | the in-program stand-in only (STATED LIMIT 1) |
| `globalRand.Intn` environment contract | `functions/callback-dispatch-shape/global-rand-locked` (born, membership {5..9}); `builtins/rand-intn/{jitter-shape,zero-panics}` | PASS | contract: some v ∈ [0, n), panic at n ≤ 0 (unit 5b) |
| External-call contracts or named refusals | — | — | STATED LIMITS 1–2 |

## Uncovered subconditions and their disposition

Added rows (all born PASS; 39 total, `scripts/diff-one` 39/39, then the full gate `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff`: RESULT PASS, 3860 = 3623 / 237, baseline diff full, no regression, certificate provenance ok, 1145 s): CL1 stale/equal
guard, `n+1` wrap in `max`, field copy with declared widths; CL2 nil/empty no-op, > 8 bytes,
the lengths 1–7 matrix, max both ways, preservation, nil-map store after a successful read,
hand shifts; CL3 receiver write surviving a panicking callee, multi-frame deferred prints on
the unrecovered path, return-then-fail, `error` vs panic on one path; CL4 the ring buffer
(wrap, stale slots, growth, Clone vs header copy); CL5 owner-argument stored dispatch, one
interface site with two callees, a visitor panicking mid-iteration, Storage-like replies,
the locked `globalRand` wrapper (gc: 20 draws, plain/-race alternating, all in {5..9}).

STATED LIMITS of the offer (not corpus gaps to close in this window):

1. **Storage is a program, not an external contract.** GoLean runs the actual Go bodies; it
   has no contract for an asynchronous or external Storage. raft's `MemoryStorage` is ordinary
   Go and runs as such (`tools/raftsubject/twin-lib.go`). No postcondition stands in for a body.
2. **Timers / wall clock are refused by name.** `time.Now`, `time.NewTimer` (and the rest of
   package `time`, outside the FR-22 initializer allowlist) export as a per-function refusal
   `package-selector call time.<F> (package "time" surface not modeled)`; likewise `rand.New`
   → `package-selector call rand.New (package "math/rand" surface not modeled)` (probed
   2026-10-03 on this branch's frontend; no corpus row expects a refusal, by apparatus
   design). raft's RawNode level reaches no timer (the caller drives `Tick`). Pinning these
   texts as red rows would need a ledger row; not taken here ([AGENT]).
3. **Access labels are not a differential observable.** gc exposes no memory-access trace;
   the labels live in the relation (`StepLabel.trace`), and their only differential
   projection is the race lane's verdict.
4. **Refusal ≠ panic** is enforced by the apparatus (a refusal is never a PASS; `recover`
   cannot catch one), not by a row that expects a refusal.
5. **LATER per charter §4**: loops/`range`/map iteration as proof subjects; goroutines /
   `select`; the protobuf route and subject deltas U-1..U-3 (`docs/2026-09-30_note-from-raft-proofs.md`)
   are tracked under their own rulings, not here.
