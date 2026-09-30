# Protobuf route A — feasibility and design (2026-09-30)

[AGENT] worker, lane `records/raft-deltas-0930` (worktree `.claude/worktrees/raft-deltas`, off `main` @ `883ebc36`). The question
the [USER] made the condition (Mike, 2026-09-30, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Yes, I also prefer
A, as long as it could be made faithful»): can a Go codec in `raftsubject/`, lowered by our frontend, be FAITHFUL to protobuf-go
wherever raft can observe it? Inputs: protobuf-go **v1.36.11** — the version raft pins (`deps/raft/go.mod`), read from the Go module
cache (`/home/dev/go/pkg/mod/google.golang.org/protobuf@v1.36.11`, no network); upstream raft @ `56e32004`; the raft-proofs note
(`docs/2026-09-30_note-from-raft-proofs.md`) and its frozen corpus `fixtures/i6/malformed-conf-bytes.json` (26 entries, read-only
at `docs/golean-response-0930` @ `f3d857f`). Evidence: `docs/evidence/2026-09-30_protobuf-route-a/` (the two scratch programs,
the run log, the commands) — scratch runs of this day, not gate inputs.

## 0. Verdict

**FAITHFUL-FEASIBLE**, under conditions C1–C5 (§5). A plain, reflection-free, generated-style Go codec reproduces every behaviour
raft can observe of protobuf-go over the nine schemas — verdicts, the one error value and its text, unknown-field retention,
re-encoding, `Size`, `Clone`, `Equal`, group skipping — exactly; the per-binary prefix spacing is a latitude modeled as a choice.
Route B is not needed. Two residues, neither a subject delta (§5).

## 1. What protobuf-go does where raft can observe it (from source, v1.36.11)

- **The error value.** Every decode error of the generated fast path is ONE value: `internal/impl/decode.go` `errDecode =
  errors.New("cannot parse invalid wire-format data")`, returned for a bad tag varint, field number `0` or `> 2^29−1`, a stray
  end-group tag (`num != groupTag`), a known field's malformed value (`consumeUint64`/`consumeBool`/`consumeBytes`/
  `consumeMessageInfo`: `n < 0 → errDecode`), and an unknown field whose `protowire.ConsumeFieldValue` is negative — truncation,
  varint overflow, reserved wire types 6/7, a mismatched or truncated group, group depth over `DefaultRecursionLimit` (10000): every
  negative code collapses to `errDecode` (`unmarshalPointerEager`). `errRecursionDepth` needs > 10000 nested MESSAGES; raft nests
  ≤ 4 (`Message → Snapshot → SnapshotMetadata → ConfState`), so it is unreachable. `raft.proto` is proto2 with no `required` and
  no `string` field: no `checkInitialized` error, no UTF-8 error. `internal/errors.New` builds a `*prefixError{s}`; `Error()` is
  `prefix + s`; `Unwrap()` is the sentinel `errors.Error` («protobuf error»), so `errors.Is(err, proto.Error)` holds.
- **The spacing (confirmed mechanism).** `internal/errors/errors.go`: `prefix` is computed ONCE at package init — `"proto: "`
  with U+00A0 if `detrand.Bool()`, else with U+0020 — «to discourage users from performing error string comparisons».
  `internal/detrand/rand.go`: `Bool() = randSeed%2 == 1`, `randSeed = binaryHash()` = FNV-64 over the executable's size plus eight
  64-byte samples of `os.Executable()` (0 on any failure, i.e. U+0020). Stable within a binary, unstable across builds — a
  deliberate per-BINARY latitude, not a per-run one. (The same bit spaces prototext output, `internal/encoding/text`.)
- **Unknown fields.** A field number with no descriptor, OR a known field at the wrong wire type (`errUnknown` from its consumer),
  is retained as the CANONICAL re-encoded tag (`protowire.AppendTag`) followed by the RAW value bytes, in arrival order
  (`mi.mutableUnknownBytes`). `Marshal` emits the unknown bytes AFTER all known fields (field-number order); `Size` adds
  `len(unknown)`; `Merge`/`Clone` appends src's unknown bytes to dst (when non-empty); `Equal` compares them — byte-equal, else a
  per-field-number multiset comparison (order-insensitive, `impl.equalUnknown`). `Unmarshal` = `Reset` + merge; nil and empty
  input decode to an empty message without error.
- **Groups.** `protowire.consumeFieldValueD`: a start-group is skipped by consuming tag/value pairs until an end-group whose number
  matches (`errCodeEndGroup` otherwise), recursively with `depth−1`; the whole group including its end tag becomes ONE unknown field.
  A start-group under a KNOWN field's number is `errUnknown` from the typed consumer and is skipped the same way.
- **Where raft observes it** (subject line numbers; upstream in parentheses). `proto.Unmarshal` at `raft.go:1334/1340`
  (`1315/1321`) — `panic(err)`: the error VALUE is the panic payload and its text the abort line; `util.go:225/232` — `err.Error()`
  into `DescribeEntry`'s string. The decoded ConfChange is read through `cc.AsV2().Changes` and `DescribeConfChange` (known fields).
  `proto.Size` (`util.go:277/290/292`), `proto.Clone` (`raft.go:836`, `log_unstable.go`, `storage.go`) and `proto.Marshal`
  (`bootstrap.go:56`; `MarshalConfChange` on `ProposeConfChange` and the auto-leave path `raft.go:767`) all run on CONSTRUCTED
  messages, never on decoded ones. **[AGENT] reading, offered as a correction to the note's U-3 line:** through RawNode, U-1 (the
  abort value) and U-2 (accept vs abort of a proposal carrying an unknown group) are directly observable; U-3's retention/
  re-encode/`Size` clauses are observable to a raftpb CLIENT that decodes entry data itself, and through prototext renderings
  (`String()`, D-1's fail-closed residue) — no RawNode path re-marshals, sizes, clones or compares a decoded message. Route A
  restores all three regardless of which observer sees them.

## 2. Can plain Go reproduce it exactly? Yes — measured

A scratch prototype (`.tmp/proto-a/main.go`, stdlib only, no reflection, ~560 lines): `ConfChange`/`ConfChangeSingle`/
`ConfChangeV2` with an `unknownFields []byte` each; the retention branch (canonical tag + raw bytes); a recursive, depth-limited
group skipper; `prefixError{s}` with `Error()`/`Unwrap()` to a package sentinel; the prefix picked ONCE at package init by the
D-11 map-range idiom over the two spellings. The REFERENCE leg (`.tmp/protoref`): real protobuf-go v1.36.11 over upstream
`raftpb`, a throwaway module built from the cache (`GOPROXY=off GOSUMDB=off GOFLAGS=-mod=mod`). Both over the 26-entry corpus:
- verdicts identical on 26/26 (16 errors, 10 decodes — incl. `v1-type-as-bytes`/`v2-changes-as-varint` kept as unknowns,
  `v1-unknown-field-number-max` accepted, `v2-field-number-too-large`/`v1-field-number-zero`/`v1-end-group-unmatched`/
  `v2-group-end-mismatch`/`v2-truncated-group` refused);
- `Size` and re-`Marshal` bytes identical on 10/10 — e.g. `v2-unknown-all-wire-types` → `120608011002180148015101…` (known
  field 2 first, then the five unknowns incl. the skipped group `5a…5d`, in arrival order) on both;
- `errors.Is(err, Error)` true on both; text identical up to the prefix byte: the reference binary realized U+0020 (44 bytes), the
  prototype's run realized U+00A0 (45) — both members exhibited; type `*errors.prefixError` vs `*main.prefixError` (§5, residue).
- **The spacing is LATITUDE; model it as a CHOICE, not a build parameter.** The spelling is a function of the binary, not of the
  program, so the weakest machine admits both; it is picked once per process (as `detrand` is) at package init through the
  map-range idiom — `ChoiceSite.mapIter`, NO core change — gc's binary being one member. The differential then compares by
  MEMBERSHIP over the two spellings, recording the bit the reference binary realized (raft-proofs records it as
  `protoErrorNBSP`). A build parameter would bake one member in and make the subject disagree with a real binary half the time.

## 3. What the frontend and GoLean support today (measured on the prototype)

`scripts/lower-diagnose .tmp/proto-a`: EXPORT OK, 30/30 declarations demand nothing refused. On the machine (`golean
native-json-run`): `routeAProbe` → `0` (all 26 verdicts and sizes agree with the reference), `routeAPrefixLen` → `8` (the slot-0
canonical member, U+00A0). SUPPORTED: byte slices, `append`/`copy`/`make`, shifts, width conversions, pointer-to-scalar presence,
slices of message pointers, self-recursion with a depth counter, a package-level `var` initialized through a map literal + `range`
(the choice site), `errors.New` (source-through), a user error type with `Error()`/`Unwrap()`, U+00A0 inside a string literal.
REFUSED: `errors.Is` (FR-14, `internal/reflectlite` — raft never calls it on this error); the ABORT LINE of `panic(err)` for ANY
error-typed payload — `unsupported: panic abort rendering for payload … (dynamic type *main.prefixError)` — BUG-004 item 4 (the
machine cannot call `Error()` at abort time; a category-(c) pin, [USER]-ratified 2026-08-20). Recovering the payload and calling
`Error()` in-language is fully supported (the R-1 forced-half pattern, `panic-recover/panic-defined-payload-methods/*-forced-half`).

## 4. The differential

- **D1 subject vs protobuf-go, both under `go run`** — `tools/raftsubject/difftest.py`. Its §7 (the W4.1 «OWED with command»
  obligation) RUNS OFFLINE now: `TMPDIR=$PWD/.tmp GOPROXY=off GOSUMDB=off GOFLAGS=-mod=mod python3 tools/raftsubject/difftest.py`
  → `PASS … 72 values: bytes, Size, and both cross-unmarshals across all 9 message types` (this day). It probes WELL-FORMED shapes,
  so it is blind to U-1–U-3. Route A adds **§8**: the 26-entry corpus (copied with provenance, frozen) plus a GENERATED adversarial
  battery over all nine types as top-level subjects — unknown fields of every wire type at every position, groups nested 0–3 and
  malformed (mismatched/truncated/stray end), known fields at wrong wire types, over-long tags, 10-byte varints, nil/empty — and,
  per input: verdict equality; `errors.Is` equality; error text equal after normalizing the ONE prefix byte sequence (the reference
  bit recorded; the subject's spelling ∈ the two); `Size` and `Marshal` byte equality; `Clone` + `Equal` agreement. **Exact = all
  of these; a NOTE-class divergence does not exist for §8.** Red-first: run against today's codec it fails 16 + 10 entries.
- **D2 machine vs `go run` over the subject codec** — `codeccheck.py` gains the same corpus as verdict ids on both legs (the prefix
  pick shows as a membership over the two lengths, or as the canonical member under a default tape).
- **D3 through RawNode** — a twin schedule proposing a malformed ConfChange: the `go run` leg panics with the subject's text; the
  machine leg refuses the abort line (BUG-004 item 4) — RED until that item lands, a machine limit, not the codec's. The witness that
  can pass today: a recovering twin-driver variant (`recover()` around `Step`, print `err.Error()`), a MEMBERSHIP row over the two
  spellings on both legs (`runprobe.py --main …`, the `mini-raft-twin/choice-order` precedent).
- **Not a corpus row.** Fixtures run `GO111MODULE=off` (stdlib only), so protobuf-go cannot be the oracle inside `Corpus/`; D1 is
  the subject-vs-upstream instrument, D2/D3 the machine-vs-gc ones. All three are instruments/rows of the subject lane, not gates.

## 5. Conditions, residues, and their §4

- **C1 (scope).** Faithful = raft's observable surface through RawNode AND the raftpb API a client uses (§1): `Unmarshal` verdict +
  error value, retention/re-encode/`Size`/`Clone`/`Equal` over unknowns, group skipping, `Marshal` of constructed messages.
  Prototext (`String()`), `%+v`/`%+#v` struct dumps (D-3) stay OUT of route A — D-1's rendering residue is the post-window `%+#v`
  lane (window plan §4) or, if it must stay, their §4 premise. Route A leaves NO protobuf delta on the codec's surface.
- **C2 (the bit).** The prefix spelling is a `mapIter` choice made once at package init; differential by membership; the reference
  bit recorded per run. The subject's pick is per PROCESS, protobuf-go's per BINARY — indistinguishable within one run.
- **C3 (the machine's abort line).** `panic(err)` renders as BUG-004 item 4's refusal on the machine until that item lands (core
  work, not this lane's); the twin witnesses U-1 through the recovering driver meanwhile. A stated limit of the MACHINE's
  observation — not a premise about the callee — so it does not enter their §2.4 form.
- **C4 (type identity — residue).** The value's dynamic type is a subject-local `prefixError`, not protobuf-go's internal
  `*errors.prefixError`: distinguishable only by `%T`/reflection or an assertion to an unexported foreign type — impossible through
  RawNode and outside a raftpb client's reach. Recorded, not a premise. The sentinel is a subject-local `proto.Error` var.
- **C5 (generation, not hand-writing).** Everything is emitted by `derive.py`'s `gen_codec` from the parsed field lists (JC-11); the
  D-1 strip keeps `unknownFields []byte` where `protoimpl.UnknownFields` was; `--check` stays the drift guard; the twin wire is
  RE-PINNED under `--slow` with the written reason. Acceptance = D1 §8 exact + D2 green + D3's row landed.

## 6. Plan and estimate — a post-window lane (no core, no trust-surface change)

`subject/protobuf-route-a`, after the re-pin offer (7b): it moves the pinned twin wire, which must not happen inside the window
for a subject change. S1 generator: the strip keeps `unknownFields`; retention branch; group skipper (depth 10000); `prefixError`
+ sentinel + init pick in `proto/proto.go`; `Clone`/`Equal` over unknowns; dispatch unchanged; `MarshalConfChange` overlay
unchanged — 1 session (Opus). S2 `difftest.py` §8 + the corpus import + `codeccheck.py` rows — 1 session (Opus). S3 the recovering
twin row, the `--slow` re-pin with reason, U-1/U-2/U-3 RETIRED in the ledger, `raftsubject/README.md` — 1 session; the audit ask.
Total 2–3 sessions. The go-ahead is a [USER] decision at dispatch (the 2026-09-30 preference is conditional; this note discharges
the condition). If the logic team cannot prove against a lowered codec (§7), route B returns as a question, not a default.

## 7. Draft question to the logic team (for the [USER] to relay)

> GoLean's user prefers protobuf route A — a faithful Go codec generated inside `raftsubject/`, lowered by the frontend like the
> rest of raft, validated differentially against protobuf-go v1.36.11 — and our feasibility check finds it exactly faithful where
> raft observes it (`docs/2026-09-30_protobuf-route-a.md`). You wrote that route B (native definitions in the core) is likely
> cheaper for your proofs. Concretely: is proving raft's ConfChange paths against a LOWERED Go `Unmarshal` (a loop over a byte
> slice with a few hundred GoCore steps, one `mapIter` pick at package init for the error prefix, `panic(err)` with an error-typed
> payload) workable for you — e.g. by treating the codec's functions as calls with contracts you discharge once, or by symbolic
> execution of the lowered body — and what would you need from us for that (a pinned equation set for the codec's functions, a
> named `FuncId` list, a purity statement, the init-time pick as a labelled choice)? If it is not workable, please say what
> specifically makes native definitions cheaper, so the [USER] can weigh A against B on that.
