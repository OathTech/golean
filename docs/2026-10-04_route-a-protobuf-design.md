# Protobuf route A — the faithful codec: DESIGN (2026-10-04) — a named design gate, HARD STOP

[AGENT] design worker, lane `design/route-a-protobuf-1004` (worktree `.claude/worktrees/route-a-design`, off `main` @ `450412a7`).
Authority: [USER] Mike 2026-10-04, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Great, launch it» — a design
note for route A, a NAMED DESIGN GATE: nothing below is built before [USER] review. Standing rulings: [USER] 2026-09-30 «Yes, I
also prefer A, as long as it could be made faithful» (relayed; `docs/2026-08-31_qrow-rulings.md`, subject-delta note item 3,
route-A dispositions 1–4). This note BUILDS ON the feasibility study `docs/2026-09-30_protobuf-route-a.md` (verdict
FAITHFUL-FEASIBLE, conditions C1–C5 — not redone here) and carries the logic team's requirements
(`docs/2026-09-30_note-from-logic-team-route-a.md` §5, disposition 2's required content) and the raft-proofs findings U-1–U-3
(`docs/2026-09-30_note-from-raft-proofs.md`). Pins: protobuf-go **v1.36.11** (`deps/raft/go.mod`; read from the module cache
`/home/dev/go/pkg/mod/google.golang.org/protobuf@v1.36.11`, no network), raft `56e32004`, go1.26.5. Every decision in §4 is
[AGENT], PENDING [USER] ratification. Evidence (small, this day's probes): `docs/evidence/2026-10-04_route-a-design/`.

## 0. Recommendation in two lines

Build route A as **A1** (§3): a GENERATED, reflection-free Go codec inside `raftsubject/`, decomposed function-for-function after
protobuf-go's own `protowire`/`impl` entry points so every generated function names its upstream twin by file:line, dispatched
through an interface (the subject `proto` package no longer imports `raftpb`, so the two hand-written overlays retire to upstream
text), with `unknownFields []byte` retained, ONE `prefixError` value, and the per-binary spelling as one labelled choice at package
init. No core change, no trusted-surface change, no register change, no wire-schema change; 3–3.5 sessions.

## 1. Scope — exactly what raft reaches (measured)

- **Generated code shape.** Upstream `raftpb/raft.pb.go` is `protoc-gen-go v1.36.11` / `protoc v3.20.3` output — the golang
  protobuf APIv2 «open.v1» API, NOT gogo (raft v3's `go.mod` requires only `google.golang.org/protobuf v1.36.11`). `raft.proto` is
  **proto2**: nine messages, four enums, field numbers 1–14, kinds `optional uint64|bool|enum|bytes|message`, `repeated uint64`
  (unpacked; `ConfState` ×4), `repeated message` (`Message.entries`, `Message.responses` — **self-recursive**, `ConfChangeV2.changes`);
  no `required`, no `string`, no map, no oneof, no group, no extension. Each struct carries `state protoimpl.MessageState`,
  `unknownFields protoimpl.UnknownFields` (= `[]byte`, `internal/impl/message.go:114`), `sizeCache`, and `ProtoReflect()`; the
  file-descriptor init registers the types (reflection). The D-1 strip (`derive.py` `parse_struct`, `PROTOIMPL_FIELD_TYPES`) removes
  all three fields and drops `reflect`/`sync`/`unsafe`/`protoreflect`/`protoimpl`.
- **Call sites in the subject** (upstream text, import paths rewritten). `proto.Marshal`: `raft/bootstrap.go:56` (`&pb.ConfChange{…}`),
  `raftpb/confchange.go` `MarshalConfChange` (ConfChange / ConfChangeV2; overlay today) ← `raft/node_decls.go:115`
  (`ProposeConfChange`) and `raft/raft.go:760` (auto-leave, `confChangeToMsg(nil)` → nil data). `proto.Unmarshal`: `raft/raft.go:1326/1332`
  — `panic(err)`, the VALUE is the payload and its text the abort line; `raft/util.go:225/232` — `err.Error()` into `DescribeEntry`.
  `proto.Size`: `raft/util.go:277/290/292` (Entry). `proto.Clone`: `raft/storage.go:213/234/259/262`, `raft/log_unstable.go:114/187`,
  `raft/log.go:295` (Snapshot, ConfState), `raft/raft.go:829` (Entry). `proto.Equal`: through `(*ConfState).Equivalent`
  (`raft/util.go:321`). All decoded messages are ConfChange/ConfChangeV2; Size/Clone/Marshal/Equal run on constructed values. The
  go-run reference harness `raftharness/` links the REAL runtime (`google.golang.org/protobuf/proto`; `harness.go:232/323/329`).
- **`scripts/lower-diagnose` over the twin assembly** (`raftsubject/{quorum,raftpb,tracker,proto,confchange,raft}` + `twin-lib.go`
  + `twin-chdriver*.go`, i.e. `check-frontend-pins`' program): EXPORT OK; static 690/696 declarations demand nothing refused;
  `raftpb` 250/250, `proto` 6/6, `confchange` 24/24 — NO protobuf-side refusal. Every refused key: `os.Exit` ×2
  (`DefaultLogger.Fatal/Fatalf`, FR-14), `log.Logger.Panic`/`Panicf` (`DefaultLogger.Panic/Panicf`, FR-14), `math/rand.Intn`
  (`lockedRand.Intn` — a STATIC-pass staleness: the dynamic pass lowers it through the 5b `rand-intn` primitive and the twin wire
  pin is green; `tools/lowerdiag`'s tables predate the primitive — a one-line follow-up outside this lane); may-refuse: the
  `!with_tla` build constraint (`state_trace_nop.go`). The 31 wire quarantines are all stdlib (`bytealg` ×2, `bytes.Buffer` ×7 on
  `io.EOF`, `log.Logger` ×22). Over the 2026-09-30 prototype: 35/36, the one refusal `errors.Is` (FR-14, `reflectlite.TypeOf`).
  Over UPSTREAM `raftpb` verbatim: does not type-check — `google.golang.org/protobuf/{proto,reflect/protoreflect,runtime/protoimpl}`
  are unresolvable at the frontend's module boundary (no `foreign-module` path exists), so option C (§3) is refused before any
  declaration is judged. Heads of the three reports: the evidence dir.

## 2. What protobuf-go does where raft (or a raftpb client) can observe it — v1.36.11, by file:line

- **Entry points.** `proto.Unmarshal` (`proto/decode.go:61-64`) = `UnmarshalOptions{RecursionLimit: 10000}.unmarshal`: `Reset` unless
  `Merge` (`:93-96`; `proto/reset.go:16-22` calls the generated `Reset()`), then the generated fast path `methods.Unmarshal`
  (`:99-120`), then `checkInitialized` — no `required` field, so never an error (`:131-135`). `proto.Marshal` (`proto/encode.go:105-116`):
  a nil interface → `nil, nil`; an EMPTY valid message → the non-nil empty buffer; a TYPED-NIL pointer → `nil` (`emptyBytesForMessage`,
  `:141-146`: invalid message → nil). `proto.Size` (`proto/size.go:19-35`): nil → 0; typed nil → 0 (`impl/encode.go` `sizePointer`
  on a nil pointer). `proto.Clone` (`proto/merge.go:41-60`): nil → nil; typed nil → `Type().Zero().Interface()` = the typed nil;
  else `New` + merge. `proto.Equal` (`proto/equal.go:42-66`): `x == nil || y == nil → x == nil && y == nil`; validity must agree; then
  the generated `Equal` (`impl/equal.go:22-131`), which ends in `equalUnknown` (`:193-224`: equal length AND (byte-equal OR equal
  per-field-number raw-bytes multisets)).
- **The decode loop** (`impl/decode.go:123-241`, `unmarshalPointerEager`): depth counter `opts.depth--` per message entry
  (`:103-106`, `errRecursionDepth` = «exceeded maximum recursion depth», `:20`); tag = 1-byte / 2-byte fast path else
  `protowire.ConsumeVarint` (`:136-148`, `n < 0 → errDecode`); field number `< 1` or `> 2^29−1` → `errDecode` (`:149-155`;
  `protowire/wire.go:24-27`); an end-group tag whose number ≠ the enclosing group's → `errDecode` (`:158-164`); a known field's
  consumer returns `errUnknown` on a WRONG wire type and `errDecode` on a malformed value (`codec_gen.go:2762-2790` `consumeUint64Ptr`,
  `:108` `consumeBoolPtr`, `:5410-5421` `consumeBytes` — an empty value becomes a NON-nil empty slice, `:687` `consumeInt32Ptr`
  which IS the enum coder: `codec_unsafe.go:12` `coderEnumPtr = coderInt32Ptr`, `codec_tables.go:288-290` — so **Go treats the
  proto2 enums as OPEN**: an unlisted enum value is stored, never diverted to unknowns; `codec_gen.go:2816` `consumeUint64Slice`
  accepts packed AND unpacked; `codec_field.go:175-193` `consumeMessageInfo` allocates-if-nil and MERGES, `:438`
  `consumeMessageSliceInfo` appends a fresh element); `errUnknown` → `protowire.ConsumeFieldValue` (`:218-224`; `n < 0 → errDecode`)
  and, unless `DiscardUnknown`, RETENTION of the canonical tag (`AppendTag`) + the raw value bytes in arrival order (`:225-229`);
  a group left open at end of input → `errDecode` (`:233-235`). `consumeFieldValueD` (`wire.go:116-160`): wire types 0/1/2/5 by
  size; 3 = skip tag/value pairs recursively (`depth−1`, limit 10000, `errCodeRecursionDepth`) until the matching end tag
  (`errCodeEndGroup` on a mismatch); 4 at top → `errCodeEndGroup`; 6/7 → `errCodeReserved`. INSIDE a skipped group the tag is read by
  `ConsumeTag` (`:168-178`), which refuses only `num < 1` — `DecodeTag` (`:525-531`) maps `x>>3 > MaxInt32` to −1 — so a field
  number in [2^29, 2^31) is ACCEPTED inside a group and REFUSED at top level: an asymmetry the generated codec must reproduce.
  `ConsumeVarint` (`:267-367`): ≤ 10 bytes, the 10th < 2 (`errCodeOverflow`), truncation `errCodeTruncated`. Every negative code
  collapses to the ONE value `errDecode` (`impl/decode.go:19`, «cannot parse invalid wire-format data»).
- **The error value and its spelling.** `internal/errors/errors.go:20-22` `New` → `&prefixError{s}`; `Error()` = `prefix + s`
  (`:36-38`); `Unwrap()` = the sentinel `Error` («protobuf error», `:16`), so `errors.Is(err, proto.Error)` holds. `prefix` is
  computed ONCE at package init (`:26-34`): `"proto: "` with U+00A0 if `detrand.Bool()`, else U+0020. `internal/detrand/rand.go:25-27`
  `Bool() = randSeed%2 == 1`; `randSeed = binaryHash()` (`:38-69`) = FNV-64 over the executable's size + eight 64-byte samples, 0 on
  any failure (→ U+0020). A per-BINARY latitude: the weakest machine admits both spellings (C2).
- **Encoding.** `marshalAppendPointer` walks `orderedCoderFields` sorted by field NUMBER (`impl/codec_message.go:158-160`), proto2
  presence (set-but-zero scalars and empty-but-present bytes emitted), repeated varints unpacked, and appends the unknown bytes LAST
  (`impl/encode.go:220-224`); `Size` adds `len(unknown)` (`:113-116`); Merge/Clone appends src's unknown bytes when non-empty
  (`impl/merge.go:106-111`). Marshal cannot fail on these schemas (no required, no UTF-8 check): `err` is always nil.

## 3. The options

| | A1 (RECOMMENDED) | A0 (the feasibility prototype's shape) | B — library-origin primitive codec | C — source-through upstream + modeled runtime |
|---|---|---|---|---|
| what | `derive.py` generates a plain-Go codec from the parsed field lists, mirroring protobuf-go's decomposition: `consumeVarint`/`consumeTag`/`consumeBytes`/`consumeFieldValue(depth)`/`appendTag`/`appendVarint` twins + per-type `MarshalAppend`/`SizeMessage`/`UnmarshalMessage(depth)`/`ProtoClone`/`ProtoEqual`/`ResetMessage`/`IsNilMessage`; `proto` dispatches via an interface (does NOT import `raftpb`); `unknownFields []byte` retained; `prefixError` + sentinel; the init spelling pick | one monolithic `UnmarshalMessage` per type, type-switch dispatch in `proto` (imports `raftpb`), both overlays stay | a machine op family (`Stmt`/`Expr` constructors, wire node, `stepFn` arms, equations) implementing Marshal/Unmarshal/Size/Clone/Equal over GoValue structs in Lean | lower upstream `raft.pb.go` + `protoimpl`/`internal/impl` as source |
| faithfulness argument | per-function twin table (file:line, §2) checked by `difftest.py` §8 EXACT (verdict, sentinel, text modulo the prefix byte, Size, bytes, Clone/Equal) over the 26-entry corpus + a generated adversarial battery; structure matches, so the asymmetries of §2 fall out instead of being special-cased | same differential; structure differs, so each asymmetry is a special case to remember | a Lean definition proved nothing about protobuf-go; differential only through the machine | upstream text itself — but it never lowers |
| refused by name | `errors.Is` on the machine (FR-14/G6 — raft never calls it; the `Unwrap` chain serves go-run clients); prototext `String()`, `Descriptor`, `UnmarshalJSON` stay fail-closed stubs (C1); `%+#v` dumps (D-3, its own lane) | the same + the typed-nil `Marshal` wrong answer (`nonNil`, §5 row) unless fixed | a non-nine message type refuses by name; the spelling bit needs its own site | refused at the module boundary (§1, measured) and by the closure: `pointer_unsafe.go`, `codec_unsafe.go`, `message_reflect*.go`, atomic `sizeCache`, `sync` — reflect/unsafe, out of language (G6) |
| cost | 3–3.5 sessions (Opus): S1 generator + dispatch + overlays 1.5, S2 differential instruments + corpus rows 1, S3 twin rows + `--slow` re-pin + ledger/README + audit ask 0.5–1 | 2–3 sessions (the 2026-09-30 estimate) | 4–8 sessions; Lean codec + totality + equations + BridgeSet rows + decoder + frontend binding | unbounded (a reflect subset + a module-source register class) |
| trusted surface / register | none / none (subject text; lowered like the rest of raft; exercised by the twin pin) | none / none | WIDENED (the codec enters the interpreter) / primitive cap **3 → 4** — a [USER] re-ratification | a NEW register class (module source-through) — [USER] |
| wire schema / logic side | no node, no constructor, no statement change; they see a `FuncId` list + footprint TSV and (if they pin it) new twin-wire bytes | same | new wire node, `Stmt`/`Expr` constructors, `stepFn` arms, new equations — a statement change in their re-pin | n/a |

B is excluded by the standing ruling unless A proves impossible (it has not); C is measured impossible under the current frontend.
A0 vs A1: A1 costs ~1 session more and buys (i) verbatim `raftpb/confchange.go` and a two-line `confstate.go` residue, (ii) a
per-function proof target the logic team can contract one twin at a time, (iii) the typed-nil behaviours right by construction.
**Probe evidence for A1's two new mechanisms** (evidence dir `dispatch-probe/`): a three-package program — `proto` dispatching via
`m.(methods)` to a `pb` type that imports `proto`, the init pick as a package-level `var prefix = pickPrefix()` over a two-key map
range, `panic(err)` with the `*prefixError` payload — LOWERS (wire 129,578 B) and the machine agrees with `go run` on all three
probes: dispatch/retention/re-encode/Size/Clone/Equal checks 1–4 pass on both; `len(ErrDecode.Error())` = 45 on both (the
U+00A0 member — slot 0 on the machine, this process's draw under gc); the abort renders `status: panic`, message
`proto: cannot parse invalid wire-format data` — BUG-004 item 4 (unit 6b) has landed, so C3 is DISCHARGED and the twin row goes
through RawNode. The probe's check 5 deliberately exposes that a typed-nil `Marshal` answers `[]byte{}` through an `AppendMessage`
-style dispatch (today's `proto.go` `nonNil` does the same) where protobuf-go answers `nil` — hence `IsNilMessage` in D2.

## 4. Decisions (all [AGENT]; PENDING [USER] ratification; none moves a register cap or the trusted surface)

- **D1** Shape A1. The generator emits ONE helper file (`raftpb/plain_wire.go`: the `protowire` twins, each with its upstream
  file:line in the doc comment) and the per-type codec (`plain_codec.go`) from the parsed field lists; `--check` stays the drift guard.
- **D2** Dispatch through an interface. `proto.Message` stays `interface{ ProtoMessage() }` (upstream's parameter type); `proto`
  asserts to an unexported interface listing the generated EXPORTED methods `MarshalAppend([]byte) []byte`, `SizeMessage() int`,
  `UnmarshalMessage([]byte, int) error`, `ResetMessage()`, `ProtoClone() proto.Message`, `ProtoEqual(proto.Message) bool`,
  `IsNilMessage() bool` (`raftpb` imports `proto`, as upstream imports `protoimpl`). Typed-nil behaviours per §2: Marshal → `nil, nil`,
  Size → 0, Clone → the typed nil, Equal → protobuf-go's validity rule; a type outside the nine still panics by name in the assertion's
  `!ok` arm. Cross-package interface assertion is modeled (rows `interfaces/assert-imported-interface/*` PASS; the probe).
- **D3** The strip KEEPS `unknownFields []byte` under upstream's field name (`protoimpl.UnknownFields` is `[]byte`); `state` and
  `sizeCache` stay stripped (D-1 narrowed, not retired). Consequence stated for the D-3 lane: `%+#v` can never be exact — upstream's
  dump prints `state`'s `*impl.MessageInfo` pointer — so D-3 is a permanent narrowed premise, not a route-A residue (Q4).
- **D4** Two error values, both `*prefixError` with `Unwrap() = proto.Error`: `errDecode` for every malformation and
  `errRecursionDepth` — REACHABLE for a raftpb client through `Message.responses` (self-recursive) at > 10000 nested messages, so
  `UnmarshalMessage` carries protobuf-go's depth counter (10000, decremented per message entry) and `consumeFieldValue` its own
  (groups). The feasibility note's «unreachable» holds for raft's own paths only; C1 puts the client API in scope.
- **D5** The spelling pick is ONE fixed shape, a package-level `var prefix = pickPrefix()`. Recommended mechanism: `rand.Intn(2)` on
  the EXISTING `ChoiceSite.intn` (index 0 = U+0020, detrand's failure default; 1 = U+00A0) — one data pick with pinned equations
  (BridgeSet rows 133–135, the 5b derived lemma), uniform under gc. Alternative: the prototype's two-key map range (`mapIter`,
  slot 0 = first key); the logic team accepted either shape («the mapIter idiom is fine, but please fix its exact shape»). [USER]
  picks (Q1). Either way the differential compares by MEMBERSHIP over {44, 45} / the two texts, recording the reference bit.
- **D6** Generated-code grammar (their (c)): indexed `for` loops only (no `range`), `break`/`continue` only, recursion bounded by
  the depth counter, no closures, no `goto`, no `fmt`, no reflection; the tagless `switch` field dispatch is retained (Q5).
- **D7** Overlays. `raftpb/confchange.go` → upstream VERBATIM (its `google.golang.org/protobuf/proto` import rewritten to `proto` by
  the existing `SUBJECT_PACKAGES` rewrite — JC-13 / the W2 overlay delta RETIRED). `raftpb/confstate.go` → upstream text plus an
  exact-text SUBJECT PATCH on the two `fmt.Errorf` lines (D-3's true residue, refusing on drift) — or the overlay stays until the
  D-3 lane (Q2).
- **D8** Hash-pinned output + the `FuncId` list + footprint (their (a), (b), (e)): `derive.py` writes `tools/raftsubject/codec-funcids.tsv`
  (every generated function/method: wire key, upstream twin file:line, footprint class — reads of `b`/the receiver, writes of the
  receiver's fields/`unknownFields`, allocation, recursion bound) and a `GENERATED_DIGESTS` table of the emitted files, both checked by
  `--check`; the generator is deterministic (sorted field numbers), so regeneration churns nothing.
- **D9** Instruments, red-first: `difftest.py` §8 (the 26-entry corpus imported with provenance from raft-proofs
  `fixtures/i6/malformed-conf-bytes.json` @ `f3d857f`, frozen; + a generated adversarial battery over all nine types; exact);
  `codeccheck.py` gains the same corpus as check ids under both oracles; the corpus rows of §5; two twin schedules through RawNode
  via `runprobe.py`.
- **D10** `errors.Is` stays refused on the machine by name (FR-14/G6); recorded as a stated limit, not a delta.
- **D11** Prototext `String()`/`Descriptor()`/`EnumDescriptor()`/`UnmarshalJSON` stay fail-closed stubs (C1); enum `String()` stays real.
- **D12** Records at landing: twin wire RE-PINNED under `--slow` with the written reason and a structural diff; U-1/U-2/U-3 RETIRED,
  D-4 RETIRED, D-1 and D-3 NARROWED, JC-14/JC-15 amended, `raftsubject/README.md` item 4 rewritten; no BUGS.md entry (subject deltas).

## 5. Acceptance plan

- **Born differential rows vs go1.26.5** (`Corpus/coverage/exec/multipkg/wire-codec/`, `wirepb` extended to mirror the NEW generated
  forms exactly — the corpus pin for the language shapes the codec runs on; fixtures are stdlib-only, so protobuf-go itself is never
  a corpus oracle): strict — `unknown-retain-reencode` (tag canonicalized, arrival order, after known fields), `wrong-wiretype-retain`,
  `group-skip-nested` (depth 0–3, one unknown field), `group-end-mismatch`, `group-truncated`, `stray-end-group`, `field-number-zero`,
  `field-number-max` (2^29−1 accepted), `field-number-over-max-top-vs-in-group` (the §2 asymmetry), `varint-ten-bytes`, `varint-overflow`
  (10th byte ≥ 2), `varint-truncated`, `packed-accepted-unpacked-emitted`, `bytes-empty-presence`, `merge-twice-singular`,
  `enum-unlisted-value-stored`, `typed-nil-{marshal,size,clone,equal}`, `nil-and-empty-input`, `recursion-depth-10000-vs-10001`
  (nested `responses`; the group limit too), `sentinel-unwrap`; membership — `prefix-pick` (lengths {44, 45}) and `panic-abort-text`
  (the two spellings, gc's draw inside). Exact texts: `proto: cannot parse invalid wire-format data`, `proto: exceeded maximum
  recursion depth`, `protobuf error`.
- **Exactness vs protobuf-go**: `difftest.py` §8 per input — verdict; `errors.Is(err, Error)`; text equal after normalizing the ONE
  prefix byte (reference bit recorded); `Size` and `Marshal` bytes; `Clone` + `Equal`. A NOTE class does not exist for §8. Red-first:
  16 + 10 corpus entries fail against today's codec (the feasibility measurement).
- **Through RawNode** (`runprobe.py`, twin schedules; instruments, not gates): a malformed ConfChange proposal → both legs abort with
  the subject's text (membership over the spellings); an unknown-GROUP proposal → accepted on both (the entry reaches Ready).
- **Deltas retiring**: U-1, U-2, U-3 (resolved), D-4 (confchange overlay — JC-13); narrowed: D-1 (`unknownFields` kept), D-3 (two
  `fmt.Errorf` lines); unchanged: D-2 (generated clone/equality, now over unknowns), D-9 (generated dispatch, reshaped).
- **Pins and certification**: `baselines/pins/twin-chdriver.wire.json` moves (subject bytes change) — re-pin under
  `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff --slow` with the reason in `check-frontend-pins`' history; `hidden-dep-order`
  and `stdlib-pin.tsv` unchanged (no new stdlib surface; `math/rand.Intn` is already on the register if D5-i); `derive.py` is in the
  certification `tools/` inventory, so `release-check` reports a changed dependency and step 5a is a provenance refresh under
  `--slow` (precedent trains r55/r56), not a certified re-pin; `check-stdlib-register` unchanged (primitive 3/3, overlay 5/12).
- **The logic team's §5, one-to-one**: (a) named `FuncId` list → D8's TSV; (b) deterministic hash-pinned generator output → D8's
  digests + `--check`; (c) plain indexed loops / `break`/`continue` / depth-bounded recursion / no reflection → D6 (+ D4's counter);
  (d) the init pick as ONE labelled choice consumed before `main` → D5; (e) a documented footprint → D8's footprint column; their §4
  caveat (C3) → item 4 landed, the `probePanic` evidence; rendering equations for error payloads are unit 6b's deliverable.
- **Gate**: `scripts/ci --diff --slow` green via `scripts/capped`; `derive.py --check`, `difftest.py` §1–§8, `codeccheck.py` green;
  no existing row's observations change except the twin pin; the pre-merge audit asked, never skipped.

## 6. Open questions for the [USER]

- **Q1 (D5)** The spelling pick's site: `rand.Intn(2)` on the pinned `intn` site (recommended: one lemma already exists) or the
  prototype's `mapIter` two-key range (the shape the logic team explicitly accepted)?
- **Q2 (D7)** Retire the `confstate.go` overlay to upstream + a two-line exact-text patch now, or leave it whole for the D-3 lane?
- **Q3 (D4)** Confirm C1's scope includes the raftpb client API, so `errRecursionDepth` (reachable only via `Message.responses` at
  > 10000 nesting, never through RawNode) is generated rather than refused by name.
- **Q4 (D3)** Accept that D-3 (`%+#v` ConfState dumps) can never be exact under any route (the `state` pointer in upstream's dump) and
  record it as a permanent narrowed premise in raft-proofs' §4 form?
- **Q5 (D6)** Is the tagless `switch` acceptable to the logic team's supported forms, or should the generator emit an `if` chain?
- **Q6** Go-ahead and sizing: 3–3.5 Opus sessions as S1–S3, the audit ask at the end, merge as one train with the `--slow` re-pin.
- **Q7 (outside this lane)** `tools/lowerdiag`'s static tables still judge `math/rand.Intn` refused (the 5b primitive is dynamic-only
  in its view): a one-line table fix lane, or leave as a known staleness?

## 7. Ratification (2026-10-04)

[USER] Mike 2026-10-04, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Approved». This ratifies decisions
D1–D12 as recommended, and the open questions as the coordinator recommended (per-question outcomes as relayed by the [AGENT]
coordinator, ratified by the [USER] «Approved»):

- **Q1 (D5)** — the spelling pick uses the `intn` site (`rand.Intn(2)` on `ChoiceSite.intn`; index 0 = U+0020, 1 = U+00A0), not
  `mapIter`.
- **Q2 (D7)** — retire the `confstate.go` overlay NOW, inside this lane (upstream text + the two-line exact-text subject patch).
- **Q3 (D4)** — yes: the raftpb client API is in scope; `errRecursionDepth` is generated, not refused.
- **Q4 (D3)** — D-3 (`%+#v`) accepted as a PERMANENT stated inexactness.
- **Q5 (D6)** — PENDING: the tagless `switch` question is being relayed to the logic team by the [USER]. Build with the design's
  shape (tagless `switch` field dispatch), but keep the tagless-switch sites easy to change and list them.
  **RESOLVED 2026-10-04 — KEEP** (the logic team's answer (a), below in §8 «Logic team answers»): `DISPATCH_FORM` stays
  `"tagless-switch"`; no generator change.
- **Q6** — go-ahead at 3–3.5 sessions as slices S1–S3, EACH gated + audited before merge.
- **Q7** — `tools/lowerdiag`'s stale `math/rand.Intn` judgement is a SEPARATE fix, outside this lane.

Build lane for slice S1: `lane/route-a-s1-1004` (worktree `.claude/worktrees/route-a-s1`), branched from this design branch at
`04b659f0` so the note lands with the build.

## 8. S1 build record (2026-10-04) — [AGENT] S1 build worker, lane `lane/route-a-s1-1004`

Delivered against §3's S1 row (generator + dispatch + overlays) and the coordinator's brief (the D9 instruments red-first, the
born corpus rows): D1 (`plain_wire.go` + `plain_codec.go` + `plain_clone.go`, each function's twin by file:line), D2 (interface
dispatch; `proto` no longer imports `raftpb`; typed-nil Marshal → `nil`), D3 (`unknownFields []byte` kept), D4 (`errDecode`,
`errRecursionDepth`, both `*prefixError` unwrapping to `proto.Error`; the two depth counters), D5 (`var prefix = pickPrefix()`,
one `rand.Intn(2)`), D6 (below), D7 (`confchange.go` verbatim; `confstate.go` upstream + the D-3 patch), D8
(`tools/raftsubject/codec-funcids.tsv`, `GENERATED_DIGESTS`, both under `--check`), D9 (difftest section 8 + codeccheck
39–51/100–125, red-first then green; 24 corpus rows), D10/D11 unchanged surfaces, D12's records for what S1 changes (ledger
continuation in `docs/raft-w42-log.md`, JC-13/14/15 amended, the twin re-pin, README). S2 keeps the RawNode twin schedules
(`runprobe.py`); S3 the rest of D12.

[AGENT] readings inside the ratified decisions, stated for review (none moves a decision):
- **D6 loops.** «Indexed `for` loops only» is read as: no `range`, no `for {}`; three-clause loops, and single-condition
  loops where the code consumes a byte slice (`for len(b) > 0`, upstream's own decode-loop shape). Upstream's `for {}` group
  loop (`consumeFieldValueD`) is `for len(b) > 0` + an explicit `errCodeTruncated` return — the value upstream's `ConsumeTag`
  gives on empty input. If the logic team's (c) means three-clause only, it is a generator change, not a design one.
- **Twin signatures.** `consumeFixed32/64` return the length only (a skip never reads the value); `consumeVarintValue` /
  `consumeBytesValue` are the shared heads of the per-kind consumers, each kind's store inlined at its field arm.
- **`proto.NewError`** is exported from the stand-in (the twin of `internal/errors.New`) because the generated codec — the
  `internal/impl` twin — declares its two error values through it; it is not part of upstream `proto`'s API.
- **Not reproduced, capacity only:** the packed-field pre-grow (`growUint64Slice`) and `Marshal`'s `growcap` buffer sizing —
  slice CAPACITY, which `append`'s own latitude already leaves open.
- **`proto.Unmarshal(b, nil)`** nil-dereferences through `m.ProtoMessage()` on the nil interface, as upstream's
  `m.ProtoReflect()` does.
- **§2 wording correction.** `equalUnknown` compares, per field number, the CONCATENATION of that number's records in arrival
  order (`mx[fnum] = append(mx[fnum], x[:n]...)`), not a multiset; the generated twin does exactly that (section 8's
  `unknown-same-num-xy`/`-yx` pair is unequal on both sides).

**Q5 (PENDING) — the tagless `switch` sites.** ONE constant, `derive.py` `DISPATCH_FORM` (`"tagless-switch"` | `"if-chain"`),
renders every site; the if-chain form generates and compiles (checked by a scratch derivation + `go build` of the twin), it is
not machine-run until chosen. Sites: the field-number dispatch inside `UnmarshalMessage` of each of the nine raftpb types
(`Entry`, `SnapshotMetadata`, `Snapshot`, `Message`, `HardState`, `ConfState`, `ConfChange`, `ConfChangeSingle`,
`ConfChangeV2`) — the `dispatch` column of `codec-funcids.tsv` — and the same four sites in the corpus mirror
(`Corpus/coverage/exec/multipkg/wire-codec/wirepb/plain_codec.go`: `Entry`, `ConfChange`, `ConfState`, `Message`), which
`--check` regenerates with the subject. No other `switch` is emitted.

**OPEN ITEM (a deviation the apparatus forces — reported, not self-adjudicated).** §5's `recursion-depth-10000-vs-10001` corpus
row is NOT born: each edge decode costs 10M–40M machine steps (measured: 9999/10000 nested `responses` and 10001 nested groups
fuel-out at 10M and complete at 40M; 10002 groups completes under 10M), past the strict lane's fixed 10M fuel, and a per-row
fuel parameter would be an apparatus (trusted-surface #2) change. Covered instead by `codeccheck.py` checks 48–51 (the machine
leg runs at fuel 3e8; both oracles agree) and `difftest.py` section 8 (exact vs protobuf-go). Options for the [USER]: (i)
accept the instrument coverage as the row's stand-in; (ii) a strict-lane fuel parameter (apparatus change, its own lane);
(iii) a born-red row with a ledger entry.

**Consumer-visible effect of D5, stated.** Every program that links the subject's `proto` package (the twin, raft's own
tree) now consumes ONE `intn` pick (bound 2) during package initialization, before `main` — the logic team's (d). Under the
default (all-zero) tape it takes slot 0 (U+0020) and nothing else moves: the twin driver's observation (`probeTwinChoice`,
default stream) is byte-identical on the pre- and post-S1 wires. A POSITIONAL choice-tape record made against the pre-S1 twin
(an explicit `--choices` stream) is shifted by one consumption; a ∀-stream statement (T1) is unaffected.

**Pre-existing finding.** `codeccheck.py`'s machine leg was already red on `main` (an E13 (b) structural-allocation quarantine
on two battery literals); the red-first commit hoists them.

**Logic team answers (2026-10-04) — Q5 RESOLVED, the D6 loop reading ACCEPTED.** The golean-logic coordinator, 2026-10-04,
by cross-session message relayed by the [AGENT] coordinator, verbatim:
- (a) «Tagless `switch { case num == 1: … }` is fine — keep it; no need for an if-chain or tagged switch. … leave
  DISPATCH_FORM as is.» → **Q5 RESOLVED: KEEP.** `DISPATCH_FORM` stays `"tagless-switch"`; the if-chain form stays
  generate-and-compile only.
- (b) «Condition-only loops `for len(b) > 0 { … }` are acceptable — no rewrite needed. … "plain indexed loops" in our note
  was an example of supported shape, not a requirement. Our logic is partial-correctness … the termination measure isn't
  used by our proofs, though recording it is welcome.» → **the D6 loop reading above is ACCEPTED by the consumer**; no
  generator change (adversarial audit Minor-1 closed by this answer).

**The recursion-edge row — [USER] ruling (i), a STATED LIMIT.** [USER] Mike 2026-10-04, verbatim, relayed by the [AGENT]
coordinator — cite as relayed: «agree to (i)». The `recursion-depth-10000-vs-10001` corpus row is NOT born. Its stand-in:
`codeccheck.py` checks 48–51 (both oracles, the machine leg at raised fuel 3e8) and `difftest.py` section 8 (exact vs
protobuf-go). Stated limit: the differential baseline itself does not exercise the 10000/10001 recursion edges (each edge
decode costs 10M–40M machine steps, past the strict lane's fixed 10M fuel); options (ii) (a strict-lane fuel parameter, an
apparatus change) and (iii) (a born-red row) are not taken.

**Landing.** Merge sign-off [USER] Mike 2026-10-04, verbatim, relayed: «merge it and share» — train r65 (Fable adversarial
audit MERGE-CLEAN; Minor-1 closed above, Minor-2 by the post-offer changelog `docs/changelog/20d3946d-WINDOW.md`).

## 9. S2 build record (2026-10-05) — [AGENT] S2 build worker, lane `lane/route-a-s2-1005`

Authority: [USER] Mike 2026-10-05, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Go ahead with Route A S2».
Off `main` @ `72e309c2`. Delivered against §8's «S2 keeps the RawNode twin schedules (`runprobe.py`)» — §5's «Through
RawNode» item of D9; nothing else in the slice plan is assigned to S2 (§3's S2 cost row also named the differential
instruments and corpus rows; S1 delivered those, §8). No change to the subject, `GoLean/`, the trusted surface, the stdlib
register, the wire schema, or any baseline; the twin wire pin does not move.

- **The two schedules** (`tools/raftsubject/twin-codec-lib.go` + thin mains `twin-codec-abort-main.go`,
  `twin-codec-group-main.go`): the n=3 twin, node 1 elected (campaign + drain), then a hand-encoded EntryConfChange MsgProp
  stepped into FOLLOWER 2 (`RawNode.Step`), forwarded through the multiset and decoded by the leader at `raft/raft.go:1326`.
  Payload = the subject's `Marshal` of `ConfChange{Type: UpdateNode, NodeId: 2, Id: 7}` (`08 07 10 02 18 02`) plus a tail:
  `7b` (a field-15 group left open → `errDecode`) for **codec-abort**; `7b 08 2a 7c` (a complete field-15 group carrying
  field 1 = 42) for **codec-unknown-group**.
- **Observations.** codec-abort: both legs abort with `proto: cannot parse invalid wire-format data`, checked by MEMBERSHIP
  over the two spellings (each leg draws its own: `go run` per process; the machine's init pick is the stream's first
  consumption — default tape slot 0 = U+0020, `--choices 1` slot 1 = U+00A0; both witnessed). codec-unknown-group: strict
  trace agreement — the entry reaches Ready on all three nodes with the payload byte-identical (`same=1`), commits at
  index 3, and each node's application decodes it through the subject `proto`, applies it (UpdateNode: a configuration
  no-op, voters=3) and re-encodes it byte-identical (`reencode-same=1`, `Size` = 10: the group retained and re-emitted
  after the known fields); `viol=0`.
- **runprobe.py** gains the ABORT-MEMBERSHIP mode `--expect-panic-member TEXT` (repeatable; exactly one `panic: <m>` line
  on `go run`, machine status `panic` with message <m'>, each EXACTLY a member; `\uXXXX` escapes decoded) and `--choices`
  (passed to the machine leg). Existing modes unchanged.
- **Red-first** (no S2 change turns them green — S1's codec already does — so the red is shown against the PRE-route-A
  subject, `raftsubject/` @ `6aa04c5d`): both schedules abort with `plainpb: malformed wire input` on BOTH legs (not a
  member; the unknown-group proposal refused instead of accepted — U-1/U-2 through RawNode).
- **Upstream anchor** (one-off, not an instrument): the same two schedule files over UPSTREAM raft @ `56e32004` + the real
  protobuf-go v1.36.11 — abort with `proto: cannot parse invalid wire-format data` (that binary's U+0020 draw) at upstream
  `stepLeader`; the unknown-group trace BYTE-IDENTICAL to both subject legs.
- Evidence: `docs/evidence/2026-10-05_route-a-s2/rawnode-schedules.txt` (red, green, anchor) and the gate tail(s) beside it.

[AGENT] readings inside the ratified decisions, stated for review (none moves a decision):
- **Own harvest.** `twin-lib.go`'s harvest flags every non-EntryNormal entry as an S3 anomaly («v1 proposes no conf
  changes»), so the codec schedules run `harvestCC` — the same persist/record/send/apply/Advance cycle plus a conf-change
  apply arm — rather than editing `twin-lib.go`, which would move the pinned twin wire for no semantic reason.
- **Proposal at a follower via `RawNode.Step`**, not `ProposeConfChange` (which encodes a well-formed value); the forwarded
  path is the one a peer's raw bytes take. UpdateNode is chosen so applying the change neither reshapes the cluster nor
  addresses a message outside the twin.
- **Instruments, not gates** (§5): `scripts/ci` does not run them.

Consumer visibility: none of S2 changes what a consumer of the subject, the wire or a GoCore program observes (no choice
consumption, no subject delta, no twin wire move). An informational changelog line is drafted for the landing train.

Where S3 starts: the rest of D12 — the deltas' final records (U-1/U-2/U-3 already RESOLVED and D-4 RETIRED by S1 in
`docs/raft-w42-log.md`; S3 confirms and closes them against these RawNode witnesses), JC-14/JC-15 and `raftsubject/README.md`
item 4 final wording, the `--slow` re-pin only if S3 moves the twin wire (S2 does not), and the pre-merge audit ask.
