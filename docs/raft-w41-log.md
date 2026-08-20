# Raft W4.1 campaign log — the run unblock

Lane: `raft-w41` (worktree `.claude/worktrees/raft-w41`), branch `raft-w41`
off `main` @ `0bb74f18` (the W4.0 tip). Charter: harness design
(`docs/2026-08-20_machine-twin-harness-design.md`) §8's W4.1 slice — the run
blockers, five commit-groups, then the census and the first RawNode probe.
Owns frontend, `Corpus/`, `baselines/`, `raftsubject/`, `tools/raftsubject/`,
and this log. Conventions: the bug-fix arc charter's — guardrails first,
predicted flips stated pre-run, same-commit re-pins.

Inherited (W4.0 census, `docs/raft-w4-log.md`): 7 run-blocker causes over 22
live quarantined declarations + 3 live codec panics + 1 live imported stub.
The items, in landing order: H-1 (the wire codec), H-6 (+H-17? no — H-18
rides here; see item 2), H-15 (the jitter choice site), the smalls
(H-17 `strings.Join`, H-13 `bytes.Equal`, H-14 `binary.LittleEndian`),
H-12 (promoted mutex ops).

DONE criterion: harness design §8 W4.1, the five-clause fail-closed census —
zero REACHABLE fail-closed stops of ANY class — then the first RawNode
execution probe, reported honestly.

## Environment notes (2026-08-20)

- Fresh worktree; `scripts/setup-deps --from /home/dev/projects/golean` exit 0
  (goose 3be88bb, perennial 43d4efa, raft 56e3200, iris-lean 3877dbe, go
  c19862e5f8).
- This workspace's sandbox denies the shared Go module cache
  (`/home/dev/go/pkg/mod` unreadable) and the module proxy — re-verified at
  the start of this arc (`difftest.py` fails at
  `verifying google.golang.org/protobuf@v1.36.11: ... permission denied`), and
  `deps/raft` has NO vendored protobuf. So the upstream-protobuf half of the
  codec differential is OWED-WITH-COMMAND (ask-don't-hack), and the in-sandbox
  validation is structural + golden + machine-vs-go — see item 1.

---

## Item 1 — H-1, the plainpb wire codec

**Landed.** `derive.py` gains `gen_codec` (emits `raftpb/plain_codec.go`:
per-type `SizeMessage`/`AppendMessage`/`UnmarshalMessage` from the parsed
field lists, cross-checked against the pinned struct tags) and `gen_proto`
now emits REAL dispatch bodies for `Clone`/`Marshal`/`Size`/`Unmarshal`
(type switch over the nine plainpb types; `Clone` dispatches to the
already-derived `CloneMessage`; defaults still panic fail-closed). The
`MarshalConfChange` overlay rejoins upstream's logic with the two
`proto.Marshal` calls as `AppendMessage` (JC-13). Headers that claimed
marshal-avoidance ("no Marshal/Unmarshal/Size lives here at all") are
rewritten to describe the codec.

**Validation, in the order it ran:**

- **Machine capability probe** (scratch, pre-generator): a hand-mini codec
  with the same forms (varint loops, byte ops, pointer presence,
  cross-package type-switch dispatch) exported and ran identically under
  `go run` and the machine (`11109 1` both sides).
- **`codeccheck.py` (new tracked instrument): PASS.** 38 checks — round
  trips + Size=len∘Marshal over 19 value shapes, 8 hand-computed golden
  byte sequences (varint edges 300/2^40/MaxUint64, field-number order,
  present-but-zero, non-nil-empty Marshal), 8 decode-only paths (packed
  acceptance, unknown skip, embedded merge, reset-vs-merge, 4 malformed
  refusals), 3 raft shapes (the stepLeader `MarshalConfChange` →
  `Entry.Data` → `Unmarshal` round trip; `entsSize`'s Size) — under BOTH
  oracles, verdicts agree at 0.
- **Corpus guardrails:** `multipkg/wire-codec/{roundtrip,size,golden,
  unknown-skip,malformed}` — the codec's language shapes as a tracked
  differential family (local package `wirepb` mirrors the generator's
  output forms; ConfChange numbering deliberately differs from struct
  order so number-ordered encoding is pinned). Focused run: 5/5 PASS.
- **`difftest.py` section 7 (the upstream-runtime differential): WRITTEN,
  NOT RUN — owed.** The sandbox denies the module cache/proxy (environment
  notes). The generated Go parses (`gofmt -e` clean); the command owed:
  `python3 tools/raftsubject/difftest.py` with normal GOPROXY access.
- **Instruments:** `derive.py --check` clean; `frontier.py` EXPORTS CLEAN
  (terminal-row plan unchanged); `sweep.py` reproduces the W4.0 census
  EXACTLY (22 LIVE / 49 quarantined / 113 imported stubs, residual sinks
  none, G-1 cross-check OK) — the codec was never a quarantine, so the
  census does not move; what moved is that the 3 live codec PANICS (+ the
  JC-13 fourth, `MarshalConfChange`) now have real bodies. `go build` over
  the subject tree: clean.

**One frontend gap hit and NOT fixed (logged per charter):** the battery's
first draft used calls/slice literals inside `||` second operands and was
refused `frontend-quarantined: slice literal in short-circuit operand` —
the KNOWN E3 normalization bound (triage-table F24's class), not a
codec-path gap; the battery was restructured to hoist. Watch item: raft's
own live decls could surface this class as a SECOND cause once the census
causes clear — the post-item sweeps will show it if so.

**Predicted flips for the full differential (stated before the run):**
exactly 5 NEW ids (`multipkg/wire-codec/*`), all PASS; zero movement on
the 2253 pre-existing ids (no frontend change in this item; corpus
otherwise untouched). Baseline re-pinned same-commit with this reason.

### Judgment calls

- **JC-11: the codec is GENERATED by `derive.py`, not hand-written.** The
  field numbers, wire types and presence modes are already parsed out of
  upstream `raft.pb.go` by the `plainpb` mode (the same field lists that
  generate `CloneMessage`/`EqualMessage`), so the codec generator is the
  mechanically-justified route the task offers: `gen_codec` emits
  `raftpb/plain_codec.go` from those lists, python-side cross-checking each
  struct tag's wire type/mode against the Go field type and REFUSING on any
  field shape it has no rule for. A hand-written codec would drift when the
  pin moves; this one re-derives or refuses.
- **JC-12: `proto.Clone` is in scope although the task names three entry
  points.** The done criterion (§8 clause 3) counts LIVE fail-closed panic
  stand-ins including `Clone`, and the W3 census measured Clone LIVE
  (snapshot paths). Clone dispatches to the already-derived
  `CloneMessage` — no new cloning logic.
- **JC-13: `MarshalConfChange` (raftpb overlay) rejoins upstream.** The W4.0
  census's class-3 list ("the proto package: Clone, Marshal, Unmarshal,
  Size") MISSED a fifth fail-closed panic stand-in: the overlay's
  `MarshalConfChange`, which is LIVE under the twin
  (`RawNode.ProposeConfChange → confChangeToMsg → MarshalConfChange`) — the
  marshal-avoidance argument ("its only caller, node.go's confChangeToMsg,
  is not in the subject tree") was stale the moment W2.2's `select` mode
  kept `confChangeToMsg`. Recorded here as a census correction; the overlay
  now carries upstream's body with the two `proto.Marshal` calls replaced by
  the per-type `AppendMessage` (raftpb cannot import the subject-local
  `proto` package — `proto` imports `raftpb`).
- **JC-14: Unmarshal semantics = protobuf wire spec over the 9 schemas,
  fail closed at the edges.** Merge semantics (proto.Unmarshal = Reset +
  merge; embedded messages merge, scalars last-one-wins, repeated append);
  unpacked AND packed acceptance for repeated varints (parsers must accept
  both; we EMIT unpacked, matching protoc-gen-go proto2 defaults and the
  pinned tags); unknown fields are SKIPPED per wire type (recorded delta:
  real protobuf PRESERVES unknowns for re-marshal — unobservable inside the
  twin, where every byte parsed was produced by this codec or the
  differential's generator, and difftest-visible if it ever matters);
  wire types 3/4 (groups) REFUSE — no group exists in any of the 9 schemas.
  Wrong-wire-type known fields are skipped as unknown (protobuf-go's own
  treatment). Varint bounds are protobuf-go's (≤10 bytes, 10th ≤ 1).
- **JC-15: the byte-fidelity bar and where each half is validated.**
  Marshal emits fields in FIELD-NUMBER order (protobuf-go's table-driven
  marshaler order; maps — the one Deterministic-flag concern — do not occur
  in these schemas). Empty-but-present `[]byte` emits tag+len0 and
  unmarshals to a non-nil empty slice (proto2 bytes presence). Marshal of a
  message with nothing set returns `[]byte{}` non-nil (protobuf-go's
  empty-message behavior). The upstream differential (difftest.py section 7,
  byte-equality vs proto.Marshal + cross-unmarshal + Size) is OWED — the
  sandbox denies the module cache/proxy (see environment notes); command:
  `python3 tools/raftsubject/difftest.py` with normal GOPROXY. In-sandbox:
  `tools/raftsubject/codeccheck.py` (new instrument) runs the DERIVED codec
  under BOTH `go run` (GOPATH scratch, stdlib-only) and THE MACHINE
  (frontend export + `golean native-json-run`), comparing observations:
  round-trips (Unmarshal∘Marshal = id via EqualMessage), Size = len∘Marshal,
  and HAND-VERIFIED golden byte sequences (computed from the wire-format
  spec by hand, written into the battery).
