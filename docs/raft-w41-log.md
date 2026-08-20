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

**Gate:** `scripts/ci --diff` at the item-1 commit — full PASS; the
baseline drift was exactly the 5 predicted NEW ids. (The first run's 4
unrelated FAILs were this fresh worktree missing `proofs/.lake/packages`
— network clone denied by the sandbox; populated from the primary
checkout at the manifest pins: batteries fa08db5, iris 3877dbe, Qq
f463249. Environment, recorded.)

---

## Item 2 — H-6 (fmt, the Q3 OPTION 1 ruling) + H-18 (strings.Builder)

**Landed.** Two mechanisms, both frontend-side, no GoCore/wire-schema
change:

1. **The fmt desugar** (`tools/nativefrontend/fmtdesugar.go`):
   `Sprintf`/`Errorf`/`Fprintf` over a CONSTANT format string, parsed at
   emit time; each verb pairs with its argument's STATIC type against the
   modeled matrix (%d signed/unsigned ints incl. enums; %x unsigned; %s
   string/error/Stringer; %v ints/string/bool/error/Stringer; %+v = %v
   over this matrix; %q byte slices, ASCII subset; %%); anything else —
   other verbs, flags, width, non-constant formats, spread args,
   arity mismatches — refuses per-declaration naming the pair. The call
   site becomes a call to a LIFTED per-site `$fmtN(...) string` whose
   parameters receive the (converted/boxed/method-value) arguments — the
   lift is what preserves fmt's argument-evaluation order (all args
   before any String/Error call; probed against gc, pinned by
   `fmt/sprintf-verbs/eval-order`). The per-verb helpers are E5-injected
   Go source (`stdlibshim.go`, `goleanShimFmt*`): digit loops, the ASCII
   %q quoter (fail-closed on bytes >= 0x80 — real %q prints printable
   non-ASCII runes; recorded bound), and the recover-and-render helpers
   reproducing fmt's `%!<verb>(PANIC=String method: ...)` forms, the
   nil-pointer `<nil>`, and the nil-error `%!s(<nil>)`/`<nil>` split
   (all probed against gc first — artifacts/w41/probe-fmt).
   `Errorf` = `goleanShimErrorsNew(<lift>)` (without %w, fmt.Errorf IS
   errors.New over the text — fmt/errors.go); the errors shim is
   co-injected. `Fprintf` is modeled for writer static type
   `*strings.Builder` only and becomes `w.WriteString(<lift>)` (same
   results, same writer-then-args order).
2. **The strings.Builder model — "E5-T"**
   (`tools/nativefrontend/importedmodel.go`): a pinned mini
   `package strings` source (struct{addr *Builder; buf []byte} + the
   copy check + WriteString/WriteByte/Write/String/Len/Reset) is lowered
   by a FRESH emitter through the ordinary pipeline and its wire output
   harvested under the type's own identity (`strings.Builder`,
   `strings.Builder.WriteString`, ...) — host references need no
   rewrite. Cap/Grow/WriteRune stay declaration-only stubs (Cap would
   expose append's growth policy — allocator latitude); the D5 marker is
   suppressed for modeled types and the harvest asserts its shape (no
   funcs, no globals, no unlowered method) fail-closed. The copy check
   is SEMANTICS and panics with upstream's exact message
   (`strings/builder-model/copy-panics` pins it).

**Judgment calls:**

- **JC-16: renderers take the CONCRETE METHOD VALUE, not an interface.**
  The first cut boxed Stringer args into an injected
  `goleanShimStringer` interface; the shim's `v.String()` dispatch edge
  made the reachability instruments mark EVERY String method in the
  program a live candidate — measured on the raft tree: the census
  jumped to 18 LIVE with 5 false candidates (`quorum.Index.String`,
  `quorum.VoteResult.String`, `tracker.{Config,Progress}.String`,
  `raft.Status.MarshalJSON` via `Status.String`), whose causes
  (strconv, fmt.Fprint, %q-over-Stringer) would have dragged a widening
  cascade. The fix is also the more FAITHFUL shape: at every modeled
  site the static type is concrete, so the dynamic dispatch target is
  exactly one method — the desugar captures `arg.String` as a
  `func() string` (nil-pointer flag computed from the once-hoisted
  pointer; value-receiver-through-pointer args REFUSED — capture-time
  vs render-time deref differ on nil) and `goleanShimFmtRender` invokes
  it under the recover. Static-`error` args keep the interface helper
  (`goleanShimFmtError`) — its `error.Error` anchor edge marks only
  Error methods, all of which lower.
- **JC-17: five H-3 quarantine witnesses retargeted, not surrendered.**
  `methods/quarantine-{sibling,interface,pointer-receiver,embedded}` and
  `generics/stencil-quarantine` used `fmt.Sprintf` as their canonical
  unlowerable construct; the desugar made their red rows flip green,
  silently un-witnessing the per-declaration method quarantine (the F3
  lost-witness class). Their fixtures moved to `fmt.Sprint` (outside the
  modeled three) with the reason recorded in each file; every row keeps
  its exact baseline result+stage. Same for the frontend unit fixture
  (`quarantine_test.go`). `spec-examples-decl/timezone-stringer` stays
  FAIL at the same stage with a new detail (`%+d` outside the subset —
  detail is not a baseline column).
- **JC-18: %v over bool included though unmeasured in the census.** The
  matrix models %v over the basic kinds ints/string/bool as one
  language-natural completion (each differential-pinned:
  `fmt/sprintf-verbs/v-kinds`); everything else in fmt stays out.

**Guardrails (landed FIRST, 35 rows, all witnessed red pre-fix** — fmt
rows at `frontend-export` on the package-selector refusal, builder rows
at `lean-observation` on the marker-type default-value refusal**):**
`fmt/sprintf-verbs` (23: one per verb x kind incl. both panic-render
shapes, nil-ptr, nil-error, decision-path, eval-order, and 2 RED-BY-
DESIGN boundary rows — verb-outside-set `%T`, nonconst-format),
`fmt/errorf` (4: fresh/text/sentinel-classify/vs-errors-new),
`fmt/fprintf-builder` (2: the DescribeConfChange shape whole, returns),
`strings/builder-model` (7: write paths, len/reset, zero, copy-zero-ok,
copy-panics with upstream's message, string-stable). Post-fix: 33 PASS
+ 2 red-by-design. Frontend unit tests green.

**The census after item 2** (`sweep.py`, tracked instruments): **22 → 13
LIVE** quarantined subject declarations (30 quarantined in PASS 1, was
49; imported stubs 113 → 107 — Builder's six modeled methods left the
stub set). G-5 (all 10 fmt declarations) and G-10 retired on the wire;
`DescribeConfChange` lowers whole. The 13 = G-6's 8 MemoryStorage
(item 5) + G-1's `lockedRand.Intn` (item 3) + `newRaft` (G-9
strings.Join), `(*raft).Step` (G-7 bytes.Equal), `readOnly.{recvAck,
heartbeatCtx}` (G-8 binary.LittleEndian) — items 4's set exactly.
Residual sinks none; G-1 cross-check OK; `frontier.py` EXPORTS CLEAN;
`codeccheck.py` PASS (frontend change re-validated against the codec).

**Predicted flips for the full differential (stated before the run):**
exactly 35 NEW ids — 33 PASS + 2 FAIL/frontend-export by design
(`fmt/sprintf-verbs/{verb-outside-set,nonconst-format}`); ZERO movement
on the 2258 pre-existing ids (the five retargeted witnesses keep their
rows; timezone-stringer moves detail only). Baseline re-pinned
same-commit with this reason.

**Gate:** `scripts/ci --diff` at the item-2 commit — full PASS
(2293/2293, no regression; the drift run before the re-pin was exactly
the 35 predicted NEW ids).

---

## Item 3 — H-15, the election-jitter CHOICE SITE (G-1 retired)

**Landed as subject-delta D-11, a recorded `derive.py` patch — no
frontend, wire, or GoCore change at all.**

- **JC-19: the choice intrinsic is PLAIN GO — the map-iteration choice
  site.** The charter offered "frontend recognizes the lockedRand shape"
  or "a subject-tree overlay replacing lockedRand with a choice
  intrinsic". Taken: the overlay route, with the intrinsic being a
  construct the machine ALREADY treats as a choice site —
  `(*lockedRand).Intn`'s body becomes the first key of a range over a
  fresh n-key map. Under the machine that is the map-iteration pick
  (envelope = all n first keys, i.e. [0, n) exactly); under `go run` it
  is Go's own randomized iteration order (a real sampler of the same
  set). No new GoCore node, no frontend recognition rule, no wire
  change; `crypto/rand` + `math/big` are never modeled, exactly as the
  H-15 ruling directs (jitter is nondeterminism; the RANGE
  `[electionTimeout, 2*electionTimeout)` is the semantics, and the
  latitude entry against that range is W4.5's). The `n <= 0` upstream
  panic is preserved; the mutex ops stay (globalRand is shared state —
  dropping the lock would smuggle a concurrency delta; §6's checklist
  item 4 keeps globalRand's inertness argument, now with a lowerable
  body).
- **The derivation contract:** `SUBJECT_PATCHES` in `derive.py` — the
  patch keys on upstream's EXACT `Intn` text and refuses on drift (a
  new rev must be re-read); the import drops re-check that no CODE
  reference survives (comment-scoped: upstream's own doc comment says
  "rand.Rand"). `derive.py --check` clean; the subject tree builds.
- **`sweep.py`: the G-1 probe is RETIRED, replaced by a fail-closed
  tripwire.** The old standalone probe carried the UPSTREAM body to ask
  what `crypto/rand` costs — a question nothing depends on once the
  subject is off that surface. In its place the sweep now EXITS if
  `lockedRand.Intn` ever reappears quarantined (the patch not applying,
  or a regression un-lowering the body). The `globalRand.Intn` flatten
  row is gone (the body lowers for real).

**Guardrail:** `maps/jitter-draw` — a MEMBERSHIP row of the D-11 shape
verbatim (timeout 5): the machine ENUMERATES exactly {5,6,7,8,9} =
[electionTimeout, 2*electionTimeout) (1 choice site, 5 leaves, width
16 ≥ 6) and every go-run sample lands inside; the run exhibited all 5
members. This is the envelope statement's admitted set, mechanized.

**Census after item 3:** **13 → 12 LIVE** (Intn lowers; 29 quarantined
in PASS 1; imported stubs 107 → 30 — dropping the crypto/rand +
math/big imports removed math/big's 61 and math/rand's 16 marker
stubs). Residual sinks none. `frontier.py` EXPORTS CLEAN.

**Predicted flips for the full differential (stated before the run):**
exactly 1 NEW id (`maps/jitter-draw`, PASS at stage membership); zero
movement on the 2293 pre-existing ids (nothing outside `raftsubject/`,
`tools/raftsubject/` and this corpus row changed). Baseline re-pinned
same-commit with this reason.

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
