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

**Gate:** `scripts/ci --diff` at the item-3 commit — full PASS
(2294/2294, no regression).

**THE-MOMENT instrumentation (built here, consumed after item 5):**
`tools/raftsubject/runprobe.py` + `rawnode-probe-main.go` — the minimal
single-node RawNode drive (snapshot-seeded voter, tick, campaign,
propose, Ready harvests with Advance, a digit-packed summary), run
under both oracles with the machine's first stop reported VERBATIM.
Dry run at the item-3 tip: `go run` completes (111035); the machine's
first stop is `frontend-quarantined: method raft.MemoryStorage.
ApplySnapshot (sync.Mutex.Lock outside a direct statement/defer
position ...)` — item 5's cause, named exactly.

---

## Item 4 — the smalls: H-17 strings.Join, H-13 bytes.Equal, H-14 binary.LittleEndian

**Landed.** Three mechanisms, judgment logged per shape:

- **JC-20: `strings.Join` and `bytes.Equal` are ordinary E5 direct-call
  shims** (`goleanShimStringsJoin`, `goleanShimBytesEqual`) — the same
  allowlist/injection/collision machinery as `strings.Fields`, no new
  mechanism. Join is plain concatenation (byte-identical to upstream's
  Builder-based body by construction); Equal is length-then-bytes,
  which gives the documented "a nil argument is equivalent to an empty
  slice" for free (pinned: nil==empty is TRUE).
- **JC-21: `binary.LittleEndian.{Uint64,PutUint64}` is a
  PACKAGE-VARIABLE METHOD desugar** (`emitBinaryVarMethodCall`) — the
  callee is a method on the exported var of an UNEXPORTED type, which
  no selector-call path can name, so the two modeled members rewrite to
  shims mirroring encoding/binary's bodies INCLUDING the leading
  `_ = b[7]` bounds check (the early out-of-range panic is contract,
  pinned by `binary/little-endian/short-read`). An unmodeled member of
  a LISTED variable now refuses NAMING the member (better than the old
  anonymous-type resolution error); unlisted variables (BigEndian) keep
  their standing refusal untouched.
- **One scan defect found and fixed by the guardrails:** the injection
  scan's default import name was the PATH, wrong for multi-segment
  paths (`encoding/binary` binds `binary`); the miss failed CLOSED
  ("shim not injected", witnessed on the little-endian rows) and the
  default is now the last path segment, with the assumption written at
  the site.

**Guardrails (landed first, 12 rows, all witnessed red pre-fix):**
`strings/join-conformance` (5), `bytes/equal-conformance` (3),
`binary/little-endian` (4). Post-fix 12/12 PASS (short-read PASSES as
an expected-panic row). Frontend unit tests green; `codeccheck.py`
re-run PASS.

**Census after item 4:** **12 → 8 LIVE** — exactly G-6's 8
`MemoryStorage` methods (item 5's set). `newRaft`, `(*raft).Step`,
`readOnly.{recvAck,heartbeatCtx}` all lower. 25 quarantined in PASS 1;
residual sinks none; `frontier.py` EXPORTS CLEAN.

**Predicted flips for the full differential (stated before the run):**
exactly 12 NEW ids, all PASS; zero movement on the 2294 pre-existing
ids. Baseline re-pinned same-commit with this reason.

**Gate:** `scripts/ci --diff` at the item-4 commit — full PASS
(2306/2306, no regression).

---

## Item 5 — H-12, promoted sync ops — and the run itself

**Landed (one commit, two named concerns — coupled because the second
was FOUND BY the first's unblocked probe):**

1. **Promoted/embedded sync ops in statement/defer position**
   (`emit.go`): `emitSyncOpStmt`/`emitDeferSyncOp` now recognize a
   selection whose RESOLVED method is a sync primitive's
   (`syncSelectionPrim` — direct form byte-identical to before;
   promoted form takes the embedded hops) and the receiver address
   walks the hops (`promotedReceiverArg`, pointer receiver — every
   modeled sync op is). Expression-position ops and sync method values
   KEEP failing closed, with the guard and stub messages reworded to
   say what actually remains refused. Guardrails
   (`sync/promoted-mutex`, 5 rows, witnessed red first): stmt,
   defer-unlock, value-var, the confluent goroutine counter (mutual
   exclusion through the promoted lock certified over ALL schedules),
   and trylock-expr RED BY DESIGN. The two standing red-until-lifted
   witnesses (`sync/escapes/{promoted,defer-embedded}` — whose own
   header called the promoted shape "the north-star idiom" and this
   lift "the recorded follow-up") flip green;
   `sync/escapes/{method-value,go-stmt}` stay red.
2. **The named-typed-nil representation fix (BUG-016's arm, found by
   THE-MOMENT probe).** With zero live quarantines the first RawNode
   drive still STUCK the machine: `map equality expected map/nil
   operands, got GoValue.nil and GoValue.nil`. Minimized (probe
   ladder in artifacts/w41/probe-mapnil*): a nil at a DEFINED
   slice/map type — `tracker.Config.Clone`'s `return nil` at
   `quorum.MajorityConfig`, stored into a `JointConfig` composite,
   compared by `checkInvariants`' `outgoing(cfg.Voters) != nil` — was
   emitted as a BARE nil (the BUG-016 nil-typing arm deliberately
   skipped defined types, BUG-014's boundary), and the machine's
   fail-closed comparison refused two bare nils. Fix: the arm keys on
   the UNDERLYING kind and emits the UNDERLYING type's wire node —
   representation only (the bool-conversion-retyping argument: static
   consequences come from go/types at use sites), and exactly what the
   machine's nil-literal arm accepts. Func/chan slots keep bare nil
   (their comparison arms take nil/nil; chan ops on stored bare nil
   recorded as untested surface, not widened). Guardrails
   (`maps/named-nil-flows`, 5 rows witnessed red): the nil flowing
   through return/composite/literal-elem/arg at named map + named
   slice. The two standing stuck rows
   (`maps/nil-literal-values/defined-{map,slice}-element`) flip green.

**`sweep.py`'s cause-flatten table is EMPTIED — the fail-closed
direction.** Every cause it carried is modeled now; keeping the
flattening would let a regression that re-quarantines one be silently
flattened over in PASS 2 instead of surfacing as a residual sink. The
probe-helper injection and the mutex-op drop go with it; PASS 2 is now
purely neutralize-believed-dead + re-census to fixpoint.

**Predicted flips for the full differential (stated before the run):**
10 NEW ids (9 PASS incl. the confluent row + trylock-expr
FAIL/frontend-export by design), zero other movement. **The run REFUTED
the zero-movement half by FOUR rows — every one investigated before
re-pinning, and every one a RECORDED red-until-lifted witness of
exactly the two lifted classes** (named above; the honest reading is
that the prediction failed to grep for standing witnesses, not that
the change moved anything unexplained). Baseline re-pinned same-commit
(2316 cases, 2177/139).

---

## The W4.1 DONE criterion, clause by clause (harness design §8)

Census instruments at this tip: `frontier.py` EXPORTS CLEAN;
`sweep.py` (with the clause-2 extension and the emptied flatten);
`derive.py --check` clean; `codeccheck.py` PASS; subject `go build`
clean.

1. **Zero live QUARANTINED subject declarations** — **HEADLINE: 0 LIVE
   (0 first-order + 0 behind sinks) out of 15 quarantined in PASS 1.**
   The 15 dead: the rendering/JSON family (`Describe*`,
   `ConfChanges*String`, `String`s over strconv/fmt.Fprint/%q-Stringer
   shapes, `MarshalJSON`s), `MemoryStorage.{Lock,TryLock,Unlock}`
   method-set stubs, `slices.SortFunc`'s `MajorityConfig.Describe` —
   all unreachable from the twin's 16-entry API surface.
2. **Zero live quarantined IMPORTED stdlib stubs** — extended the sweep
   to census this class (it previously only counted them): **0 LIVE of
   30** (bytes.Buffer x24, strings.Builder's Cap/Grow/WriteRune,
   sync x3).
3. **Zero live fail-closed panic stand-ins** — the four `proto.*`
   bodies are REAL (item 1), and the fifth the W4.0 list missed
   (`MarshalConfChange`, JC-13) is real too. The plainpb
   `String`/`Descriptor`/`UnmarshalJSON` stubs remain panic bodies BY
   DESIGN and are not run-stops: `Descriptor`/`UnmarshalJSON` are
   unreachable; the enum/message `String`s are reached ONLY inside the
   fmt render helpers, where BOTH oracles run the same panicking body
   and fmt's recover renders identically (`%!v(PANIC=...)` — pinned by
   fmt/sprintf-verbs) — a symmetric, agreed behavior, not a stop.
4. **Nothing masked by a body-replacing walk row** — the tracked plan
   is the TERMINAL ROW alone since W4.0; D-11 (the jitter draw) is a
   DERIVATION patch carried by the subject itself — both oracles run
   the patched body, and the census reads the derived tree, so nothing
   is masked from it (the ledger records the delta; the membership row
   pins its envelope).
5. **Residual-sink report empty** — over subject AND imported stubs
   (the clause-2 extension widened the check), with the cause-flatten
   table EMPTY, so any reappearing cause would surface here rather
   than be flattened over.

## THE MOMENT — the first RawNode execution

`tools/raftsubject/runprobe.py` (tracked; both oracles, first stop
verbatim), probe `rawnode-probe-main.go`: a single snapshot-seeded
voter — `NewMemoryStorage`, `ApplySnapshot`, `NewRawNode`, `Tick`,
`Campaign`, Ready harvest (`HasReady`/`Ready`/`SetHardState`/`Append`/
`Advance`), `Propose([]byte("x"))`, harvest again — summary packed as
isLeader/term/committedNormal/applied/rounds.

> **`runprobe: go run probeRawNode -> 111035`**
> **`runprobe: machine probeRawNode -> 111035`**
> **`runprobe: PASS — both oracles agree: 111035`**

The machine executes etcd-io/raft's RawNode end to end — election,
leadership, a committed proposal, five Ready rounds — and agrees with
gc on the drive's whole observable summary. (Fuel used: well under the
2*10^8 given; wall clock ~seconds.) This is the W4.1 exit: every
remaining step to the W4.2 twin is harness Go, not machine surface.

---

## Handoff ledger effects (W3 §4's table)

| id | disposition |
|---|---|
| H-1 | **DISCHARGED** (item 1) — the generated codec; difftest section 7 OWED with command where the sandbox denies the module proxy; codeccheck.py is the standing in-sandbox battery. |
| H-6 | **DISCHARGED** (item 2) — the Q3 OPTION 1 desugar, per-verb pins. |
| H-12 | **DISCHARGED** (item 5) — promoted statement/defer sync ops. |
| H-13, H-17 | **DISCHARGED** (item 4) — E5 shims. |
| H-14 | **DISCHARGED** (item 4) — the package-variable method desugar. |
| H-15 | **DISCHARGED as D-11** (item 3) — the map-range choice site; the RANGE's latitude entry remains W4.5's. |
| H-18 | **DISCHARGED** (item 2) — the E5-T Builder model. |
| H-19 | unchanged (ErrStopped chunk granularity; its errors.New row stopped mattering when G-2 retired). |
| NEW → W4.2+ | the harness supplies `Config.Logger` AND `raft.SetLogger` (Q2, §5); `sync/escapes/{method-value,go-stmt}` remain the sync fail-closed frontier; chan-typed bare-nil ops recorded untested (item 5's fix note); the fmt matrix's boundary rows are the widening protocol's entry point. |

## W4.1 exit state

Branch `raft-w41`, six commits over `main` @ `0bb74f18`, one per
commit-group (items 1–5 + the follow-through), each landed
guardrails-first with predicted flips stated pre-run and same-commit
re-pins; every landing's `scripts/ci --diff` PASS is recorded in its
section. **Final gate at the tip: PASS** (2316 cases, 2177/139;
baseline diff FULL 2316/2316 no regression; negative lane no
regression; frontend unit tests, eval tests 136, proofs + Audit gate
all green). The one red any gate showed post-item-1 was the bug-index
cross-check catching BUG-014's pins flipping before the entry closed —
the gate doing its job; closed in the follow-through.

The DONE criterion's five clauses are discharged (the clause-by-clause
section above); THE MOMENT is recorded (go=111035 = machine=111035).
W4.2 (the twin, single node) starts from a machine that RUNS RawNode.

Open obligations carried forward: difftest.py section 7 vs the real
protobuf runtime (OWED with command — this sandbox denies the module
cache/proxy); the W4.5 latitude entries (the jitter range, the §2
harvest-atomicity re-envelope); the Q2 harness logger (W4.2's, the
design's §5 both-seams form); the fmt matrix's boundary rows as the
widening protocol's entry point.

**D-11 `(*lockedRand).Intn` — the jitter CHOICE SITE** (item 3, JC-19):
body replaced by the exact-text-keyed `SUBJECT_PATCHES` derivation
patch (map-range draw, envelope [0,n) on both oracles; upstream's
n<=0 panic preserved; mutex kept); `crypto/rand` + `math/big` imports
dropped. **Observable weight:** the draw's DISTRIBUTION differs (go's
map-iteration randomness vs crypto/rand uniformity) — the ENVELOPE is
identical, which is the semantics the twin's theorems quantify over
(possibilistic doctrine); the latitude entry against
`[electionTimeout, 2*electionTimeout)` is W4.5's. Pinned by the
`maps/jitter-draw` membership row (admitted set = the contract range,
all members exhibited).

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
