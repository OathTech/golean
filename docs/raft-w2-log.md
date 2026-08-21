# Raft W2 campaign log

Lane: `raft-w2` (worktree `.claude/worktrees/raft-w2`), supervised arc under
the standing merge/audit protocol. Charter: master plan
(`docs/2026-08-15_raft-master-plan.md`) §W2.1–§W2.2 — subject engineering, no
core ownership. Owns the vendored subject tree (`raftsubject/`), its
derivation toolkit (`tools/raftsubject/`), `raftharness/`, and this log. Does
NOT touch `Corpus/`, `baselines/`, GoCore, the frontend, or `scripts/` — every
need found there is a recorded handoff item below, not a change.

Base: `main` @ `e3859353`. `deps/raft` @ `56e32004b1af3a4cb625fbfe5dbca24fb6023d09`.

---

## §1 The RULING (Mike, 2026-08-19): `plainpb` over the gogo-rev pin

Recorded verbatim-in-substance, and mirrored into the scoping doc as a dated
RULING block (`docs/2026-08-15_raft-push-p0-scoping.md` §8.6, which is the
canonical location — §8 item 6 was the open decision it closes).

**The ruling.** The `plainpb` shim (scoping §7 layer C option 2), composed
with marshal-avoidance (option 3). NOT the gogo-rev pin (option 1).

**Rationale, as given.** Forward-looking: we verify the logic of the raft that
exists NOW, with the wire types *declared* rather than *generated*. Pinning
`deps/raft` backward to the last gogo rev would buy plain-Go
`Marshal`/`Unmarshal` at the price of verifying a library etcd has already
moved off. The encode paths are provably never taken under marshal-avoidance,
so declaring the types costs nothing we were going to exercise, and the
restrictions the shim imposes are liftable later without re-deciding this.

The ruling rests on a W1 measurement: at the pinned rev the runtime is
`google.golang.org/protobuf` (raft has already migrated off gogo), so §7's
"pin to the last gogo rev" means pinning BACKWARD — `docs/raft-w1-log.md`,
tier-1 probe.

**The four requirements, and where each is discharged.**

| req | requirement | discharged by |
|---|---|---|
| a | the shim is MECHANICALLY DERIVED by stripping the actual generated raftpb file; the derivation is a re-runnable documented script so the delta re-derives when the pin moves. `scripts/` is off-limits, so it lives in `tools/raftsubject/` — noted per the ruling | `tools/raftsubject/derive.py`; §2 below |
| b | every runtime-touching method (Marshal/Unmarshal/Size/descriptor init/registration) is a FAIL-CLOSED stub — explicit panic/refusal a differential would see, never a silent zero | §3, the fail-closed register |
| c | the subject delta is RECORDED — every divergence from upstream raftpb source itemised | §4, the subject-delta ledger |
| d | any shim method with real logic gets a differential obligation, probed against upstream under `go run`, comparison recorded | §5, `tools/raftsubject/difftest.py` |

Requirement (b) carries named residues rather than a clean discharge. The one
scoping §7 found is `proto.Size`: absent/fail-closed, while raft's flow
control computes protobuf wire sizes on its NORMAL path (`entsSize`/`limitSize`
in the raft root package). The pre-merge audit found a second and larger one —
`proto.Unmarshal` on raft's conf-change ADMISSION path (`raft.go:1314`/`:1320`)
— so the residue is decode-and-encode, not sizing alone; §3 censuses all four
sites and ranks them. Nothing in the packages vendored so far reaches any of
them. They are handoff item **H-1** below, not a quiet deferral.

Requirement (b) carries one further BOUND, also audit-found and recorded in §3:
the stub panics are a fail-closed guarantee for DIRECT calls, and `fmt` recovers
Stringer panics rather than propagating them. Unexploitable in the tree as it
stands; an input to the H-6 fmt ruling.

---

## §2 The derivation (requirement a)

`tools/raftsubject/derive.py` produces the whole of `raftsubject/` from
`deps/raft`. Three modes, and a digest gate in front of all of them.

- **`verbatim`** — copy, rewriting `go.etcd.io/raft/v3/<pkg>` to the short
  dot-free `<pkg>` (the frontend's case-relative multi-package convention,
  `docs/2026-08-18_multipackage-identity.md` §4/§6). That rewrite is the ONLY
  change. Two paths rewritten in the whole tree, both in `tracker/tracker.go`.
- **`plainpb`** — `raftpb/raft.pb.go` stripped declaration by declaration
  against a rule table keyed to RECOGNISED generated forms.
- **`overlay`** — a hand-written replacement for a file a script cannot
  strip, behind a **pinned upstream SHA-256**. Three of them:
  `raftpb/confstate.go`, `raftpb/confchange.go`, `raft/logger.go`.

**The re-derivation contract, which is the point of the exercise.** Every
vendored upstream file's SHA-256 is pinned in `DIGESTS`, and the derivation
refuses before writing anything if one has changed. For `verbatim` files that
is a courtesy; for `plainpb` and the overlays it is the contract — the rules
and the replacements were written against exactly those bytes. There is
deliberately no `--force` and no `--update-digests`: `--print-digests` emits
the table for a human to paste, so a pin move shows up as a reviewable diff.
The rule table itself fails closed the same way — **any top-level declaration
with no rule refuses the derivation**, naming it. A new protoc-gen-go release
must be read before the tree moves.

Two soundness guards on the (deliberately simple) declaration splitter, both
checked at run time: no multi-line raw string literal may exist (single-line
ones are fine — struct tags are exactly that), and the split chunks must
reassemble the source byte-for-byte.

**The getters are the interesting kept case.** raft calls `GetTerm`,
`GetIndex`, `GetType`, `GetAutoLeave` and friends on every normal path, so the
**40** generated getters are kept VERBATIM — and the derivation shape-checks each
one against the stripped struct's field list (canonical pointer shape vs
canonical value shape, receiver/field agreement, pointer-shape-only-over-
pointer-field, `nil` zero for the value shape). "Kept verbatim" is therefore
a checked claim, not an assumption.

**Sizes.** Upstream `raft.pb.go` 1233 lines → derived 765, plus 624 lines of
generated `plain_clone.go`. 9 message structs (40 fields, field numbers
preserved in the struct tags), 4 enums with constants and name/value maps,
**40** getters, 4 `Enum()`, 9 `Reset()`, 9 `ProtoMessage()`.

The getter count breaks down per message as: `Entry` 4, `SnapshotMetadata` 3,
`Snapshot` 2, `Message` 14, `HardState` 3, `ConfState` 5, `ConfChange` 4,
`ConfChangeSingle` 2, `ConfChangeV2` 3 — 40 total, and **the per-message
counts equal the per-message FIELD counts, every one of the nine**. That
equality is the check worth stating: the shim exposes exactly one getter per
declared field, so the 40 matching the struct field count above is a property,
not a coincidence to be squinted at.

*(Corrected 2026-08-19 from "37", which the pre-merge audit caught, and the
provenance was reproduced rather than guessed: a counting regex whose receiver
class was `[A-Za-z]+` —* `^func \(x \*[A-Za-z]+\) Get[A-Za-z]+` *— returns
exactly 37, because the class admits no DIGIT and so misses all three getters
on `ConfChangeV2`, the one message type with a digit in its name. 40 − 37 = 3,
the whole gap. The lesson is cheap and general: **a count that feeds a doc
claim is re-derived by re-running it, and a type-name pattern in Go uses `\w`,
because Go identifiers contain digits** — here the language's own naming
convention for protobuf versions (`V2`, `V3`) guarantees they will.)

Reproduce: `tools/raftsubject/derive.py --check` (re-derives to a temp dir and
diffs; exit 1 on drift). Scope note: the drift walk compares every DERIVED file
against the tree, and the reverse walk (tracked-but-not-derived) scans `.go`
files only — `raftsubject/README.md` is hand-written and deliberately exempt,
which is also why `frontier.py` copies the tree with `README.md` ignored.

---

## §3 The fail-closed register (requirement b)

**30 fail-closed stubs** in the derived `raft.pb.go`, each an explicit panic
naming itself:

| stub | count | why it is runtime-touching |
|---|---|---|
| `(*T).String()` | 9 | `protoimpl.X.MessageStringOf` |
| `(*T).Descriptor()` | 9 | returns the gzipped raw descriptor |
| `E.String()` | 4 | `protoimpl.X.EnumStringOf` |
| `E.EnumDescriptor()` | 4 | ditto |
| `(*E).UnmarshalJSON()` | 4 | `protoimpl.X.UnmarshalJSONEnum` |

Plus one hand-written stub in the confchange overlay: `MarshalConfChange`
(upstream body is two `proto.Marshal` calls).

**33 dropped declarations**: the import block (`reflect`, `sync`, `unsafe`,
`protoreflect`, `protoimpl`), the `EnforceVersion` const block, 4×
`Descriptor()`/`Type()`/`Number()` enum triples returning protoreflect types,
9× `ProtoReflect()`, and the ten file-descriptor declarations
(`File_raft_proto`, `file_raft_proto_rawDesc`, `…rawDescOnce`/`…rawDescData`,
`…rawDescGZIP`, `…enumTypes`, `…msgTypes`, `…goTypes`, `…depIdxs`, `init()`,
`file_raft_proto_init()`).

**On "descriptor init/registration becomes a fail-closed stub".** A panicking
`init()` would fire on every program start, which is not a refusal, it is a
crash. The requirement is discharged the other way round: the registration is
DELETED and every ACCESSOR that would have consumed it panics. There is no
path that reads a descriptor and gets a zero value — it reads a descriptor and
gets a panic. Recorded explicitly because it is the one place the
implementation reads the ruling rather than following it literally.

**Marshal-avoidance is structural, not stubbed.** `Marshal`, `Unmarshal` and
`Size` do not exist in the shim at all — there is no encoder to call. The only
in-tree caller of any of them was `MarshalConfChange`, which is the one
hand-written stub above. Their absence beyond the vendored tree is H-1, and
H-1 is BIGGER than `proto.Size` — see the residue census immediately below.

**The upstream residue, censused (2026-08-19, pre-merge audit).** "H-1 =
`proto.Size`" was too narrow: the DECODE side is at least as load-bearing, and
it sits on a decision path, which `Size` mostly does not. Measured against
`deps/raft` @ `56e3200`, root package, non-test:

| site | call | why it matters |
|---|---|---|
| `raft.go:1314`, `raft.go:1320` | `proto.Unmarshal` into `ConfChange` / `ConfChangeV2` | **DECISION PATH.** `stepLeader`'s `MsgProp` handler decodes each proposed entry to decide whether to ADMIT the conf change or rewrite it to a no-op (`alreadyPending`/`alreadyJoint`/`wantsLeaveJoint`). The decode result steers raft's membership-change safety check; a failure `panic`s. Not rendering, not optional. |
| `bootstrap.go:56` | `proto.Marshal` of a `ConfChange` | `Bootstrap` encodes the initial peer set into `Entry.Data`. An ENCODE on a setup path — avoidable by snapshot-seeding membership (which is what marshal-avoidance assumes), but only if W4 declines `Bootstrap`. |
| `util.go:225`, `util.go:232` | `proto.Unmarshal` in `DescribeEntry` | rendering-internal (§6(a)); decode, but behind a `Describe*`. Lowest rank of the three. |
| `util.go:277`, `:290`, `:292` | `proto.Size` in `entsSize`/`limitSize` | the originally-named residue: flow control sizes entries in WIRE bytes. Normal path, but the value feeds a LIMIT, not a branch on message content. |

**Re-ranked W4 obligation list**, which is the point of the census: (1) the
`stepLeader` decode, because a decision path cannot be papered over with a
seam and no snapshot-seeding trick removes it — the entries arrive as
proposals; (2) `proto.Size`, which needs wire-accurate byte counts derived
from the same field lists + tags the shim already parses, or an explicitly
argued size seam; (3) `bootstrap.go`'s encode, retired for free if W4 seeds
membership by snapshot and declines `Bootstrap` — a scoping decision, not an
implementation; (4) `DescribeEntry`'s decode, which rides on whatever §7/H-6
rules for rendering. Note that (1) and (2) are the same missing artefact seen
from two ends: a wire codec derived from the pinned `.proto` field numbers
would discharge both, which is the argument for building one rather than four
seams.

**The frontend's own fail-closed behaviour was exercised, not assumed.** The
two plain functions that could not lower — `raftpb.ConfChangesFromString` and
`raftpb.ConfChangesToString` (both `strings`/`strconv` helpers) — land on the
wire as `unsupported` entries via the per-decl quarantine, i.e. they refuse
WHEN CALLED. That is the paired control for §6's finding about methods.

**Correction (2026-08-19, pre-merge audit).** An earlier version of the
sentence above justified those two as "called only from `rafttest` upstream".
That justification was WRONG for `ConfChangesToString`: it is called from
`deps/raft/util.go:216`, inside `DescribeEntry`, which is root-package
non-test code. The conclusion survives, but on the OTHER argument — §6(a)'s:
`DescribeEntry` is itself a rendering function, so the call is
rendering-internal and no decision path reaches it. Recorded rather than
quietly repaired, because the two arguments have different reach: "only
`rafttest` calls it" would have survived W4 vendoring the root package, and
the argument that actually holds does not — W4's `Describe*` helpers put a
live in-tree caller in the tree, at which point this stub's refusal becomes
reachable from anything that renders. See the fmt bound below and H-6.

**The fail-closed guarantee is bounded: it covers DIRECT calls.** The 9
`(*T).String` and 4 `E.String` stubs panic, and a direct call therefore
refuses loudly, as intended. But the normal way a `String()` method is invoked
in Go is through `fmt` — and `fmt` does not propagate a Stringer's panic. Its
`catchPanic` recovers it and renders the verb as `%!s(PANIC=String method:
...)`, after which formatting and the program CONTINUE. So a `%s`/`%v` on one
of these types is not a refusal a differential would see as a stop; it is a
funny-looking string. In-tree this is currently unexploitable in the direction
that matters, and that was checked rather than assumed: of the twelve `fmt`
verb sites in the vendored tree's Go code, exactly ONE formats a type carrying
a fail-closed stub — `confchange.go:109`'s `%+v` over a `*ConfChangeV2` (see
§6(a)) — and it is inside a panic ARGUMENT, where the outer `panic` fires
regardless of what the argument rendered to. The other eleven format integers
or `tracker`/`quorum` types whose `String` methods are upstream's real ones. The no-op logger never calls `fmt` at all. It stops being unexploitable at W4: the `Describe*` helpers
RETURN rendered strings, so a recovered panic there becomes a value that flows
onward. This is an INPUT to the H-6 fmt ruling (§7), not a separate item —
whichever of §7's three options is taken must say what `fmt`-mediated
rendering of a fail-closed type does.

---

## §4 The subject-delta ledger (requirement c)

Every divergence of `raftsubject/` from upstream `deps/raft`. Outside the five
files itemised below nothing differs: `quorum/*`, `tracker/*`,
`raftpb/alias.go` and `raftpb/util.go` are upstream text with only the two
import-path rewrites. (Wording tightened 2026-08-19: the old "nothing else
differs" read as a completeness claim over the whole tree including
`raft.pb.go`, whose comment-stripping D-1 had not named. It now does.)

### D-1 `raftpb/raft.pb.go` — the strip (mechanical)
Structs keep their fields, types and protobuf struct tags; the three
`protoimpl` private fields (`state`, `unknownFields`, `sizeCache`) are removed.
`Reset()` keeps its plain-Go half (`*x = T{}`) and loses the message-info
store. Everything else per §3. **Observable weight:** the types no longer
implement `proto.Message`, so nothing outside the shim can marshal, reflect
over, or JSON-decode them. Under marshal-avoidance nothing tries.

**One non-semantic delta the ledger owed and did not name (audit-found,
2026-08-19): the strip drops every TOP-LEVEL doc comment — all 64 of them.**
This is structural, not incidental: `split_decls` treats a column-0 `//` as a
declaration start, so a doc comment becomes its own chunk, and a chunk with no
declaration text is skipped. FIELD-level comments (indented, inside the struct
bodies) are kept — 46 of them survive into the derived file — as are the
protobuf struct tags, so the field-number provenance a reader needs is intact.
The 23 top-level `//` lines in the derived file are all `PLAINPB_HEADER`; zero
upstream ones survive. Weight: NIL semantically — no declaration, type, field,
tag or body changes — but it is a real textual divergence, and a ledger whose
whole job is "every divergence, itemised" owed it a line. It is also why §4's
opening sentence now says "outside the five files itemised below" rather than
"nothing else differs": the verbatim claim is about `quorum/*`, `tracker/*`,
`raftpb/alias.go` and `raftpb/util.go`, and it was never a claim about
`raft.pb.go`, which this section itemises.

### D-2 `raftpb/plain_clone.go` — GENERATED, no upstream counterpart
Plain-Go `CloneMessage()`/`EqualMessage()` per message type (9 each), derived
from the same parsed field lists, standing in for `proto.Clone`/`proto.Equal`
— which raft calls on its NORMAL paths (`log_unstable.go`, `storage.go`,
`log.go`, `raft.go:817`), so marshal-avoidance does not remove them. proto2
presence semantics reproduced deliberately: an optional scalar/bytes field is
set iff its pointer/slice is non-nil and unset ≠ set-to-zero; repeated fields
have no presence, so nil and empty are equal AND an empty repeated field
clones to nil (matching `proto.Clone`, which ranges over populated fields).
Differentially validated — §5. **Authoring note:** the element copies are
written `_ = copy(dst, src)` rather than `copy(dst, src)`. This is OUR code,
not upstream's, so there is no fidelity claim on its syntactic form, and the
expression-position form avoids a self-inflicted instance of the frontier item
at F-6 below. The upstream instance in `tracker/inflights.go` is untouched and
still refuses.

### D-3 `raftpb/confstate.go` — overlay
`proto.Clone`/`proto.Equal` → `CloneMessage`/`EqualMessage` (same operation,
plain Go). The mismatch error's TEXT loses the four `%+#v` value dumps and
becomes a fixed-text sentinel (`ErrConfStateNotEquivalent`,
`ErrConfStateNilInput`), which is what keeps `fmt` out of raftpb. **Observable
weight:** the VERDICT (nil vs non-nil error) is unchanged, and raft's callers
branch on the verdict only — checked by reading every caller. Anything that
logged the dumps loses them; under the no-op logger nothing does. `slices.Sort`
is kept (the one modeled stdlib extern). The algorithm — sort copies, treat
nil `AutoLeave` as false, compare — is upstream's, transcribed.

### D-4 `raftpb/confchange.go` — overlay
ONE change: the `google.golang.org/protobuf/proto` import and with it
`MarshalConfChange`'s body, which becomes a fail-closed panic (§3).
Everything else is upstream verbatim, INCLUDING what the frontend cannot lower
— `EnterJoint`'s `panic(fmt.Sprintf(...))` and the `strings`/`strconv`
rendering helpers stay exactly as etcd writes them, so they classify honestly
in §6 instead of being papered over.

### D-5 `raft/logger.go` — the W2.2 no-op Logger injection
The `Logger` INTERFACE is upstream verbatim (twelve methods, same signatures),
so every raft call site type-checks unchanged. `DefaultLogger` — the
`*log.Logger`-backed implementation, its `EnableDebug`/`EnableTimestamps`
knobs and the `header` helper — is replaced by `noopLogger`: twelve empty
bodies. `fmt`, `io`, `log`, `os` disappear from the file. `defaultLogger` and
`discardLogger` are both the no-op, so `ResetDefaultLogger()` restores the
no-op. `raftLoggerMu sync.Mutex` is KEPT (sync.Mutex is modeled,
`docs/2026-08-09_sync-package-design.md`; `SetLogger`/`getLogger` race under
the concurrent twin, and dropping the mutex would be a concurrency-semantics
delta smuggled in as a convenience).

**The one delta with real observable weight, stated plainly:** `Fatal`/`Fatalf`
no longer call `os.Exit(1)` and `Panic`/`Panicf` no longer panic. Upstream,
those terminate. The argument for accepting it: both are rendering-coupled
aborts — they exist to print a message and die — and raft reaches them only on
states it treats as impossible. Keeping the abort without the message would be
a bare `panic("")`, which a differential could not distinguish from a genuine
panic, so the fail-closed instinct pulls in the wrong direction here.

**And here is the concrete site that makes it a real question, found while
checking D-3.** `raft.go:479` and `raft.go:1936` call
`assertConfStatesEquivalent(r.logger, ...)` (`util.go:320`), whose entire body
is `if err := cs1.Equivalent(cs2); err != nil { l.Panic(err) }`. That is an
ASSERTION — raft's own safety net over configuration restore — and it is
routed through the LOGGER. Under the no-op logger the assertion still computes
its verdict and then throws it away: a ConfState mismatch that upstream would
crash on continues silently. That is a weakening of the subject, in the
direction that hides a defect. It costs nothing today (`raft.go` is not
vendored yet, so the site is not in the tree), but it must be settled before
W4 vendors the root package. This is NOT a settled question; it is handoff
item **H-2**. The likely shape of the answer: `Panic`/`Panicf` panic with a
FIXED string (assertions keep their teeth, the message is what we give up),
while `Fatal` and the six informational levels stay empty — but that is a
ruling to make with the call sites in front of you, not here.

**Scope note.** `raftsubject/raft/` contains logger.go ONLY. The rest of
package `raft` (raft.go, log.go, storage.go, node.go, rawnode.go, util.go)
arrives with W4's stage-wise lowering. The package compiles and lowers as it
stands, which is what makes the injection checkable now rather than at W4.

> **RETIRED 2026-08-21 (W4.2 item 1, executing the 2026-08-20 Q2 ruling —
> `docs/raft-w3-log.md` §5, harness design §5).** The no-op overlay is
> DELETED; `logger.go` is vendored VERBATIM and the HARNESS supplies the
> `Logger` through BOTH seams (`raft.SetLogger` + `Config.Logger`). H-2's
> weakening — `Panic`/`Panicf`/`Fatal` doing nothing — is gone with it:
> the harness logger's four abort methods genuinely panic, so
> `assertConfStatesEquivalent` keeps its teeth. The surviving delta is
> D-12 (three code lines: the two package-level initializers and the
> orphaned `io` import), recorded in `docs/raft-w42-log.md`'s ledger
> continuation with the re-measured numbers and the dead-DYNAMICALLY
> census argument the swap re-owed.

### D-6 import paths
`go.etcd.io/raft/v3/{quorum,raftpb}` → `{quorum,raftpb}`, two occurrences,
both in `tracker/tracker.go`. Per `docs/2026-08-18_multipackage-identity.md`
§4: path == name is what makes rendering exact and lets ONE tree feed both the
machine and the `go run` oracle.

---

## §5 Differential obligations, discharged (requirement d)

`tools/raftsubject/difftest.py` builds a throwaway Go module that links BOTH
the upstream raftpb (with the real protobuf runtime, from `deps/raft`) and the
derived plainpb, converts values between them field by field — with converters
GENERATED from the same struct field lists `derive.py` parses, so the probe
cannot drift from the shim it probes — and runs the battery under `go run`.

Result, 2026-08-19:

```
ok  Equivalent          169 ordered pairs over 13 ConfStates
ok  Equal               611 ordered pairs across 5 message types
ok  Clone               51 values across 5 message types
ok  Clone deep-copy     nested bytes, *uint64 and []uint64 all unaliased
ok  Equivalent purity   inputs unsorted and AutoLeave still unset after the call
ok  Clone nil-ness      0 Go-level nil/empty divergence(s) recorded
PASS plainpb agrees with upstream raftpb on every probed value
```

Battery shapes, chosen to cover every field kind the type set admits: unset vs
set-to-zero optional scalars and enums; nil vs empty vs non-empty repeated
scalars, repeated messages and bytes; nil vs non-nil nested messages;
recursive message lists (`Message.Responses`); permuted and duplicated voter
sets; joint configurations; `AutoLeave` unset/false/true.

**Two methodological points worth keeping.** First, the Clone verdict is taken
with UPSTREAM's own `proto.Equal` over the two clones, so the shim's equality
never judges the shim's clone. Second, section 6 of the battery exists because
`proto.Equal` is BLIND to nil-vs-empty on a repeated field: it compares the Go
nil-ness of the two clones directly. That section found a real divergence on
first run — `CloneMessage` preserved an empty-non-nil repeated slice where
`proto.Clone` normalises it to nil (3 instances). The generator was corrected
(`len(x.F) > 0` for repeated fields; `x.F != nil` retained for `[]byte`, which
in proto2 DOES carry presence), and the section is now a standing check at 0.
Had the battery stopped at `proto.Equal`, the divergence would have shipped
invisible.

**End-to-end, both oracles.** The subject tree plus a harness-shaped probe
main (`tools/raftsubject/probe-main.go`) runs on the machine and under
`go run`, agreeing exactly:

| | `go run` (GOPATH oracle) | machine (`golean native-json-run`) |
|---|---|---|
| `probeTracker` | 7 | 7 |
| `probeCommitted` (real `quorum.MajorityConfig.CommittedIndex`) | 5 | 5 |
| `probeConfState` (plainpb `ConfState.Equivalent` over permuted voters) | 1 | 1 |

`probeConfState` is the one that matters: it drives `CloneMessage`,
`slices.Sort` and `EqualMessage` through the actual interpreter and gets the
right answer. The plainpb real-logic path is therefore validated twice over —
against upstream raftpb under `go run`, and against the machine.

---

## §6 The quarantine sweep and the NEW refusal inventory

**The question W2.2 asks:** with plainpb and the no-op logger in place, are the
rendering paths (W1 rows 1–4, 6) quarantine-dead under harness-shaped entry
points? **Measured, and the answer is two-part.**

**(a) Runtime-dead: YES, with one named exception that does not change the
verdict.** Almost every `String()`/`Describe()` call site in raft's non-test
code sits inside another rendering function — `util.go`'s `Describe*` helpers,
or the `String` methods themselves — and nothing on a decision path calls them.

**The exception, audit-found 2026-08-19, because the claim was written
categorically and is not:** `raftpb/confchange.go:109`, inside
`(*ConfChangeV2).EnterJoint`, is `panic(fmt.Sprintf("unknown transition: %+v",
c))`. That `%+v` over `c` — a `*ConfChangeV2` — REACHES `(*ConfChangeV2).String`,
one of the 9 fail-closed stubs, and it is not inside a rendering function:
`EnterJoint` is semantic. So a `String` stub is reachable from a non-rendering
path after all. Why the verdict survives anyway, on the merits rather than by
narrowing: the site is raft's own defensive-unreachable default over a closed
enum (`ConfChangeTransitionAuto`/`JointImplicit`/`JointExplicit` are exhaustive
for a well-formed value), it is inside a `panic` ARGUMENT, and per §3's fmt
bound the recovered Stringer panic only degrades the message — **the outer
`panic` still fires**, so the program still stops, which is the behaviour the
fail-closed register is actually promising. It is F-5 in the inventory below
and one of the two sites §7's fmt ruling exists to settle; it is NOT a
quarantine-deadness counterexample, but the earlier "every call site sits
inside another rendering function" was simply false and is withdrawn.

(The other apparent exception, `state_trace.go`, is behind
`//go:build with_tla`; the default build takes `state_trace_nop.go`, whose
`traceChangeConfEvent` is an empty body. It becomes live only if the subject
is ever vendored with that tag, which would be a recorded decision.)

With the no-op logger, the `%s` verbs
in `logger.Infof(...)` never run, so the `String()` methods behind them are
never invoked — Go evaluates the argument (a field read) but only `fmt` calls
`String`, and `fmt` is never reached. The injection does what W2.2 wanted.

**(b) Export-dead: NO — and this is the finding.** The frontend lowers every
declaration in a package, not the reachable ones, and **methods have no
per-decl quarantine**: an unsupported method fails the WHOLE export
(`tools/nativefrontend/mono.go:489`, and the D2 contract at
`tools/nativefrontend/emit.go:537`). Plain functions DO quarantine. So the
rendering methods block the export regardless of being runtime-dead, while the
two unsupported plain functions in the same package export cleanly as
refuse-when-called stubs. That contrast is the measurement, not a reading of
the comments: §3's `ConfChangesFromString`/`ToString` are on the wire as
`unsupported`; every method below had to be neutralised for the walk to
continue.

### The instrument

`tools/raftsubject/frontier.py` walks the frontier: run the frontend, record
the refusal, replace ONE declaration's BODY with a panic, run again. Body
replacement rather than deletion is deliberate — deleting a method changes the
package's type-check and the next thing you see is a cascade of your own
removal, which is exactly what W1's row 2 (`c[0].String undefined`) was. Each
step is driven from a tracked plan (`tools/raftsubject/frontier-plan.tsv`) and
checked against its recorded expectation, so the walk reproduces or refutes.

**The instrument's own gate, hardened 2026-08-19 (pre-merge audit).** The walk
checked each row's predicted refusal against the frontend's actual one, but
its exit code said nothing about the state it STOPPED in — so a plan truncated
to its first few rows walked them, matched them all, printed a live refusal in
its `final:` line, and **exited 0**. The auditor demonstrated exactly that,
and it is the failure mode that matters here: this instrument's output is the
inventory in this section, so an under-complete plan does not report an error,
it reports a SHORTER FRONTIER — a claim about raft that is simply false, made
by a green run. Two changes, both re-demonstrated:

- the plan now ends with a **terminal `*` row** asserting `(exports clean)` —
  documented in the docstring before, present in the file now — and
  `frontier.py` REFUSES a plan lacking it, because a walk with no terminal
  assertion is a list of steps, not a measurement of a frontier;
- the final state is folded into the **exit code**, so completeness is checked
  even if the terminal row is present but premature.

Demonstrated on both truncation shapes: a 3-row plan with the terminal row
dropped is refused (`EXIT=1`), and a 3-row plan that keeps the terminal row —
i.e. one that falsely CLAIMS completeness — fails it as a MISMATCH and then
fails the final check (`EXIT=1`). The same 3-row plan against the pre-fix
instrument still exits 0, which is the before/after pair. Full plan: 10 rows +
terminal, all `ok`, `final: EXPORTS CLEAN`, `EXIT=0` — so the inventory below
is unchanged by the hardening; it is now load-bearing rather than advisory.

### The inventory (2026-08-19, `deps/raft` @ 56e3200, full derived tree)

| # | refusal (verbatim) | site | class |
|---|---|---|---|
| F-1 | `selector call Fprintf is not a method value` | `quorum/majority.go` `MajorityConfig.String` | rendering; runtime-dead, export-blocking |
| F-2 | `slices.SortFunc (only slices.Sort at integer elements is modeled)` | `quorum/majority.go` `MajorityConfig.Describe` | **NEW** — extern/language gap, master plan §W1.2 |
| F-3 | `selector call FormatUint is not a method value` | `quorum/quorum.go` `Index.String` | rendering; runtime-dead, export-blocking |
| F-4 | `selector call FormatInt is not a method value` | `quorum/voteresult_string.go` `VoteResult.String` | rendering (generated stringer); ditto |
| F-5 | `selector call Sprintf is not a method value` | `raftpb/confchange.go` `ConfChangeV2.EnterJoint` | **NEW** — semantic-path fmt (panic message); needs-design |
| F-6 | `builtin copy in statement position` | `tracker/inflights.go:93` `Inflights.grow` | language gap; cross-ref'd, do not fix here |
| F-7 | `selector call Sprintf is not a method value` | `tracker/progress.go:183` `Progress.SentEntries` | semantic-path fmt (panic message); needs-design |
| F-8 | `selector call Fprintf is not a method value` | `tracker/progress.go` `Progress.String` | rendering; runtime-dead, export-blocking |
| F-9 | `selector call Fprintf is not a method value` | `tracker/progress.go` `ProgressMap.String` | rendering; ditto |
| F-10 | `selector call Fprintf is not a method value` | `tracker/tracker.go` `Config.String` | rendering; ditto |

Quarantined rather than blocking (on the wire as `unsupported`, refusing when
called): `raftpb.ConfChangesFromString`, `raftpb.ConfChangesToString`.

With those ten neutralised the tree **exports clean**: 20 funcs, 206 methods,
34 types, 14 globals, 31 method-set records; `sync.Mutex` present (the no-op
logger's mutex lowers).

### Classification, as the brief asks

- **dead-under-harness, export-blocked (F-1, F-3, F-4, F-8, F-9, F-10)** —
  six rendering methods. Runtime-dead (a); export-blocking (b). The clean fix
  is a FRONTEND change — extend the per-decl quarantine to methods — which
  this lane must not make. Until then the only alternative is a recorded
  subject delta stubbing them, which we have deliberately NOT taken: the tree
  keeps upstream's text and stays honestly red. Handoff **H-3**.
- **language-gap, cross-ref'd (F-6)** — statement-position `copy`. Frontend
  site `tools/nativefrontend/emit.go:1767`; recorded class since the
  goose-parity buildout (`docs/goose-parity-buildout-log.md`, `semantics/copy`
  and `unittest/copy`); language-wide expression-position coverage exists at
  `spec-examples-decl/copy-forms` (`docs/spec-archaeology/spec-examples-dispositions.tsv`
  row `Appending_and_copying_slices-4-820d26f7`), so this is the
  statement-position residue. It belongs in the bug-fix arc's slice-6
  frontier ledger (`docs/2026-08-19_bugfix-arc-charter.md`), which asks for
  exactly this shape of row — refusal point with file:line and error string,
  plus a raft-path priority mark. Handoff **H-4**. NOT fixed here.
- **extern gap (F-2)** — `slices.SortFunc`, frontend site
  `tools/nativefrontend/emit.go:1780`. Already a named work item (master plan
  §W1.2: "shim or extern extension — decide by fidelity argument; shim
  preferred, it needs no GoCore change"). NEW to the inventory because W1's
  probe omitted `Describe` entirely, so its body was never lowered. Handoff
  **H-5**.
- **needs-design (F-5, F-7)** — `panic(fmt.Sprintf(...))` on a semantic path.
  Deliberately NOT improvised here; scoped as a design question in §7.

### Diff against W1's inventory

| W1 row | fate |
|---|---|
| 1 `Fprintf` (rendering, several sites) | splits into F-1, F-8, F-9, F-10 — one row per declaration, each independently confirmed |
| 2 `c[0].String undefined` | **GONE — it was not a frontier item.** It was a cascade of W1's probe omitting the methods; under body replacement `quorum/joint.go`'s `String`/`Describe` lower fine (they only call other methods) |
| 3 `FormatUint` | F-3, unchanged |
| 4 `FormatInt` | F-4, unchanged |
| 5 `copy` in statement position | F-6, unchanged |
| 6 `Sprintf` (progress.go) | F-7, unchanged; and F-5 joins it — the same class inside raftpb itself, invisible to W1 because raftpb was a 5-field ConfState stand-in |
| — | F-2 `slices.SortFunc` is new (W1 omitted `Describe`) |

Net: W1's 6 rows over 2 packages → 10 rows over 3 packages, one W1 row
retired as a probe artifact, two genuinely new. The count going UP while the
tree grew from a hand-made ConfState stand-in to the real raftpb is the
expected direction; the retirement of row 2 is the instrument improving.

---

## §7 The fmt story — scoped as a design question for W2.3, not improvised

F-5 and F-7 are the same shape: `panic(fmt.Sprintf("...%s...", x))` on a path
raft treats as unreachable but which is NOT rendering — it is the message of a
panic that the machine must be able to take. The no-op logger does not touch
them, and quarantining them is wrong twice over (they are methods, so there is
no per-decl quarantine; and quarantining would make an assertion path silently
unlowerable rather than visibly refusing).

Scoping §7 measured three non-logger `fmt.Sprintf` sites in `raft.go` itself,
so the class grows when W4 vendors the root package. The options, stated so
W2.3 can rule rather than drift into one:

1. **A modeled `fmt` subset** — `Sprintf` over a closed verb set at known
   argument kinds, as a frontend shim with a fidelity argument, in the shape
   of the `strings.Fields` shim (E5, `tools/nativefrontend/stdlibshim.go`).
   Widest reach, largest fidelity surface, and a frontend change.
2. **A panic-message seam** — the machine's panic value need not be the
   rendered string if nothing observes it. Requires arguing that no corpus
   case or theorem statement reads a panic message, which is a real claim
   about the observation vocabulary, not a shrug.
3. **A recorded subject delta per site** — flatten each panic message to a
   constant (what W1's probe did, marked `[probe delta]`). Cheapest, honest,
   and a delta count that grows with the subject, which is exactly the kind of
   erosion the verbatim discipline exists to prevent.

This lane records the options and the measurement; the ruling is W2.3's.
**Do not treat option 3 as the default just because the probe used it.**

---

## §8 Handoff items

| id | item | owner |
|---|---|---|
| H-1 | **The protobuf residue in the root package — DECODE first, then `Size`.** Ranked in §3's census: (1) `proto.Unmarshal` at `raft.go:1314`/`:1320`, `stepLeader`'s `MsgProp` conf-change admission — a DECISION path, unavoidable by seeding; (2) `proto.Size` in `entsSize`/`limitSize` (`util.go:277`/`:290`/`:292`), flow control's wire-byte limit; (3) `proto.Marshal` at `bootstrap.go:56`, retired for free if W4 declines `Bootstrap`; (4) `proto.Unmarshal` in `DescribeEntry` (`util.go:225`/`:232`), rendering-internal. (1) and (2) are one artefact from two ends: a wire codec derived from the pinned field numbers + tags discharges both. Not reached by the packages vendored so far. Scoping §7 layer C named the `Size` half; this is the whole ticket. (Widened 2026-08-19 — the pre-merge audit found the decode side, which the original H-1 missed entirely.) | W4 (head of its obligation list) |
| H-2 | **The no-op logger's `Fatal`/`Panic` do not abort** (D-5), which SILENCES raft's own assertions: `assertConfStatesEquivalent` (`util.go:320`, called from `raft.go:479`/`:1936`) routes a failed ConfState-equivalence assertion through `Logger.Panic`. Must be settled BEFORE W4 vendors the root package; candidate answer is "Panic/Panicf panic with a fixed string, the rest stay empty". | W4 / W2.3 — blocking for W4 |
| H-3 | **Methods have no per-decl quarantine** (`mono.go:489`), so six runtime-dead rendering methods block the whole export. Extending the quarantine to methods — signature-carrying stubs that refuse when called, the same contract plain functions already get — would unblock the subject tree with no subject delta at all. Frontend change; this lane must not make it. | W1 / frontend lane |
| H-4 | **`copy` in statement position** (F-6, `emit.go:1767`) → the bug-fix arc's slice-6 language-coverage ledger as a `frontier` row with a raft-path priority mark. | bug-fix arc |
| H-5 | **`slices.SortFunc`** (F-2, `emit.go:1780`) — master plan §W1.2, shim preferred. Now has a concrete raft call site (`MajorityConfig.Describe`). | W1 |
| H-6 | **The fmt story** (§7) — three options scoped, ruling owed. | W2.3 |
| H-7 | **covmap for the subject↔upstream delta ledger.** W1's §CROSS-READ item 4 records `deps/covmap` (`docs/2026-08-17_covmap-pilot.md`) as the candidate mechanism for tracking this delta. This lane used SHA-256 digest pins + a fail-closed rule table instead, which is cheaper and needs no new dependency, but does NOT give the per-line delta view covmap would. Worth a look before the tree grows to raft.go. | W2.3 / W4 |
| H-8 | **`raftsubject/` is not in any gate.** `derive.py --check`, `difftest.py` and `frontier.py` all reproduce their claims on demand but nothing runs them. When the tree stops moving, a cheap gate step (`derive.py --check` at least) would keep the "the tree IS the derivation" claim honest. `scripts/` is off-limits to this lane. | operator / a scripts-owning lane |

---

## §9 Judgement calls

- **JC-1: the subject tree is a top-level `raftsubject/`, not a corpus case.**
  It is a source of truth that W4 will COPY into corpus cases; keeping it out
  of `Corpus/` keeps this lane off the serialized resource entirely, exactly
  as the ownership split requires.
- **JC-2: the whole tree is derived, not just raftpb.** The ruling asks for a
  derivation script for the shim. Making the verbatim vendoring and the
  overlays run through the same script was nearly free and buys one property
  worth having: `--check` can assert that the ENTIRE tree is the derivation's
  output, so no file can be hand-edited without the check going red.
- **JC-3: upstream's unlowerable text is kept, not stubbed.** Every rendering
  method, the statement-position `copy`, and both `panic(fmt.Sprintf(...))`
  sites stay exactly as etcd writes them. This costs a red export today and
  is the reason §6 has ten rows instead of zero. The alternative — stubbing
  them as subject deltas — would buy a green export by growing the delta
  ledger, which is precisely the erosion the verbatim discipline exists to
  prevent (scoping §7 Blocker 1's argument, applied to text rather than to
  packages).
- **JC-4: `_ = copy(...)` in the GENERATED clone file.** Our code, no fidelity
  claim on its syntactic form, and using the supported expression position
  keeps a self-inflicted red out of the inventory so F-6 reads as the one
  upstream instance it is. Recorded in D-2 rather than left silent.
- **JC-5: `CloneMessage` normalises empty repeated fields to nil.** Chosen to
  match `proto.Clone` exactly after the differential found the divergence,
  rather than keeping the "obvious" `!= nil` form and recording a delta. A
  delta we can eliminate is not a delta worth recording.
- **JC-6: the frontier walk replaces bodies instead of deleting declarations.**
  Retired one row from W1's inventory (row 2 was a cascade of the probe's own
  omission). Any future walk should keep this property.
