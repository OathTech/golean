# Landing chunk L3 — `land/panic-text-tape`: the abort-line renderer redone per doctrine (strict UTF-8 fix, the `repanicCollapse` choice site, fail-closed invalid bytes)

[AGENT] landing worker, lane `land-panic-text`, 2026-09-07. Source of the
reworked material: branch `typed-consumer-sprint` at `7edc298f` (archive:
`docs/ARCHIVE.md`), REDONE on main `90bc3e06` per
`docs/2026-09-07_typed-sprint-landing-plan.md` §2.3 (L3) and §4 (D2, D5).
Squashed into ONE landing commit; the authored sprint history is on the
branch. Sections §1–§3 were written BEFORE the code (the brief's order);
§4 onward records what was built and measured.

Ruling context ([USER] Mike, 2026-09-07, relayed by the [AGENT]
coordinator in the landing brief — cite as relayed): land the sprint in
reviewable chunks; «where appropriate fix some of the issues, eg. the
choice tape stuff». Doctrine applied (CLAUDE.md): no semantic choice hides
in evaluator recursion — latitude is reified on the choice tape; fail
closed BY NAME where the model cannot render; gc-visible texts are
observations and are byte-exact when deterministic. The panic-text
latitude precedent this chunk EXTENDS is BUG-087's ruling «(2) panic-text,
agree, demonic choice so both are admitted» ([USER] 2026-09-03, relayed —
`docs/2026-08-31_qrow-rulings.md`) — whose scope is ONE demonic choice at
the nil arm (`nilValueMethodText`/R9a; it does not cover the `[recovered,
repanicked]` marker): this chunk applies the ruling's SHAPE (a demonic
choice where gc's realization is toolchain-internal) to that marker under
R-1's re-envelope authority (`docs/2026-08-20_w32-re-envelope-charter.md`:
the rendered TEXT is spec-silent latitude quotiented via membership; the
payload's KIND and the control flow stay forced and exact). That extension
is the [AGENT]'s; [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off)
(adversarial audit R2 — §7 below; the wording "under BUG-087's ruling" in
earlier drafts of these records overclaimed and is relabelled everywhere).

Inputs read in full: `CLAUDE.md`, `AGENTS.md`, the essence-of-Go doctrine,
the landing plan (§2.3, §4, Appendix B), both landing audits (A-R1–R4,
B-R3/R13/R14), the R-1 ruling, BUGS.md BUG-004 / BUG-087, the `ChoiceSite`
census (`GoLean/GoCore/State.lean`), the L1 landing note §4–§5 and its
deferred list, `deps/go/src/runtime/{panic.go,error.go,iface.go}` and
`cmd/compile/internal/walk/convert.go` at the pin.

## 1. gc at the pin (`deps/go` @ `c19862e5f8` = go1.26.5), read and witnessed

Every cite below is a line in `deps/go/src/runtime/` at the pin; every
behaviour claim has a witness program in
`docs/evidence/2026-09-07_land-panic-text-tape/witness/` (38 programs — w01–w37 plus w06b,
byte-exact stderr recorded in `table.tsv`; `go version go1.26.5
linux/amd64`, `GODEBUG=panicnil=0` as the differential oracle sets it).

### 1.1 When `[recovered]` / `[recovered, repanicked]` print (panic.go)

- `preprintpanics` (702–730) walks the chain from the NEWEST panic. For
  each `p` with `p.link != nil`: **`*efaceOf(&p.link.arg) ==
  *efaceOf(&p.arg)` (715)** — a bitwise compare of the interface's type
  word AND data word — marks the OLDER entry `p.link.repanicked = true`
  (718) and skips the newer one's rewrite. Otherwise (723–728) an `error`
  payload is REWRITTEN to `v.Error()` and a `stringer` to `v.String()`
  (BUG-004 item 4, unchanged here).
- `printpanics` (734–755) recurses into `p.link` first (735–736) — the
  OLDEST panic prints first, so the differential's first line is the
  oldest entry. **`if p.link.repanicked { return }` (737–739)** suppresses
  the newer duplicate line entirely; every non-first line is TAB-prefixed
  unless the link is a `goexit` (740–742). Each line is `panic: ` +
  `printpanicval(p.arg)` (747–748) + **` [recovered, repanicked]` iff
  `p.recovered && p.repanicked` (749–750), else ` [recovered]` iff
  `p.recovered` (751–752)**, then `\n`.
- `printPreFatalDeferPanic` (1259–1276) applies the same identity marking
  on the fatal-during-defer path, without the `Error()`/`String()`
  rewrite (BUG-106's shape; L4's territory).
- `gorecover` (1068–1150) sets `p.recovered = true` (1149) on the NEWEST
  panic only; the chain entry's `recovered` flag is exactly the machine's
  `PanicEntry.recovered`.

Archaeology: the collapse is NEW in go1.25 — CL 645916 (`478ad013f9`,
2025-01-31, "runtime: don't duplicate reraised panic values in
printpanics", Fixes #71517: output changed FROM `panic: PANIC [recovered]
⏎ ⇥panic: PANIC` TO `panic: PANIC [recovered, reraised]`), renamed
`repanicked` by `d365f2266d` (2025-05-05). Every go ≤ 1.24 prints the
two-line ` [recovered]` form for EVERY same-value re-panic, including
`panic(r)`. Both renderings are therefore realizations of conforming Go
toolchains; the spec fixes neither (R-1: «the spec defines none of these
strings»).

What decides the eface identity at the pin (witnessed; `-N -l` variants
agree where run — `table-Nl.tsv`):

| shape | eface bits | gc first line | witness |
|---|---|---|---|
| `panic(r)` / `panic(recover())` — the recovered interface value passed through | identical (bit copy) | ` [recovered, repanicked]` — FORCED | w01, w02, w19 (`runtime.Error`), w20 (`panic(r.(error))` — iface→eface keeps the data word), w22 (`panic(nil)` → `*PanicNilError`), w27 (`Code(7)`), w34 (multi-line), w36 (invalid bytes) |
| re-boxing at runtime: `panic(r.(string))`, a runtime-computed string, a package-level `var`, `panic(r.(int))`, `panic(r.(Code))` | fresh `convTstring`/`convT64` allocation (iface.go 419–427: `mallocgc` unless `val == ""`; the empty string uses `zeroVal`, which is NOT the literal's static box) | ` [recovered]` + a second line — FORCED-DISTINCT | w03, w05, w30, w06 (empty), w09 (`7`), w10 (`1000`), w28, w33 |
| two independent CONSTANT literals of the same value (`panic("orig")` twice; `s := "orig"; panic(s)` constant-propagated) | the compiler emits a read-only static box per site (`walk/convert.go` `dataWord` 183–186, "n is a readonly global; use it directly") and the LINKER dedups content-identical read-only symbols | ` [recovered, repanicked]` at the pin — LAYOUT-DEPENDENT (a toolchain property, not a language one) | w04, w06b, w11, w26, w29 |
| bools / single-byte values | `staticuint64s` at EVERY site (`dataWord` 161–177) | ` [recovered, repanicked]` — forced at the pin | w08 |
| two runtime FAULTS of the same kind | nil-deref: the shared package var `memoryError` → collapse; index-out-of-range: a fresh `boundsError` per fault → distinct | w31 collapses, w32 does not |

The consequence the brief asked to decide (its hard stop): **the marker is
deterministic in eface identity, and the machine does not have the bits.**
Implementing it exactly would mean modelling gc's boxing: which
conversions allocate, the static read-only box per literal site, the
linker's content dedup, `staticuint64s`, `zeroVal`, the runtime's shared
error singletons — a gc-specific allocation/layout model that (i) the
spec says nothing about, (ii) changes across toolchains (go ≤ 1.24 prints
the other member for every shape), (iii) is exactly the address-exposing
representation register #6 of the doctrine forbids the observation surface
to depend on, and (iv) is not cheap: it is an identity on every
`.interface` value, threaded through every conversion and copy. Relative
to the machine's value-level state the marker is LATITUDE; both members
are gc-realized at the pin on the string, int, defined-int and
`runtime.Error` families (rows in §3). So: a site, not an
implementation — and this note says so explicitly.

### 1.2 How gc prints string payloads (error.go)

- `printpanicval` (215–256): `string` → `printindented(v)` (251–252);
  `nil` → `nil`; bool/ints/floats → `print`; anything else →
  `printanycustomtype` (259–304: a defined string type prints
  `T("…")` through `printindented`, a defined int `main.Code(7)`).
- `printindented` (306–318) writes the payload's RAW BYTES, inserting a
  `\t` after every `\n` (`print(s[:i]); print("\t")`), then the tail.
  The suffix (`[recovered…]`) follows the WHOLE payload (panic.go 748–752),
  i.e. it lands on the payload's LAST line. Hence the first abort line
  of a multi-line payload is the bytes BEFORE its first LF, with NO
  suffix: `panic("first\nsecond")` recovered then `panic("other")` →
  `panic: first⏎⇥second [recovered]⏎⇥panic: other` (w14, first line
  `first`); `panic("first\n")` → `panic: first⏎⇥⏎` (w15, first line
  `first`). Valid non-ASCII UTF-8 is written verbatim (w12: `a é 界 😀
  z` = `61 c3a9 e7958c f09f9880 7a`).

### 1.3 What gc prints for invalid UTF-8

Raw bytes, no escaping, no replacement: `panic("\xff")` → `panic: ff ⏎`
(w37); `panic("\xffZ\nY")` → first line `ff 5a` (w35); `panic("a\n\xff")`
→ first line `61` (`a`) — the invalid byte is on the SECOND line (w16);
the recovered pass-through of `"\xffZ"` → `ff 5a 20 [recovered,
repanicked]` (w36). No `"\xHH"` form is ever printed — the sprint's
`escapeAllBytes` member (A-R3, B-R3) is a rendering no Go toolchain
produces.

## 2. Design (decided before code)

### 2.1 (a) Valid-UTF-8 first-line rendering — a strict-lane FIX (gc-verified)

The sprint's `ff7173dd` widening (credited) is kept in substance and
sharpened in one place:

- `asciiString?` is DELETED. `utf8String? : Array UInt8 → Option String`
  is the strict constructive decoder over `decodeRuneAt` (the same total
  decoder string range/conversion use; U+FFFD-with-width-1 is its invalid
  sentinel, a correctly encoded U+FFFD has width 3 and is kept) AND a
  byte round-trip check `text.toUTF8.data == bytes` INSIDE the function —
  so `utf8String? bytes = some text → text.toUTF8.data = bytes` is a
  theorem by construction (`utf8String?_bytes`), not a trust in the
  custom decoder (the sprint checked the round trip in the escape
  renderer; here it is the decoder's own contract).
- The first-line projection is BYTE-level and comes FIRST, mirroring
  `printindented`: `stringFirstLine? bytes = (utf8String? (bytes.takeWhile
  (· ≠ 0x0A)), hasLF)`. The suffix is appended ONLY when the payload has
  no LF (gc puts it on the last line). Consequence, deliberately: a
  payload whose FIRST LINE is valid UTF-8 renders byte-exactly even if a
  later line is not (`a\n\xff` → `a`, w16) — the observation compared IS
  the first line, and its bytes are gc's bytes; nothing about the unseen
  tail is claimed. [Audit fix round R4, [AGENT]: this silently EXTENDED the
  unwinding arc's first-line-only contract — stated there for deeper CHAIN
  entries — to a single payload's CONTINUATION lines. It is now a dated
  rule in `docs/2026-07-25_unwinding-arc.md` §A3, MEASURED rather than
  asserted (`docs/evidence/2026-09-07_land-panic-text-tape/first-line-scope.txt`:
  `panic("head\nTAILA")` ≡ `panic("head\nTAILB")` byte-identically on both
  sides), with the honest consequence that the tail is unmodelled
  (`renderPanicPayload` returns `(firstLine, multilineFlag)`) and
  unobserved; the widening is rowed as ledger FR-32, pointed at L4's
  byte-view machinery. `panic-text/invalid-after-lf` is accordingly a
  first-line-SCOPE control, not invalid-UTF-8 coverage — retagged
  `first_line_scope` (R4d).] The String-level `PanicText.firstLine` is kept (an
  L1-landed constructive helper the interface audit pins) but the
  renderer no longer needs it.
- The `runtime.Error` arm decodes through the same `stringFirstLine?`.

Strict-lane witnesses: the nine `panic-recover/panic-text/*` rows (w12–w15
shapes) and `panic-recover/panic-newline-abort` (FAIL→PASS), all compared
against gc's actual first line by the unchanged strict comparator.

### 2.2 (b) The `[recovered, repanicked]` marker — `ChoiceSite.repanicCollapse`

- **Name / shape:** `ChoiceSite.repanicCollapse`. Width
  `repanicCollapseWidth first rest = 2` exactly when the abort's HEAD
  entry is recovered AND its successor carries an equal payload
  (`first.recovered ∧ rest = e :: _ ∧ e.value == first.value` — any
  payload family; BEq on `GoValue`), else 1. The predicate is on the
  chain SHAPE alone, not on renderability: a chain the renderer then
  refuses still consults (and the refusal is the same under either pick).
- **Members:** slot 0 = ` [recovered, repanicked]` (the COLLAPSE — the
  member the corpus pinned at `repanic-same-value-abort` and gc's forced
  point for `panic(r)`); slot 1 = ` [recovered]` (the two-line form; gc's
  forced point for a re-boxed value and every go ≤ 1.24's only form).
  Unequal adjacent payloads cannot share a box, so ` [recovered]` stays
  FORCED there (width 1, no pop) — unchanged from main. A head that is
  not recovered renders `base` alone (gc's line for the oldest entry
  carries no suffix whether or not a later duplicate is suppressed — w25).
- **Consumption point:** THE ABORT — the only transition that observes
  the marker (`stepFn`'s `.panicking (first :: rest) .stop` arm and the
  pool's `stepThread` tombstone arm), through one shared consult FUNCTION
  `abortConsult first rest ch := Choices.consumeAt .repanicCollapse
  (repanicCollapseWidth first rest) ch`, called from exactly those two
  arms (L6: "ONE shared consult" overstated — two call sites, one
  definition), under the G-U uniform rule (pop
  iff bound ≥ 2). Drawing at the re-raise would need a `repanicked` field
  on `PanicEntry` (gc's own data structure) and would pop on re-panics that
  are later recovered and never print — a dead pick on every stream; the
  abort draw is observable exactly when it exists. The sequential driver
  drops the popped stream (the machine stops; `abortLeftover` exposes it
  for enumerators); the pool returns it and RECORDS the pick in the
  abort `StepEvent` (`Choices.consumeAtE`, so the L1 observer
  `stepAbortRecord?` re-derives the rendered member from the event's
  own pick — provenance stays exact).
- **Rendering:** `renderPanicHead state first rest (pick : Nat)`; the
  old unconditional `none` at equal payloads is REPLACED by the two
  members; the sprint's unconditional string ` [recovered]` (A-R2) never
  lands. `abortMsg state first rest pick : Except Stop String`.
- **Uniform across families (decided, with the reason):** the site fires
  for every payload family the renderer covers (string, `runtime.Error`,
  nil, int, bool, defined int). gc's draw is forced to slot 0 at the pin
  for bools (`staticuint64s`) and never draws slot 1 there; slot 1 is
  still a CONFORMING rendering (go ≤ 1.24 prints it for that exact
  program), so admitting it is the weakest machine, not an over-widening;
  narrowing bools to width 1 would encode gc's `staticuint64s` layout —
  a (b)-pin. Recorded per family in the inventory entry (R10a) with the
  witness per member; the membership rows' `members=2` pins are honest
  about which member gc exhibited.
- **LOCKSTEP mirrors** (the CLI.lean inventory's standing obligation,
  the `unseqPanic` precedent of lane e13-b): the constructor and its
  `canonicalSlot0` row (State.lean); the projection arms
  `seqConsumption` (Machine.lean) and `poolConsumption` (Multi.lean) —
  hence `CLI.stepNeedsSeq`/`stepNeeds` for free; inventory row 9 in
  CLI.lean; `ChoiceTrace.siteName`/`allSites`/`seqFacts` (a
  `repanicCollapseFacts` validator recomputing the width from the chain);
  `EnumDedup.refusalReason` (fail closed by name — the dedup checker's
  certified fragment excludes the site; the default enumerator carries
  the rows); the flag `consumesRepanicCollapse`, added to
  `stepFn_oblivious`/`seqConsumption_none_of_flags` (a seventh
  hypothesis), `poolThreadOblivious` (an abort is oblivious iff width
  ≤ 1) and `innerVecs` (already `none` at an abort); the nondeterminism
  doctrine's site list; the latitude inventory's census table.
- **Relation shape:** the sequential relation has no abort rule (B4 —
  the abort is the driver's terminal, not a configuration step), so
  `Step`/`stepFn_sound`/`step_complete` are unchanged in statement; the
  POOL relation's `StepM.abort` (Multi.lean) and NPDRF's
  `StepMFine.abort` quantify the pick with a total premise `pick <
  repanicCollapseWidth first rest` and `abortMsg m.shared first rest pick
  = .ok msg`; `stepMulti_sound` discharges it from
  `Choices.consumeAt_fst_lt`, `stepM_complete` realizes it with the
  singleton stream `[pick]` (`consumeAt_fst_singleton`). `stepFn_abort`,
  `stepMulti_abort_single`, `execProg_single_eq_execStmt`'s abort case,
  `RecoverySingleton.singleton_abort_step`,
  `RecoveryPool.stepFn_success_no_abort`/`singleton_abort_driver` are
  restated with the consult; the consumption theorems'
  `fun_cases` tags are untouched because the `.stop` arm gains a plain
  `let`, not a new match arm (verified against the built `stepFn`, §4).

### 2.3 (c) Invalid UTF-8 — REFUSE by name (D5 default (i) — [AGENT] default applied per the coordinator's brief; [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off) (plan §4 D5))

The compared observation is `golean-observation-v1` with a `String`
message; a Lean `String` cannot carry the bytes gc writes, and a bytes
variant is an observation-schema change the [USER] owns (D5). So a payload
whose FIRST LINE is not valid UTF-8 renders `none`, and `abortMsg` refuses
with a message that NAMES the cause (`panic abort rendering: the string
payload's first line is not valid UTF-8 … (BUG-004 item 3 / D5)`), never
the sprint's `"\xHH"` member (A-R3). Rows: `panic-recover/panic-text/
{invalid-single,invalid-first-line,invalid-recovered-equal}` land RED
(FAIL/lean-observation) on BUG-004's `Cases:` line with gc's bytes recorded
in the entry (w37, w35, w36). If a byte channel is ever ruled, they flip
in a strict BYTE comparison, not a membership quotient. The
`escapeAllBytes`/`decodeEscapedBytes` half of `PanicText.lean` (landed by
L1 consumer-free) is DELETED here: with D5(i) the escape form is never a
member and a definition of a rejected member has no purpose in the
semantic core (the interface audit's two export lines go with it).

### 2.4 (d) The `string-member` lane — RETIRED ([AGENT] default applied per the coordinator's brief; [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off) (plan §4 D2))

Decision: RETIRE (the plan's recommended default; the [AGENT] applies it
as the default because the brief delegates the choice and asks for the
reason — it is NOT a ruling: D2 is a `[USER]` decision in the landing plan
§4 with `blocks: L3`, and the coordinator is putting it to the [USER]; audit
fix round R1). Its
three functions are covered by ordinary lanes after (a)–(c): the collapse
is a MEMBERSHIP row (both members enumerated, gc's draw checked ∈ set —
A-R1's exact defect is impossible by construction there); valid text is a
STRICT row with real gc comparison; invalid first-line bytes are RED by
name. What remained was a third comparison mode with its own pin format,
no re-pin guard (A-R4) and a CLI driver with one consumer. Nothing of it
lands: `Corpus/controls/string-members/**`, `baselines/string-members/**`,
`tools/string_member*.py`, `tools/test_string_member.py`,
`tools/check_string_member_fixtures.py`, `scripts/check-string-members.py`,
its `scripts/ci` step and lane vocabulary, `GoLean/CLI.lean`'s
`native-json-string-run` (C2/C3) and the `abortHeadJson`/`abortChainJson`
schema — all stay on the archive branch. Of its 13 control roles the 8
non-abort exact-equality roles add one thing the corpus lacked — the
recovered VALUE of an invalid-UTF-8 payload compared in-language — which
lands as the strict `ok` row `panic-recover/panic-text/invalid-recovered-value`
(the forced half beside the red text rows); the rest duplicate existing
`recover-*` rows. The sprint's `string-members/{equal,multiple,unequal}`
shapes land as ordinary rows of `panic-recover/repanic-collapse/`.

CORRECTION (audit fix round R5, [AGENT]): the sentence "its three functions
are covered by ordinary lanes" is FALSE for one role. The `Controls` role
(sprint branch `7edc298f`, `Corpus/controls/string-members/explicit/controls.go`
`catchControls`/`Controls`: `panic("a\x00\x01\t\r\nZ")` — embedded
NUL/SOH/TAB/CR preserved through the first-LF projection) has NO landed row
at this tip; the corpus holds zero control-byte panic payloads. It is the
one role DEFERRED, conditional on L4 landing its `panic-recover/panic-controls`
rows (9 rows, BUG-105 — filed by L4 on `land/observer-terminal`, NOT on this
branch: a merge-train dependency, deliberately not filed here), and rowed
in the ledger as FR-33 so the gap is visible regardless of the train order.
Measured asymmetry (`docs/evidence/2026-09-07_land-panic-text-tape/controls-asymmetry.txt`):
the machine renders the first line with all five bytes (`61 00 01 09 0d`,
valid UTF-8 — `stringFirstLine?`), while the gc side LOSES the NUL through
bash command substitution in `scripts/diff-coverage` (four bytes survive) —
a plain strict row today would be a red-by-accident (the harness's, not
the semantics'). Recorded; nothing landed.

### 2.5 (e) D5 default

`invalid-*` rows red; the escape-form member is never a member; no byte
channel is added by this chunk. Provenance class: [AGENT] default applied per the coordinator's brief; [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off) (plan §4 D5).

## 3. Rows by class, deferred-module restatements (the plan; measured in §4)

**Strict FIX (FAIL→PASS / born PASS):** `panic-recover/panic-newline-abort`;
`panic-recover/panic-text/{unicode-two,unicode-three,unicode-four,
unicode-mixed,unicode-newline,trailing-newline,recovered-newline,
recovered-unicode,output-prefix}` (the sprint's rows, credited);
`panic-text/invalid-after-lf` (first line `a`, w16 — a first-line-SCOPE
control, not invalid-UTF-8 coverage: its compared observation holds no
invalid byte; tagged `first_line_scope` at the audit fix round, R4d) and
`invalid-recovered-value` (ok); the controls `repanic-collapse/
{unequal,unrecovered-equal,equal-pair-not-head,multiline-passthrough}`
(strict — the last is a width-2 consult whose two members render the same
first line `first`, so the enumerated set is a singleton and the strict
invariance check certifies it).

**MEMBERSHIP (both members enumerated, `members=2`, K gc draws ∈ set):**
`panic-recover/repanic-same-value-abort` (FAIL/lean-observation → PASS/
membership; `expected_reason` kept at `orig`, the substring both members
share); `panic-recover/repanic-collapse/{passthrough-var,two-literals,
empty-literals,multiple,bool-reboxed,int-literals,defined-passthrough,
runtime-error-passthrough,nil-passthrough,unicode-literals,
runtime-error-two-faults}` (gc draws member 0) and `{reboxed-string,
runtime-computed,global-var,empty-reboxed,int-reboxed,defined-reboxed,
index-two-faults}` (gc draws member 1). Both members are gc-certified on
the string, int, defined-int and `runtime.Error` families; bool exhibits
member 0 only (§2.2).

**RED by name (BUG-004 `Cases:`):** `panic-recover/panic-text/
{invalid-single,invalid-first-line,invalid-recovered-equal}`.

**Deferred L1 modules, restated over the tape and the refusal** (a theorem
true only because of a baked-in member now quantifies the pick; a theorem
that assumed a total renderer gains the named refusal disjunct):
`StringPanic.lean` — `stringPanicHead bytes recovered collapsed : Option
String` (the member function; `none` iff the first line is invalid
UTF-8), `renderPanicHead_string`, `abortMsg_string`/`_refused`,
`stepFn_string_abort`, `runConfig_string_abort`; `RecoveryTerminal.lean` —
`Inv.run_classified` with FOUR disjuncts (normal / `.panic (stringPanicHead
… = some msg)` for the stream's pick / the NAMED invalid-UTF-8 refusal /
`fuelOut`), `Inv.run_refusal_named` replacing `run_no_refusal` (the only
refusal an admitted recovery program reaches is the invalid-first-line
abort), `runProgram_typed`/`runProgramPool_typed` likewise;
`RecoveryPoolObservationTyped.lean` — every member statement over the
event's recorded pick; `Tests/{PanicRendering,StringPanicMembers,
RecoveryTerminal,RecoveryTerminalAudit}.lean` — choice-indexed kernel
checks (both members at picks 0/1; invalid → `none`; the bool equal
re-panic is now a MEMBER, no longer `none`); `Tests/InterfaceContract.lean`
gains the import; spike `Terminal.lean` restated over the record's pick;
`scripts/check-recovery-terminal` + `tools/recovery-terminal-audit.py`
(L1-T) land with a `scripts/ci` step.

## 4. What was built (file by file; the sprint SHAs whose work each part redoes)

**Semantic core (trusted surface #1 — a BEHAVIOURAL change, disclosed here
first):**

- `GoLean/GoCore/State.lean` — `ChoiceSite.repanicCollapse` (the 13th
  constructor), its census prose entry and `canonicalSlot0` row.
- `GoLean/GoCore/Machine.lean` — `asciiString?` DELETED; `utf8StringAux?`/
  `utf8String?` (strict decode WITH the byte round-trip; theorem
  `utf8String?_bytes`), `stringFirstLine?` (byte-level first line +
  multi-line flag), `renderPanicPayload : … → Option (String × Bool)`,
  `repanicEqualNext`/`repanicCollapseWidth` (the envelope statement),
  `abortConsult` (THE consult), `recoveredSuffix`, `renderPanicHead … (pick)`,
  `abortRefusal` (the named D5 refusal text), `abortMsg … (pick)`,
  `abortLeftover`, `consumesRepanicCollapse`, the `seqConsumption` arm.
  (Redoes M1–M4 of `ff7173dd`/`819182b5`; `PanicText` is no longer imported
  by the renderer.)
- `GoLean/GoCore/StepFn.lean` — the `.panicking _ .stop` arm draws the pick
  through a plain `let` (no new match arm: `fun_cases`' positional tags are
  unchanged — `case7` is the abort arm in both consumption theorems, as
  before).
- `GoLean/GoCore/Multi.lean` — the pool's tombstone arm draws through
  `Choices.consumeAtE` (recorded in the abort `StepEvent`, the popped stream
  returned); `StepM.abort` quantifies `pick < repanicCollapseWidth first
  rest`; `poolConsumption`'s abort arm.
- `GoLean/GoCore/MachineSound.lean` — `seqConsumption_none_of_flags` and
  `stepFn_oblivious` gain the seventh flag `hnr`; `allStreamsOk`'s flag
  chain and proof; `stepFn_consumption_some`'s explicit `case7` (vacuous —
  the abort never returns `.ok`). `stepFn_sound`/`step_complete` are
  UNCHANGED in statement (the sequential relation has no abort rule, B4).
- `GoLean/GoCore/MultiSound.lean` — `stepFn_abort`, `stepMulti_abort_single`,
  `execProg_single_eq_execStmt`'s abort case, `stepMulti_sound`'s abort case
  (`consumeAt_fst_lt` discharges the width premise), `stepM_complete`'s abort
  case (the pick realized by `[]` at bound 1 and `[pick]` at bound 2).
- `GoLean/GoCore/MultiStreams.lean` — `poolThreadOblivious`: an abort is
  oblivious iff `!consumesRepanicCollapse`; `stepThread_oblivious`'s abort
  arm and its `stepFn_oblivious` call.
- `GoLean/GoCore/NPDRF.lean` — `StepMFine.abort` quantifies the pick.
- `GoLean/GoCore/RecoverySingleton.lean`, `RecoveryPool.lean` — the abort
  step/driver lemmas restated with the consult.
- `GoLean/GoCore/RecoveryPoolObservation.lean` — `abortEventPick?` (reads the
  event's recorded pick; `[]` = the forced 0), `stepAbortRecord?` re-derives
  the member from it, `stepAbortRecord?_some` carries the pick,
  `abortEventPick?_consumeAtE`.
- `GoLean/GoCore/RecoveryChoices.lean` — `Control.no_seq_consumption` and
  kin restated as `seqConsumption s c = none ∨ c.abort?.isSome` (the profile
  IS choice-free on every step — `Inv.step_no_seq_consumption` — and its
  abort may draw); `Inv.loop_all_choices` unchanged in statement.
- `GoLean/GoCore/PanicText.lean` — the `escapeAllBytes`/`decodeEscapedBytes`
  half DELETED (D5: never a member); `firstLine`/`firstLine_bytes`/
  `lfPrefix_valid` kept.
- `GoLean/GoCore/Ops.lean` — O1: the docstring names `utf8String?`.
- NEW `GoLean/GoCore/StringPanic.lean` — the member function
  `stringPanicHead bytes recovered collapsed : Option String`, `collapseBit`,
  `renderPanicHead_string`/`_runtimeError`, `abortMsg_string`/`_refused`/
  `_ok`, `stepFn_string_abort`/`_refused`, `runConfig_string_abort`/
  `_refused`, `stringFirstLine?_bytes` (redoes `819182b5`'s module; the total
  renderer, `renderStringMember_*`, `abortMsg_string_total` are GONE, not
  renamed).
- NEW `GoLean/GoCore/RecoveryTerminal.lean` — `Inv.run_classified` (FOUR
  disjuncts), `Inv.run_refusal_named`, `Inv.observed_abort_member`,
  `runProgram_typed`, `runProgramPool_typed`, `runProgramPool_refusal_named`,
  `runProgram_refusal_named` (redoes `7bd32ad6`; the `*_no_refusal` theorems
  are not restated — they were true only of the total renderer).
- NEW `GoLean/GoCore/RecoveryPoolObservationTyped.lean` — every member
  statement over the event's recorded pick; `singleton_observer_string_abort`
  + `_refused`; `Inv.pool_observation_eq` on both the member and the refusal
  path; `Inv.observer_classified`, `runProgramPoolWithAbort_typed`,
  `runProgramPoolWithAbort_panic_iff`, `runProgramPoolWithAbort_refusal_named`.

**Tooling / tests / spike:** `GoLean/ChoiceTrace.lean` (`siteName`,
`allSites` — `allSites_complete` re-proved by `cases`, `repanicCollapseFacts`,
`seqFacts` arm, `isPoolRecorded` includes the abort's recorded consult);
`GoLean/EnumDedup.lean` (the dedup checker refuses the site by name);
`GoLean/CLI.lean` (inventory row 9; `enumInitRun` returns `abortLeftover`;
the C2/C3 `native-json-string-run` driver is NOT landed — D2);
`Tests/GoCoreEval.lean` (the four `renderPanicPayload` checks retyped + five
L3 checks); `Tests/PanicRendering.lean`, `Tests/StringPanicMembers.lean`
(choice-indexed kernel checks), `Tests/RecoveryTerminal.lean` +
`Tests/RecoveryTerminalAudit.lean` (44 exports — the count read "48" before the audit fix round; three D5-refusal challenges,
the multi-line challenge, and the equal re-panic's TWO members from two
streams on an admitted program); `Tests/InterfaceContract.lean` (import);
`Tests/InterfaceAudit.lean` (exports; the constructive-helper check now
pins `utf8String?`, `stringFirstLine?`, `renderPanicHead`, `abortMsg`);
`GoLean/Interface.lean` (imports + the terminal/choice-free prose);
`lakefile.toml` (`InterfaceTests` globs, `RecoveryTerminalTests`);
`scripts/check-recovery-terminal` + `tools/recovery-terminal-audit.py`
(L1-T, verbatim from `7bd32ad6` except the scratch dir made repo-local) and
its `scripts/ci` step; `spikes/iris-customer/GoLeanIris/Terminal.lean`
(restated; `*_no_refusal` → `*_refusal_named` + `fixtures_not_refused_at_fuel`)
and the spike's module wiring (`GoLeanIris.lean`, `Audit.lean`, `check`,
`gate_checks.py`).

**Corpus:** `Corpus/coverage/exec/panic-recover/panic-text/` (14 rows: the
sprint's 9 + `invalid-after-lf`, `invalid-single`, `invalid-first-line`,
`invalid-recovered-equal`, `invalid-recovered-value`),
`panic-recover/repanic-collapse/` (22 rows: 18 membership + 4 strict
controls), `panic-recover/repanic-same-value-abort/cases.tsv` (→
`lane=membership`, `nondet`, `width=2,sites=8,members=2`, `why`).

**Records:** `docs/BUGS.md` BUG-004 (Cases line + the L3 block);
`docs/2026-08-11_latitude-inventory.md` (census table row, R10 revised, NEW
R10a, §10 (a) list + history); `docs/2026-08-04_nondeterminism-doctrine.md`
(site mirror re-synced — `tryLock` and `unseqPanic` had been missing too);
`docs/2026-08-19_triage-table.md` (C4 pointer); `docs/2026-09-05_master-plan.md`
(the BUG-004 row); `docs/language-coverage-ledger.md` (§8 header, bucket
table, §8w movement); `baselines/native-full.tsv` (re-pinned once, header
reason); this note; `docs/evidence/2026-09-07_land-panic-text-tape/`.

## 5. Verification (measured at the landing tip)

Envelope for every Lean/Lake invocation: `scripts/capped`, `GOLEAN_MEM_MAX=16G
LEAN_NUM_THREADS=4`; the differential at `GOLEAN_COVERAGE_JOBS=12` (the
brief's cap is 16; a sibling landing lane ran concurrently). Host and
toolchain: evidence README.

### 5.1 Build, escape hatches, axioms, the correspondence statements

- `scripts/capped lake build golean`: `Build completed successfully (190
  jobs)`, ZERO `warning:` lines (the core-build step's warning-free rule).
- Escape hatches: `grep -rn 'sorry\|native_decide\|axiom' GoLean/` — prose
  hits only (NPDRF.lean's docstring), no new hits; `grep -rn 'partial '
  GoLean/GoCore/` — one prose hit (ProgramTrace.lean), unchanged from main;
  no `decide +native` anywhere. `decide +kernel` is used in
  `Tests/PanicRendering.lean`, `Tests/StringPanicMembers.lean`,
  `Tests/RecoveryTerminal.lean` (kernel, doctrine-permitted, as the sprint's
  tests did).
- Axioms (`#print axioms`, `.tmp/build/axioms.log` at the tip):
  `utf8String?`, `stringFirstLine?`, `renderPanicHead`, `abortMsg`,
  `stringPanicHead` → `[propext, Quot.sound]` (constructive — the interface
  audit's constructive-helper check pins the first four);
  `utf8String?_bytes`, `Inv.run_classified`, `runProgramPool_typed`,
  `runProgramPoolWithAbort_panic_iff`, `stepFn_sound`, `step_complete`,
  `stepMulti_sound`, `stepM_complete`, `stepFn_consumption_some`/`_none` →
  the classical trio `[propext, Classical.choice, Quot.sound]` (the public
  layer's allowance).
- `stepFn_sound : stepFn s c ch = .ok (c', s', ch') → Step c s c' s'` and
  `step_complete : Step c s c' s' → ∃ ch ch', stepFn s c ch = .ok (c', s',
  ch')` `#check` to exactly main's statements. The sequential relation has
  no abort rule (B4) so neither gains an arm; the POOL relation's
  `StepM.abort`/`StepMFine.abort` quantify the pick, and `stepMulti_sound`
  (soundness) / `stepM_complete` (completeness: the stream `[]` at bound 1,
  `[pick]` at bound 2) cover the new premise. `fun_cases stepFn`'s
  positional tags are unchanged: `case7` is the abort arm in both
  consumption theorems, exactly as on main (the arm gained a `let`, not a
  match arm) — the `some` half now handles it explicitly as vacuous.
- Gates run standalone at the tip: `scripts/check-interface` → `Semantic
  interface: PASS` (InterfaceTests incl. `Tests/PanicRendering`,
  `Tests/StringPanicMembers`; the post-import audit; compiled poison
  controls); `scripts/check-recovery-terminal` → `Typed recovery terminal
  gate: PASS` (44 exports, five compiled poisons rejected);
  `gocore-eval-tests` → 207 ok (202 on main + the five L3 checks);
  the opt-in spike gate `spikes/iris-customer/check` → `Iris customer: PASS`
  (the spike's `.lake/packages` seeded by copy from a sibling worktree —
  no network; `GoLeanIris.Terminal` built and audited, the two fixture
  differentials 3/3 and 5/5 PASS); `GO111MODULE=off go test
  ./tools/{nativefrontend,lowerdiag,coverageharness}` → ok ×3 (nothing
  under `tools/` changes except the new audit tool).

### 5.2 The rows (`scripts/diff-one` over the 39 touched ids, then the full run)

36 PASS / 3 FAIL, every row exactly as §3 planned; the full run agrees
(§5.4). gc's draw per membership row (`gc-draws.tsv`; K=32, alternating
plain/`-race`, one distinct observation per row, `enumerated=2` on every
row — `enumeration-stats.txt`):

| gc draws member 0 (collapse) | gc draws member 1 (two-line form) |
|---|---|
| `repanic-same-value-abort`, `passthrough-var`, `two-literals`, `empty-literals`, `multiple`, `bool-reboxed`, `int-literals`, `defined-passthrough`, `runtime-error-passthrough`, `nil-passthrough`, `unicode-literals`, `runtime-error-two-faults` (12) | `reboxed-string`, `runtime-computed`, `global-var`, `empty-reboxed`, `int-reboxed`, `defined-reboxed`, `index-two-faults` (7) |

Every draw matches the witness table's prediction for its shape (§1.1);
both members are gc-certified on the string (`passthrough-var` vs
`reboxed-string`), int (`int-literals` vs `int-reboxed`), defined-int
(`defined-passthrough` vs `defined-reboxed`) and `runtime.Error`
(`runtime-error-two-faults` vs `index-two-faults`) families; bool exhibits
member 0 only (§2.2). The three red rows fail with the NAMED refusal
(`… the string payload's first line is not valid UTF-8 (2 payload byte(s),
first line [255, 90]) — gc prints the raw bytes and the String-valued
observation cannot carry them (BUG-004 item 3 / landing decision D5: no
byte channel)`), status `unsupported`, stage `lean-observation`.

### 5.3 The whole-corpus consumption trace, main's binary vs this one

`scripts/choice-trace-corpus --dump --jobs 6` over the same corpus (3595
exported rows; 2 excluded as every corpus trace excludes them; 37 frontend
refusals; 1 tracer ERROR row — all identical before/after) and the same six
streams, once with the binary built at main `90bc3e06` in a detached
worktree and once with this tip's (`choice-trace-compare.txt`):

- (row, stream) lines: 21,565 = 21,565. Status/obsHash DIFFERENT on 408
  lines, all on the 34 rows this chunk added or re-laned (13 of the 14
  `panic-text/*` — `invalid-recovered-value`, an in-language `ok` row, is
  identical on both binaries — the 18 membership + `multiline-passthrough`
  of `repanic-collapse/`, `repanic-same-value-abort`, `panic-newline-abort`;
  the three strict controls `unequal`/`unrecovered-equal`/`equal-pair-not-head`
  are likewise identical on both); NO other row moved on any stream.
- Per-site consumption totals: every pre-existing site IDENTICAL
  (`l5ExitWindow=325 mapIter=1307 l2Entry=24 l1Sched=9443 backEdge=2404
  l2Arrival=3 postOp=4534 unseqPanic=417 appendSpill=4874 tryLock=101
  nilValueMethodText=84 l4Waiter=22`); after adds `repanicCollapse=126` =
  21 rows × 6 streams — the 18 membership rows, `multiline-passthrough`,
  `repanic-same-value-abort` and `invalid-recovered-equal` (whose refusal
  is drawn under either pick). Record sequences changed on exactly those
  126 lines and nowhere else: a bound-1 consult pops nothing and leaves no
  record, so every pre-existing abort consumes exactly as before.
- Menu-invariant violations 0, self-check alarms 0, driver disagreements 0
  on both sides; the 37 depth-exposure rows the tracer lists are the
  standing pre-existing report, identical before/after.

### 5.4 The full differential and the re-pin

`scripts/capped scripts/ci --diff` (run 1, this working tree, jobs 12):
`differential coverage summary: cases=3634 pass=3388 fail=246`; DRIFT vs the
previous pin = exactly the 36 born rows and the 2 FAIL→PASS flips listed in
§8w of the ledger, 0 PASS→non-PASS, 0 removals (`.tmp/build/ci-run1.log`;
every other step `ok`, incl. `core build (warning-free)`, `semantic
interface`, `typed recovery terminal classification`, `eval tests (207 ok)`,
`frontend pins`, `negative baseline diff` 394/394). `baselines/native-full.tsv`
re-pinned ONCE by splicing that drift into the tracked file (the two flips
updated in place, the 36 born rows inserted at their families' alphabetical
positions, the 9 stage-alternation rows and their `# reason:` blocks
untouched), header reason at its top; awk tally PASS 3388 / FAIL 246;
`scripts/coverage-baseline-diff artifacts/coverage/latest.tsv` → `no
regression: 3634 case(s)`; `scripts/check-alternation-survival` silent;
`scripts/check-bugs.sh` → `ok (104 bug(s)); backlog — 14 unexplained
fidelity failure(s)` (main's figure; unchanged). Frontend and
`NativeToIR.lean` untouched → merge-protocol step 5a is not owed.

### 5.5 The gate at the clean committed tip (run 2)

Run at `52b77e4502bc93f6876ec0868a3337853fff4668` (= `refs/snapshots/
land-panic-text-gated`; the final landing commit differs from it ONLY by
`docs/evidence/2026-09-07_land-panic-text-tape/ci-diff-tail.txt` and this
section — a documentation-only amend, the 2026-09-05/2026-09-07 landing
practice). Envelope `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=4
GOLEAN_COVERAGE_JOBS=12`. The run's `latest.meta.tsv`: `git_commit
52b77e45…`, `git_dirty false`, `jobs 12`, `membership_draws 32`. Verbatim
lines (full tail: `ci-diff-tail.txt`):

```
differential coverage summary: cases=3634 pass=3388 fail=246 export_status=0
  ok   bug-index cross-check
  ok   evidence-on-main size gate
  ok   core build (warning-free)
  ok   semantic interface (bridges, counterexamples, compiled audit negatives)
  ok   admission checker proofs and post-import audit
  ok   typed recovery terminal classification
  ok   frontend pins (realized init-order deviation + twin wire = pinned bytes)
  ok   eval tests (207 ok)
  ok   differential run completed (exit 1; failing-set judged by baseline diff)
  ok   negative run completed (exit 0; set judged by baseline diff)
  ok   negative baseline diff (no regression)
  ok   baseline diff FULL (3634/3634, no regression)
  ok   re-pin guard (0 PASS→non-PASS flip(s), all listed in BUGS.md Cases)
  note re-pin baselines/native-full.tsv: 2 non-PASS→PASS flip(s), 0 deleted row(s) — report-only; verify the re-pin's written reason covers them
  note reconciler: 3 finding(s), 0 HIGH — report-only (details: tools/reconcile-records)
RESULT: PASS
```

Baseline drift at the tip: ZERO (`baseline diff FULL (3634/3634, no
regression)`); the re-pin guard in `HEAD-vs-HEAD~1` mode: 0 PASS→non-PASS
flips, the 2 non-PASS→PASS flips reported and covered by the header reason;
awk tally of `baselines/native-full.tsv`: PASS 3388, FAIL 246; the
reconciler's 3 report-only findings are main's standing ones (dangling
BUG-105/106/107 references in the landing plan, off-pin Go-version
citations, one frontier-table citation) — 0 HIGH, as at L1. `git status
--short` at the tip: empty. `scripts/ci --slow` is NOT owed (no
`wire.go`/`NativeToIR.lean` change; the twin pin is byte-identical).

## 6. Dispositions, deferred-module restatements, records, credits

- **D2 (the `string-member` lane): RETIRED, unlanded — [AGENT] default applied per the coordinator's brief; [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off) (plan §4 D2).**
  Reason in §2.4. Nothing of it exists on main; the archive branch keeps
  it. The `Controls` role is DEFERRED to L4 (§2.4 correction; FR-33).
- **D5 (byte channel): default (i) — [AGENT] default applied per the coordinator's brief; [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off) (plan §4 D5)** —
  no byte channel; `invalid-*` rows red by name; the escape-form member is
  never a member (§2.3, §2.5).
- **BUG-087 shape (audit fix round R2):** the envelope's authority is an
  [AGENT] extension of BUG-087's ruling SHAPE (a demonic choice where gc's
  realization is toolchain-internal) under R-1's re-envelope authority;
  [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off) — relabelled on all 18
  `repanic-collapse` `why` fields, `repanic-same-value-abort`'s, R10a, the
  triage table, BUGS.md, the corpus `main.go` header and the code docstrings
  (Machine.lean's envelope statement, CLI.lean's inventory row; the
  `canonicalSlot0` string in State.lean is OWED — a core string literal this
  round does not touch).
- **C4 re-classification (audit fix round R3):** `repanic-same-value-abort`
  was a [USER]-ratified category-(c) pin (triage §7, 2026-08-20; §7's
  re-colorable list names C1/C5/E7/R6 — not C4). Its (c)→(a) move to the
  membership lane is by [AGENT] under R-1 and touches a ratified pin —
  [USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off); marked so in the triage
  table (a dated line under the C4 entry), the ledger (§8 bucket table,
  §8w) and R10a. The move itself was KEPT pending the ruling and STANDS under it (§7.2).
- **The brief's hard stop (implement exactly vs a site): a SITE.** The
  marker is deterministic in gc but in a quantity — eface identity — the
  machine does not and should not carry (§1.1). Said explicitly there.
- **Deferred L1 modules, restated** (§4 lists each): every theorem that was
  true only of the sprint's total renderer or its unconditional
  ` [recovered]` member now either quantifies the pick (`collapseBit … pick`,
  `∃ collapsed`) or carries the named refusal as a disjunct
  (`Inv.run_classified`'s four outcomes; `*_refusal_named` in place of
  `*_no_refusal`). The bool equal re-panic that the sprint's
  `non_string_boundary` test pinned as `none` is now a MEMBER (both picks) —
  `Tests/PanicRendering.equal_repanic_other_families`.
- **Records touched:** `docs/BUGS.md` (BUG-004: Cases line and the L3 block —
  no new BUG number: the three reds are item 3's residue under D5);
  `docs/2026-08-11_latitude-inventory.md` (census row; R10 revised; R10a
  new; §10 (a) list 11/13 → 13/15 with R9a's missing membership line added
  and the history note); `docs/2026-08-04_nondeterminism-doctrine.md` (site
  mirror — `tryLock`/`unseqPanic` were missing too; re-synced);
  `docs/2026-08-19_triage-table.md` (C4 pointer); `docs/2026-09-05_master-plan.md`
  (the BUG-004 row); `docs/language-coverage-ledger.md` (§8 header, bucket
  table: (c) 24 + 1, (a)-queued 7, post-vintage 68, total 246; §8w);
  `baselines/native-full.tsv` (one re-pin, reason in header). The doctrine's
  §10 known-≠-gc list is unchanged: a named refusal is not a deterministic
  answer that differs from gc's. `CLAUDE.md`/`AGENTS.md` untouched.
- **Credits (sprint commits whose work this chunk redoes or lands):**
  `ff7173dd`, `82e177c7`, `c7eeaf57` (the UTF-8 first-line widening and the
  nine `panic-text/*` rows — landed in substance, sharpened to the byte-level
  first line); `819182b5`, `ccf826cb`, `c969079a`, `4a8a8ad1`, `e6a99203`,
  `731beb0b`, `bb850710`, `f0829091`, `91efd4ca`, `563c01de`, `b5dd4076`
  (the string-member lane, `StringPanic`, `PanicText`'s escape half, the
  `Equal`/`Multiple`/`Unequal` shapes — the ORIGIN of what §2.2–§2.4 rework;
  the lane itself is retired); `7bd32ad6` (L1-T: `RecoveryTerminal`,
  `RecoveryPoolObservationTyped`, their tests, `scripts/check-recovery-terminal`,
  `tools/recovery-terminal-audit.py`, the spike's `Terminal.lean` — landed
  restated). Squashed into ONE landing commit; the authored history is on
  `typed-consumer-sprint` (`docs/ARCHIVE.md`). The two landing audits'
  findings this chunk closes: A-R1 (no comparison mode exists that skips
  gc's text — the membership lane checks gc's draw ∈ set, the strict lane
  compares gc's line), A-R2 (the collapse is on the tape, never a
  hard-coded member), A-R3 (the fail-closed `none` is restored by name for
  invalid first lines; no escape member), A-R4 (no `baselines/string-members/`
  pin class exists), B-R3 (R-1 is not stretched: the envelope's members are
  both gc-realized renderings).
- **Not done here, by design:** a byte channel (D5(ii), the [USER]'s);
  BUG-004 item 4 (the `Error()`/`String()` rewrite — its two red rows
  stand); BUG-105's control-byte transport (L4's, running in parallel —
  this chunk adds no control-byte rows); the spike gate's fixture-controls
  tool of the sprint (`tools/check-recovery-fixture-controls.py`, not on
  main — L2/L4's).

## 7. Adversarial audit fix round (2026-09-07, [AGENT] fix-round worker, same lane)

Verdict received (the pre-merge adversarial audit of `bf925590`): **the
envelope is sound — no gc realization outside the set, no baked-in
choice — FIX-FIRST on provenance and records.** Applied here, every
judgement [AGENT]-tagged; nothing below is a ruling. The [USER] rulings
this round makes PENDING (verbatim tags as written in the records):

- D2 / D5: «[AGENT] default applied per the coordinator's brief; [USER]
  ratification PENDING at the merge gate (plan §4 D2/D5)».
- BUG-087 shape: «[AGENT] extension of BUG-087's ruling SHAPE (a demonic
  choice where gc's realization is toolchain-internal), under R-1's
  re-envelope authority; [USER] ratification PENDING».
- C4: «(c)→(a) re-classification by [AGENT] under R-1; touches a ratified
  (c) pin — [USER] ratification PENDING at the merge gate».

All four were RULED at merge train round 24 (§7.2 below). The three tags
above are the fix round's wording, kept verbatim here as history; every
live record now reads «[USER] ratification — PENDING at the lane's tip,
RULED [USER] 2026-09-07 at merge train round 24 — «Go ahead with the
merge» (…)» with the [AGENT]-default history left visible.

| item | disposition |
|---|---|
| R1 authority (D2/D5 applied as defaults) | FIXED — tagged PENDING in this note (§2.3, §2.4, §2.5, §6), BUGS.md, the inventory (R10a), the ledger (§8w), the triage table (:481), `Interface.lean`, `panic-text/main.go`. No ruling claimed; left PENDING (none relayed before this round closed). |
| R2 BUG-087 over-extension | FIXED — the 18 `repanic-collapse` `why` fields, `repanic-same-value-abort`'s `why`, `repanic-collapse/main.go`, R10a (heading + body), the triage C4 block, BUGS.md, this note's ruling context, Machine.lean's envelope docstring, CLI.lean row 9 all relabelled "extension of BUG-087's ruling SHAPE … PENDING". OWED: the `canonicalSlot0` row string in State.lean (core code literal; this round does not touch it). |
| R3 C4 re-classification | FIXED — move kept; marked PENDING in the triage table (dated line under C4 + the L3 block), the ledger (§8 bucket table, §8w), R10a (ROWS), `repanic-same-value-abort/cases.tsv` and `main.go`. |
| R4 observation scope | FIXED — (a) dated rule in `docs/2026-07-25_unwinding-arc.md` §A3 (continuation lines; tail unmodelled/unobserved); (b) BUGS.md item 3 softened to "fixed as far as the observed surface reaches"; (c) ledger FR-32 + queue 32 (whole-message widening; L4's `crashview.go` as the site — not on this branch); (d) `invalid-after-lf` retagged `first_line_scope` (new vocabulary tag), its `main.go` comment and every "born PASS" mention say first-line-scope control; (e) `first-line-scope.txt` measured (`head`/`head` identical through the harness awk; `stringFirstLine?` identical on the machine); (f) `unwinding-arc.md` (3) marked STALE with the L3 facts. |
| R5 D2 mapping | FIXED — `Controls` named as the one role DEFERRED (§2.4 correction), conditional on L4's `panic-controls` rows / BUG-105 (NOT filed here — a train dependency); ledger FR-33 + queue 33; asymmetry measured and recorded (`controls-asymmetry.txt`: machine 5 bytes `61 00 01 09 0d`, bash capture 4 — the NUL dropped). Note: the audit's phrase "the machine emits `"a b"`" is not what the probe shows — the machine's String carries the five raw bytes; the record states the measurement. |
| R6 doctrine mirror | FIXED (CODE, tooling) — `tools/reconcile-records` C12 now compares the doctrine's site list (every entry names its constructor in backticks; the seven pre-W3.2 entries were tagged) and `ChoiceTrace.allSites` against the `ChoiceSite` datatype, HIGH on drift; negative-tested (removing one constructor name → two HIGH findings; restored → none); 0 HIGH at this tip; obligation recorded in the doctrine's history block. |
| R7 Interface overclaim | FIXED (CODE, statements) — `Inv.observed_abort_member` now yields the member on the RECORD's chain at the STREAM's pick (`Inv.observed_abort` supplies `residual = ch` and `first :: rest = record.chain`); `Inv.run_classified`'s panic disjunct carries the computed record + that anchored member (the induction moved to `Inv.run_outcomes`); `runProgram_typed`/`runProgramPool_typed` additionally tie the record to the driver's own `runProgramSetupM`; observer twins `stepAbortRecord?_member`, `PoolAbortWitness.string_member`, `runProgramPoolWithAbort_member`, `Inv.observer_classified`, `runProgramPoolWithAbort_typed`, `_panic_iff` anchored to `collapseBit first rest pick` on `record.chain`. All proofs close; axioms unchanged (classical trio; `stepAbortRecord?_member` constructive). `Interface.lean` says exactly what is proved and what is NOT (the tail; the setup exposed existentially). Spike `Terminal.lean` restated (opt-in gate not re-run this round — OWED at the train). |
| R8 `/tmp` in README | FIXED — `.tmp/witness/` per operational-lessons. |
| L1 stale `main.go` comment | FIXED. |
| L2 MultiSound comment | FIXED (comment only). |
| L3 `land-typed-core-proofs.md:32` | FIXED (the note is on this branch; bracketed correction). |
| L4 `.nil` arm | FIXED (CODE, one arm → `none`); probe: `renderPanicPayload {} .nil = none`, the refusal names the payload, `panicPayload .nil` still renders gc's text; build + 207 eval ok. |
| L5 `no_seq_consumption` | FIXED (CODE) — `∨ consumesRepanicCollapse c = true` in `UnwindCont`/`Control`/`Inv.no_seq_consumption`; the sole consumer `Inv.step_no_seq_consumption` closes with one `unfold`. |
| L6 "ONE shared consult" | FIXED — one shared consult FUNCTION, two call sites. |
| L7 counts | FIXED — 38 witnesses (note + README), 13 of 14 `panic-text/*` moved (§5.3), baseline header "38 rows" → 34 of 38, "48 exports" → 44. |
| L11 `abortEventPick?` docstring | FIXED — cites `isTerminal_of_abort`/`atBoundary_of_abort` and `abortEventPick?_consumeAtE` for the `none` arm. |
| L13 provenance classes | FIXED — D5's disposition, the doctrine re-sync block, the triage C4 block, ledger §8w carry [AGENT] tags. |
| L14 `printPreFatalDeferPanic` | FIXED — 1259–1276. |

Owed (recorded, not done here): the State.lean `canonicalSlot0` wording (R2); the opt-in spike gate re-run (R7); FR-32 and FR-33 (rowed with queue slots, L4-dependent); the [USER] rulings D2, D5, C4 and the BUG-087-shape extension — RULED at merge train round 24 (§7.2).

### 7.1 Gate at the fix round's clean committed tip

Run at `0ccefe3f726dc9346cbacb3020fbc36baf47066f` (this round's single
code+records commit; the commit that follows differs from it ONLY by this
subsection and `ci-diff-tail-fixround.txt` — the documentation-only amend of
the landing practice, §5.5). Envelope `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=4
GOLEAN_COVERAGE_JOBS=12`; `latest.meta.tsv`: `git_commit 0ccefe3f…`,
`git_dirty false`, `jobs 12`, `membership_draws 32`. Verbatim lines (full
tail: `ci-diff-tail-fixround.txt`):

```
differential coverage summary: cases=3634 pass=3388 fail=246 export_status=0
  ok:207  fail:0  exit:0
  ok: lake-build failure exits 2, no readable results (G1)
  ok: lake-build timeout exits 2, no readable results (G2)
  ok: manifest-not-found exits 2, no readable results (G3)
  ok: empty manifest exits 2 without publishing (G4)
  ok: harness re-validation rejects sites=0 (F4)
  ok: harness refuses the retired samples= param by name (F4b)
  ok: membership under non-native frontend fails closed (F6)
  ok: members= cardinality pin refuses a wrong pin (B3)
  ok: confluent lane refuses a non-singleton set (B4)
  ok: racy lane fails loud on a refuted width (B5)
  ok: depth guard refuses a strict row whose adversarial streams are exhausted, naming the cause (D1)
  ok: the same row routed to confluent is certified (|set|=1) (D2)
  ok: the same row with a sufficient depth=N passes, recording wide=/depth= (D3)
  ok: an insufficient depth=N is refused, naming the exhausted seeded stream (D4)
  ok: a variant-stream refusal is reported as a refusal (lean-observation), not as nondet (D5)
  ok: harness re-validation refuses depth=0 (D6)
  ok: fan-out that ran no worker exits 2 without publishing (G5)
  ok: G5 named both causes (global fan-out refusal + empty-row guard), no stray .out
  ok: T1-strict-lean-run: cause named at stage lean-observation (Lean run TIMED OUT after 1s)
  ok: T2-nondet-rerun: cause named at stage nondet (re-run under stream [9,8,7,6,5,4,3,2,1,0] TIMED OUT after 1s)
  ok: T3-coupling-pin: cause named at stage membership (driver-coupling pin: native-json-run under stream [9,8,7,6,5,4,3,2,1,0] TIMED OUT after 1s)
  ok: T4-sample-loop: cause named at stage membership (observation-eq TIMED OUT after 1s (LEAN_TIMEOUT_SECONDS) comparing a Go sample against member #1)
  ok: T5-comparator-undecodable: cause named at stage go-observation (Go output is not a valid observation (comparator said: left.status: unknown observation status)
  ok: T6-lean-run-sigkill: cause named at stage lean-observation (Lean run KILLED (exit 137)
  ok: T7-differential-sigterm: cause named at stage differential (observation-eq KILLED (exit 143)
  ok: T8-go-oracle-sigkill: cause named at stage go-run (go run oracle KILLED (exit 137)
  note build parallelism: LEAN_NUM_THREADS=4 (set by the caller — honoured as-is)
  ok   oracle toolchain (go1.26.5 = pin)
  ok   escape-hatch preflight
  ok   meta-layer escape hatches (allowlist empty since the repo split)
  ok   escape-hatch addendum (no decide +native / native-config spellings)
  ok   bug-index cross-check
  ok   feature-coverage (no dead tags)
  ok   spec-anchor citations resolve at the pin
  ok   stdlib admission register = frontend tables
  ok   lane-validation fixtures (manifest gates reject bad shapes)
  ok   evidence-on-main size gate
  ok   imported-goose verbatim (above-marker bytes = pinned upstream)
  ok   engine-isolation (core ↛ EnumDedup)
  ok   core build (warning-free)
  ok   semantic interface (bridges, counterexamples, compiled audit negatives)
  ok   admission checker proofs and post-import audit
  ok   typed recovery terminal classification
  ok   frontend pins (realized init-order deviation + twin wire = pinned bytes)
  ok   import-goose fixtures (importer + verbatim guard reject bad shapes)
  ok   frontend unit tests
  ok   lowering-diagnostic tables
  ok   eval tests (207 ok)
  ok   differential run completed (exit 1; failing-set judged by baseline diff)
  ok   lane-validation fixtures incl. harness half (F4/F6/B3-B5/G5/T1-T8/D1-D6)
  ok   negative run completed (exit 0; set judged by baseline diff)
  ok   Tests/FloatVectors.lean = fresh hardware-oracle regeneration (byte-exact)
  ok   inittask-std.tsv = fresh gc-derived regeneration (header at pin; byte-exact modulo date line)
  ok   negative baseline diff (no regression)
  ok   baseline diff FULL (3634/3634, no regression)
  ok   re-pin guard (0 PASS→non-PASS flip(s), all listed in BUGS.md Cases)
  note reconciler: 3 finding(s), 0 HIGH — report-only (details: tools/reconcile-records)
RESULT: PASS
```

Drift: ZERO (`baseline diff FULL (3634/3634, no regression)`;
`scripts/coverage-baseline-diff` → `no regression: 3634 case(s)`; the re-pin
guard 0 PASS→non-PASS; no re-pin note — the baseline's data rows are
untouched, only its header comment changed, L7). The reconciler's 3
report-only findings are the standing classes (off-pin Go-version cites, the
FR-7 `=` citation, dangling BUG-105/106/107 references — the BUG-105 count
grew because this round names L4's filing on purpose). `git status --short`
at the tip: empty. `scripts/ci --slow` is NOT owed (no `wire.go`/
`NativeToIR.lean` change).

### 7.2 The merge-gate ruling and the round-24 rebase onto main dd636996 (2026-09-07, [AGENT] rebase-reconciliation worker)

**The ruling.** The coordinator's merge-ask for this chunk (branch tip
`9e3c54f0`, the fix round applied) listed the four items §7 tags PENDING —
D2 (the `string-member` lane retired unlanded), D5 (option (i): no byte
channel, the `invalid-*` first lines refused by name), the BUG-087-shape
extension (the `repanicCollapse` envelope under R-1) and the C4 (c)→(a)
move of `repanic-same-value-abort` — as what the sign-off would ratify.
[USER] Mike, 2026-09-07, verbatim as relayed by the [AGENT] coordinator
(this worker did not receive it firsthand — cite as relayed): «Go ahead
with the merge». The coordinator reads the sign-off as ratifying all four;
this worker records it so. Every PENDING tag this lane wrote now reads
«[USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at
merge train round 24 — «Go ahead with the merge» (relayed by the [AGENT]
coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and
the C4 (c)→(a) move as the four items ratified by this sign-off)», the
[AGENT]-default history left visible (they WERE applied as defaults first):
this note (§1 ruling context, §2.3, §2.4, §2.5, §6; §7's three quoted tags
are kept verbatim as the fix round's wording), `docs/BUGS.md` BUG-004 (the
L3 block, 4 tags + "the move STANDS"), the latitude inventory (R10a heading
+ body + ROWS + the D2 line; §10's history line), the triage table (the C4
dated line — the count 3 → 2 is no longer provisional — and the L3 block,
3 tags), the ledger (§8 bucket table's C4 note, §8w's D2 line and its
fix-round paragraph), `GoLean/Interface.lean`, `GoLean/GoCore/Machine.lean`
(the `repanicEqualNext` docstring) and `GoLean/CLI.lean` (inventory row 9)
docstrings, `Corpus/coverage/exec/panic-recover/{panic-text,repanic-collapse,
repanic-same-value-abort}/main.go` and the 19 `why` fields (18
`repanic-collapse` + `repanic-same-value-abort`). The tracked ruling record
is `docs/2026-08-31_qrow-rulings.md`, "The merge-train round-24 ruling
record". Still OWED: the `canonicalSlot0` row string in State.lean (§7 R2).

**The rebase.** `git rebase main` from `90bc3e06` onto `dd636996` (main
gained chunk L4 `land/observer-terminal`: the same-run crash-channel
harness, the 20 `panic-controls`/`panic-markers` rows, BUG-105 fixed,
BUG-106/BUG-107 open, baseline 3618 = 3362 / 256, ledger §8x). Snapshot
`refs/snapshots/r24-l3/pre` = `9e3c54f0`. Conflicts ONLY in the three
record files, resolved keep-both: `baselines/native-full.tsv` (header
blocks, this lane's on top, re-derived; the data rows auto-merged — the two
lanes' rows are disjoint, 0 duplicate ids), `docs/BUGS.md` (BUG-004's Cases
line composed; L3's block then L4's two paragraphs), the ledger (§8 head
paragraph, the bucket table, §8w before §8x — no letter collision, no
re-lettering). `scripts/ci` auto-merged with BOTH lanes' steps present (L3's
`typed recovery terminal classification`, L4's `coverage-harness unit
tests`). No `wire.go`/`NativeToIR.lean` change on either side — no
`scripts/ci --slow` (5a) owed. Composition: 3618 + 36 born = 3654 = 3397 /
257 (3362 + 33 + 2; 256 + 3 − 2).

**The focused slice at the rebased tip, and the re-pin.** `scripts/capped
scripts/diff-one` over the 65 rows either lane touched (jobs 12, K=32;
`docs/evidence/2026-09-07_land-panic-text-tape/round24-rebase-slice.txt`):
56 PASS / 9 FAIL; `scripts/coverage-baseline-diff` vs the composed rows
moved EXACTLY nine, all re-pinned with the reason in the baseline header:

| row | composed | rebased tip | why |
|---|---|---|---|
| `panic-recover/panic-controls/{newline,recovered-newline}`, `panic-recover/panic-markers/{mixed-line,fake-trace,literal-continuation}` | FAIL/lean-observation | PASS strict | main's `asciiString?` refused the embedded-LF payload; this chunk's strict first-line renderer reaches L4's rows |
| `panic-recover/panic-controls/child-confluent` | FAIL/confluent | PASS/confluent, \|set\|=1 | same, inside the schedule enumerator's alias-guard probe |
| `panic-recover/panic-text/{invalid-single,invalid-first-line,invalid-recovered-equal}` | FAIL/lean-observation | FAIL/go-observation | L4's harness refuses the oracle's invalid-UTF-8 first line BY NAME (`could not extract Go panic message: observation string is not valid UTF-8 (N bytes), refused`) before the machine's D5 refusal is reached — the same cause, both sides refusing by name; still red on BUG-004's Cases line (D5 RULED (i): no channel) |

The six flips are under option (ii) of L4's hazard note (BUG-004, L4 note
§2): the first-line scope is a DOCUMENTED standing contract of the
observation — this chunk's §A3 rule (`docs/2026-07-25_unwinding-arc.md`,
2026-09-07; ledger FR-32) — so a first-line match IS the claim, and on every
row the machine's first line equals gc's: gc's first lines from
`oracle.stderr` (od -c, the evidence file) are `a\0\001\t\r` on the three
`panic-controls` rows — the five control bytes before the LF, NUL included,
carried by L4's byte transport — `original` on `mixed-line`/`fake-trace`,
`forged` on `literal-continuation`. That is also the retired lane's
`Controls` role (§2.4 correction): covered now by L4's rows, so FR-33
RETIRES in the ledger (0 reds; FR-32's implementation site is on main).
Tracked figure 3654 = 3403 / 251 (3397 + 6; 257 − 6), re-derived from the
data rows by the header's awk; 0 PASS→non-PASS vs main; buckets 137 + 9 +
(24 + 1) + 7 + 73 = 251 (ledger §8, §8w's round-24 note). BUG-004's Cases
line loses the six L4 ids (its round-24 paragraph); BUG-105/BUG-106 carry a
dated note that their multi-line rows are green. `scripts/check-bugs.sh`
ok; `tools/reconcile-records` 0 HIGH at this tip.

**What this subsection does not contain:** the full `scripts/capped
scripts/ci --diff` at THIS clean committed tip — run by this worker after
this commit is written and reported verbatim to the coordinator in the
round-24 merge report (the tip is the gated tree; recording that tail in a
follow-up records-only commit, as §7.1 did, is the coordinator's call).
