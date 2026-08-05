# Known fidelity bugs — the SINGLE canonical index

A **fidelity bug** is a case where GoLean gives a *wrong* answer relative to real
Go: a wrong value, or a wrongly-*stuck* run on a construct we claim to support.
(A construct we don't model yet is not a bug — it must fail closed at the
frontend boundary as `frontend-export`, and is tracked as coverage, not here.)

This file is machine-cross-checked against the recorded differential **baseline**
(`baselines/native-full.tsv`) by `scripts/check-bugs.sh` (part of `scripts/ci`),
so a bug can neither rot in prose nor silently outlive its evidence:

1. every `- Cases:` id of an open `Pinned-by: differential` bug **exists in the
   baseline and is currently `FAIL`** — if a listed case now `PASS`es, the bug is
   fixed-but-not-closed (or the case no longer pins it), and the check fails;
2. every `Status: open` + `Pinned-by: differential` bug lists ≥1 case;
3. (warning) the check reports how many baseline **fidelity failures**
   (`stage=lean-observation` or `stage=differential` — wrong/stuck answers, not
   frontend-coverage gaps) are **not** yet explained by any bug entry — the
   omission surface to ratchet toward zero.

Bugs that cannot yet be mechanically pinned use `Pinned-by: none (<reason>)` and
are exempt from (1)/(2) — but still listed, so they cannot disappear.

**Entry format (keep parseable):** a `## BUG-NNN — <title>` heading, then
`- Status: open|fixed`, `- Pinned-by: differential|none (<reason>)`, and (for
differential-pinned) `- Cases: <id>, <id>, …` (baseline case ids), then prose.

---

## BUG-001 — struct-field / array-element WRITE lowers an address base as a value

- Status: fixed
- Closed: 2026-07-25 (W4 slice 1, branch `seq-coverage-scoping`)
- Fix: exactly where the 2026-07-19 diagnosis pointed — `emitAddressOf` in
  `tools/nativefrontend/emit.go` now emits ADDRESS chains (`a.b.c` →
  `fieldAddr(fieldAddr(ref a))`; pointer bases used as-is per auto-deref;
  array `index-addr` takes the array's address, slices stay by-value).
  GoCore needed zero changes, as predicted. All three pinned cases PASS
  (structs/copy-value, structs/pointer-field, arrays/arrays) plus 33 more
  in the same class (36 total, re-pin 2026-07-25). Fixing it exposed and
  fixed a second bug the fail-closed stuck had been masking:
  read-modify-write lvalues containing calls evaluated their address twice
  (`structs/selector-eval-once` — a WRONG ANSWER once reachable).
- Original status: open
- Pinned-by: differential
- Cases: structs/copy-value, structs/pointer-field, arrays/arrays
- Discovered: 2026-07-19 (directional audit, finding F1)

Writing through a struct field or array index — `b.n = 7`, `a[1] = …`,
`p.n = …` — fails closed at `lean-observation` with "expected address value, got
GoLean.GoValue.struct/array". Root cause is in the **frontend lowering**, not
GoCore: `tools/nativefrontend/emit.go` `fieldBase` (~736) and `emitAddressOf`'s
`SelectorExpr` case (~814) lower the base via a value-read (`.var`) where the
*address* path needs an address base (`.ref`/`.fieldAddr`). GoCore's
`valueAsLoc` correctly rejects the struct/array value and fails closed — so this
is a visible stuck, not a silent wrong answer, but the interpreter cannot perform
one of the most common Go mutations. On the north-star path (raft mutates struct
fields pervasively). GoCore already has the right primitives (`fieldAddr`,
`indexAddr`); the fix is in `emit.go`. Also: `docs/native-frontend-goal.md`
overclaims "field/index access" as working (true for reads, false for writes) —
correct it when the lowering is fixed. Tracked in `TODO.md` (F1).

## BUG-010 — TypeId keys are qualified by package NAME, not import PATH

- Status: open
- Pinned-by: differential
- Cases: interfaces/imported-package-name-collision
- Discovered: 2026-07-31 (final pre-merge adversarial audit of
  `quorum-pilot`, findings 4/7)

`qualifiedTypeName` (`tools/nativefrontend/emit.go`) builds every wire
`TypeId` from `obj.Pkg().Name()`. Go keys type identity on the import
PATH, so two packages that merely SHARE A NAME — `html/template` and
`text/template`, `math/rand` and `crypto/rand`, the many generated
`config`/`types`/`v1` packages — produced the SAME key, and `Ty.eqb`'s
`.defined a, .defined b => a == b` arm then called two unrelated Go types
identical. A single `package main` importing both stdlib templates was
enough:

    var p *ht.Template; var a any = p; _, ok := a.(*tt.Template)

Go answers `false`; the machine answered `true`. The panicking form is
worse — Go aborts with `interface conversion: interface {} is
*template.Template, not *template.Template (types from different
packages)`, its runtime message literally naming this class, and the
machine returned a value. No multi-package lowering was needed: an
imported named type needs no `TypeDef` to reach GoCore as `.defined`.

**v1 fail-closure (2026-07-31)**: the frontend COLLISION-CHECKS at the
one boundary constructor that builds the key
(`emitter.checkPackageNameCollisions`) and refuses the export when two
distinct import paths would share a qualifier — CLAUDE.md's "every
mangling strip happens at exactly one boundary constructor and
collision-checks", which `TypeId` (unlike `FuncId`) did not honour. The
pinned case is now an honest `frontend-export` refusal naming both paths.

The REAL fix is widening the key to `obj.Pkg().Path()`. It is deferred,
not forgotten: it re-keys every `TypeId` — every pinned lowering, every
`main.T(v)` panic rendering, every `TypeId.unqualified` observation — so
it belongs with the multi-package slice, scoped in
`docs/2026-07-30_quorum-extern-policy.md`. Escalate the moment
multi-package lowering is claimed.

## BUG-009 — an imported named type's METHOD SET is not on the wire, so interface satisfaction is UNKNOWN

- Status: open
- Pinned-by: differential
- Cases: interfaces/assert-imported-method-set/comma-ok, interfaces/assert-imported-method-set/panic-form
- Discovered: 2026-07-31 (final pre-merge adversarial audit of
  `quorum-pilot`, finding 8)

BUG-008's sibling in the other polarity, and the exact mirror of the
interim audit's finding 0 (vacuously TRUE satisfaction) — this one was
vacuously FALSE. `firstUnsatisfiedMethod?` derives satisfaction from
`state.methods`, which the frontend populates only for the ANALYZED
package. For an imported/stdlib named type the method table is empty and
no `TypeDef` exists, so `satisfiesMethodSig` answered `false` and
`dynamicHasEmbeddedFields` answered `false`, and the function returned a
DEFINITE `some name` — an answer derived from no information:

    var p *strings.Builder; var x any = p; _, ok := x.(fmt.Stringer)

`*strings.Builder` really does implement `fmt.Stringer`. Go gives
`ok == true`; the machine gave `false`. The panicking form `x.(fmt.Stringer)`
FABRICATED `interface conversion: *strings.Builder is not fmt.Stringer:
missing method String` on a program Go runs to completion. The sibling
function `tyUncomparable` was made three-valued on this same branch for
exactly this hazard ("Callers must fail CLOSED on `none`"); satisfaction
was not.

**Fail-closure (2026-07-31)**: `dynamicMethodSetRecorded` distinguishes
"the wire KNOWS this type, so an absent method really is absent" from
"this type was never declared, so the method set is UNKNOWN". Soundness
of the first half rests on a Go rule: methods can only be declared in
their type's own package, and the frontend emits a `TypeDef` for every
named type the analyzed package declares — so for a known `.defined`
name the recorded method set is COMPLETE. Non-`.defined` dynamic types
(basics, slices, maps, `**T`) can carry no methods in Go at all, so an
empty method set is correct for them; `*T` is known exactly when `T` is.
Only the definite-FALSE answer is guarded — finding a matching recorded
method is still sound.

Residual, recorded: a method declared for a package-local type in a
`_test.go` file is excluded by the frontend's `nonTestGoFile` filter,
which would leave a KNOWN type with an incomplete method set. No corpus
case has one (cases are single-file `main.go`), and the differential's
own oracle would not compile such a subject either.

The real fix is the same one BUG-008 names: emit declarations for
imported named types. The mechanism already exists for imported
INTERFACES (the interface-declaration pass); extending it to non-interface
named types is the owed sub-slice, and it closes both bugs at once.

## BUG-008 — imported named types have no declaration on the wire, so their comparability is UNKNOWN

- Status: open
- Pinned-by: differential
- Cases: maps/imported-named-key-unhashable
- Discovered: 2026-07-31 (pre-merge adversarial audit of the interfaces
  campaign, finding 11)

The frontend emits `TypeDef`s only for types declared in the analyzed
package, but it emits `{"kind":"named"}` for EVERY `*types.Named` — so any
imported/stdlib named type reaches GoCore as a `.defined` name the type
environment does not know. `tyUncomparable` used to answer `false`
("comparable") for such a name, which skipped Go's hash panic:
`m[sort.IntSlice{1,2}] = 1` inserted and returned len 1 where real Go
panics `runtime error: hash of unhashable type sort.IntSlice`. A silent
wrong answer on a program the tool accepted end to end.

`tyUncomparable` is now three-valued (`none` = unknown) and the map-key
hash precheck fails CLOSED on `none`, so the pinned case is an honest
`unsupported` instead. Neighbouring paths (default value, conversion,
same-type equality) already failed closed on unknown defined types; this
closes the boxing/hash hole. **Correction 2026-07-31 (final pre-merge
audit, finding 8): that enumeration was not exhaustive.** Interface
SATISFACTION — the path this branch added — did NOT fail closed on an
unknown defined type; it answered a definite `false`. Tracked separately
as BUG-009, closed the same way, and both are fixed for good by the same
owed sub-slice below. The real fix is emitting declarations for
imported named types — which is also what the interface-declaration pass
(finding 0's fix) now does for imported INTERFACES, so the mechanism
exists; extending it to imported non-interface named types is the owed
sub-slice.

## BUG-007 — method PROMOTION through embedded fields is unmodeled

- Status: fixed (2026-08-05, general-coverage slice 2 — the recorded fix
  direction landed: promotion is FLATTENED at emission
  (docs/2026-08-05_embedding-interfaces-design.md D1). Field promotion:
  Selection.Index() paths become field-get/deref chains (reads) and
  field-addr chains (writes/addresses). Method promotion: call sites and
  method values adjust the receiver through the hop path AT THAT MOMENT
  (evaluation order and capture moment pinned by
  embedding/promoted-nil-embedded-pointer/before-args and
  embedding/promoted-method-value/{snapshot,live}); dynamic dispatch and
  satisfaction go through synthesized forwarding WRAPPERS
  (synthesizePromotionWrappers, one per promoted method-set entry,
  receiver T or *T per Go's method-set asymmetry — mirroring gc's
  wrappers), so GoCore's method table stays flat and COMPLETE. The
  machine's over-approximate embedded-fields satisfaction fail-closure is
  retired under that wire contract (D2), with the definite-FALSE polarity
  pinned by embedding/promoted-ambiguous-not-satisfied and
  embedding/promoted-pointer-receiver-method-set/value-box.)
- Pinned-by: differential
- Cases: interfaces/embedded-interface-shadowing/interface-field-dispatch, interfaces/embedded-interface-shadowing/interface-field-nil-panic, interfaces/embedded-interface-shadowing/nil-pointer-method-promoted, interfaces/embedded-interface-shadowing/pointer-method-promoted, interfaces/error-idioms/promoted-method, interfaces/promoted-method-assert-ok, methods/embedded-interface-satisfaction, embedding/deep-promoted-method, embedding/embedded-method-promote, embedding/promoted-ambiguous-not-satisfied, embedding/promoted-method-value/live, embedding/promoted-method-value/snapshot, embedding/promoted-nil-embedded-pointer/before-args, embedding/promoted-nil-embedded-pointer/call, embedding/promoted-nil-embedded-pointer/nil-panic, embedding/promoted-pointer-receiver-method-set/pointer-box, embedding/promoted-pointer-receiver-method-set/value-box
- Discovered: 2026-07-30 (interfaces campaign — these cases were
  frontend-blocked before the campaign; the wrap/dispatch landing made
  the gap VISIBLE at the machine: `dynamic type main.T has no method m`)

Go promotes an embedded field's methods (and its interface's method
set) to the embedding struct, with receiver adjustment through the
field path — depth-first, shadowing by depth, ambiguity = compile
error. The machine's method table has only DECLARED methods, so a
promoted call finds no entry and dispatch fails stuck.

**Correction 2026-07-31 (pre-merge audit, finding 5): this entry used to
claim the gap was "fail-closed — never a wrong answer". That was FALSE on
the ASSERT path.** All eight originally pinned cases are dispatch/call
shapes; on `_, ok := any(Outer{…}).(I)` where `I` is satisfied via a
promoted method, the missing table entry made the method-SET check answer
`false`, and the comma-ok assert turned that into a silently WRONG boolean
(Go: true) with `status: ok` — no stuck, no unsupported. The machine now
fails CLOSED instead: a satisfaction check that would answer "unsatisfied"
on a struct (or pointer-to-struct) with EMBEDDED fields raises
`unsupported` naming the method and this bug, since promotion could supply
it. Detecting promotion soundly is the real fix, not the fail-closure;
until then `interfaces/promoted-method-assert-ok` is the added red pin, and
the fail-closure is deliberately over-approximate (it fires on any embedded
field, whether or not promotion would actually apply). The two pre-existing
`embedding/` untriaged ids are the same root cause and are folded in
here (untriaged 29 → 27 in the same commit). Fix direction (owed
sub-slice, recorded in
`docs/2026-07-30_interfaces-campaign-design.md`): frontend synthesizes
forwarding method entries for the promoted method set (receiver
adjustment = field access chain), which keeps GoCore's dispatch flat —
mirroring how gc actually compiles wrappers.

## BUG-006 — interface slots hold RAW values (no conversion wrap); guarded fail-closed

- Status: fixed (2026-07-30, interfaces campaign — the real
  conversion wrap landed: `wrapInterfaceConversion` emits
  `to-interface` at every former guard site; the machine boxes with the
  canonical dynamic `Ty`. `interfaces/typed-nil-pointer-compare` now
  PASSES (Go 111 = machine 111); the pinned case below flipped back
  FAIL→PASS with the wrap in place. Residue kept fail-closed: the two
  multi-value-assign tuple sites still refuse (deferred, message says
  so).)
- Pinned-by: differential
- Cases: comparisons/short-circuit/struct-skips-interface-panic
- Discovered: 2026-07-25/26 (slice 0d; scope completed by the pre-merge audit)

The lowering has no interface-conversion wrap: a concrete value flowing
into an interface-typed slot keeps its raw representation, which makes
typed-nil comparisons and cross-dynamic-type behavior silently WRONG
(`interfaces/typed-nil-pointer-compare`: Go 111, raw lowering 1). Until
the interfaces campaign lands the real wrap
(`docs/2026-07-25_arc-sequence.md` item 3), the frontend FAILS CLOSED at
every site a value implicitly converts to interface: assignment pairs,
var initializers, call arguments and packed variadic elements, append
elements, `new(expr)`, composite-literal fields/elements/keys/values,
the map-assign fast path, and `return` into interface results (the last
four were audit findings — the guard's first cut missed them). The
pinned case is the one PASS→FAIL this closed: a struct literal with an
interface field was accidentally green because Go's `==` short-circuits
on an earlier field before touching the raw payload — listed here per
the re-pin guard. The guard treats an untyped-nil source as exact
(a nil interface IS the raw nil).

## BUG-005 — map iteration snapshots ENTRIES, so it observes neither delete/clear nor value updates

- Status: open
- Pinned-by: differential
- Cases: maps/delete-during-range, maps/clear-during-range, maps/update-during-range
- Discovered: 2026-07-26 (pre-merge adversarial audit of `wrong-answers-builtins`)

`mapRange` snapshots the entry array once (the reshape's nondeterminism
design) and iterates the snapshot, so an entry removed during iteration
is still produced. The Go spec is explicit the other way: "If a map entry
that has not yet been reached is removed during iteration, the
corresponding iteration value will not be produced." The combination only
became REACHABLE when this arc landed `delete`/`clear` — the audit's
probe (`for k := range m { n++; delete all }`) gets one iteration from Go
and three from the machine, a silent wrong answer, now pinned red by the
two Cases. (Entries CREATED during iteration may or may not be produced,
so the snapshot's not-producing them is fine — removal is the defect.)

**Third symptom, added 2026-07-31 (final pre-merge audit, finding 1):
STALE VALUE READS.** The title and the paragraph above enumerate removal
and explicitly dismiss creation, and never mention UPDATE — so a reader
of this entry would not learn the symptom exists, and no case pinned it.
The snapshot freezes each entry's VALUE as well as its key, and
`Cont.mapIterK` hands both to `bindIterVars`, so a value written to an
already-present key from inside the loop is never observed:

    m := map[int]int{1: 10, 2: 10}
    sum := 0
    for _, v := range m { m[1] = 99; m[2] = 99; sum += v }

Go returns 109 (the second iteration reads the update); the machine
returns 20. Deterministic on BOTH sides — the two entries start equal and
end equal, so iteration order is irrelevant and the machine gives 20
under every choice stream — so this is a plain differential red, not a
nondet case: `maps/update-during-range`. The prescribed fix below already
covers it ("re-read values live"); this records the symptom and pins it.

The fix is real machine surgery: `Cont.mapIterK` must carry the map's
base location and the pick-next step must skip keys no longer present
(and re-read values live), which touches the nondeterministic rule pair
and `MachineSound` — scheduled as its own slice, not rushed into an
audit response.


COUPLING (sem-adequacy arc, 2026-08-04): the snapshot-time key/value
self-normalization check (`mapRangeSnapshotEntries`) and `MachineWf`'s
`itersNormalized` component are built ON the snapshot design this bug
schedules for replacement. The prescribed live-iteration fix
(`Cont.mapIterK` carrying the map's base loc, pick-next skipping absent
keys and re-reading values) must REPLAY the stream-obliviousness
analysis: the per-pick lookups it introduces must stay
choices-independent in ok-ness, and the wf typing component must move
from the snapshot to the live map cell. Do not land the BUG-005 surgery
without re-running `step_complete_any_wf`'s mapIterNext case.

## BUG-004 — panic abort rendering: boxing identity and defined-type payloads unmodeled

- Status: open
- Pinned-by: differential
- Cases: panic-recover/repanic-same-value-abort, panic-recover/panic-newline-abort, panic-recover/panic-defined-payload-methods/error, panic-recover/panic-defined-payload-methods/stringer
- Discovered: 2026-07-25 (pre-merge adversarial audit of `unwinding-arc`)

Go's abort output makes four demands the machine's value-level state
cannot meet, all found by audits and now FAILING CLOSED instead of
printing a wrong first line:

1. **`[recovered, repanicked]` collapse is eface IDENTITY** (a bitwise
   type-word + data-pointer compare in `preprintpanics`), not semantic
   equality. `panic(recover())` and re-panicked constant literals share a
   box and collapse; runtime-computed equal values do not (the arc's §A3
   probe was constant-folded — `"or"+"ig"` is one static eface). Unequal
   payloads certainly render ` [recovered]`; EQUAL payloads are
   undecidable without an allocation-identity model, so `renderPanicHead`
   returns none there. This turned `repanic-same-value-abort`
   PASS→FAIL (intentional, recorded here per the re-pin guard): the
   collapse it pins is real Go behavior our chain cannot decide.
2. **Defined-type payloads print qualified**: `panic(Code(7))` renders
   `main.Code(7)` via `printanycustomtype`. Root cause was deeper than
   the render arm: the lowering modeled a defined non-struct type as a
   GoCore ALIAS, erasing the identity before the machine saw it.
   **FIXED 2026-07-30 (interfaces campaign)**: `TypeDef.defined` keeps
   the identity, TypeId keys are package-qualified at the frontend, and
   `renderPanicPayload` renders the `main.Code(7)` form for
   int-underlying defined payloads (other underlyings stay closed).
   `panic-recover/panic-named-type-abort` flipped red→PASS with this.
   Items 1 (eface identity), 3 (multi-line payloads) and 4 (the
   `preprintpanics` rewrite) remain open; their pins stay red.
3. **Multi-line string payloads**: Go's first line stops at an embedded
   `\n` (`printindented`); `asciiString?` rejects the newline byte
   (`panic-newline-abort` is the red pin).
4. **`preprintpanics` REWRITES the payload before printing**: a payload
   implementing `error` prints `v.Error()`, one implementing
   `fmt.Stringer` prints `v.String()`, and `printanycustomtype`'s
   `main.T(v)` shape is reached only when the defined type has NEITHER.
   Item 2's fix shipped an UNCONDITIONAL `main.T(v)` arm, so
   `panic(Code(9))` with `func (Code) Error() string` rendered
   `main.payloadCode(9)` where Go prints `boom` — a fail-closed →
   wrong-answer regression (pre-merge audit 2026-07-31, finding 3).
   Rendering the rewritten form means CALLING a method at abort time,
   which the terminal rule cannot do, so the machine now checks the
   payload's method set (`Error() string` / `String() string`, the
   runtime's own two interfaces — checked directly, not through a wire
   interface declaration, since the rewrite applies whether or not the
   program mentions `error`) and returns `none` when either is present.
   `main.T(v)` survives for the method-less case
   (`panic-defined-payload-methods/plain` is the green pin; `/error` and
   `/stringer` are the red ones).

RECOVERING any of these payloads is fully supported — only the terminal
abort line is restricted. The remaining fixes, if ever needed, are an
allocation identity on boxed payloads (1), the multi-line `printindented`
shape (3), and a way to render the `preprintpanics` rewrite without
calling a method at abort time (4). (Corrected 2026-07-31, final
pre-merge audit finding 15: this sentence used to offer "a
package-qualification story (2)" as outstanding — item 2 SHIPPED on
2026-07-30, as the body says and the baseline's PASS on
`panic-recover/panic-named-type-abort` confirms — while omitting both
items that really are open. `scripts/check-bugs.sh` parses Status/Cases
and never prose, so no gate could catch it.)

## BUG-003 — for-clause per-iteration loop variables (Go 1.22) are not lowered

- Status: fixed
- Pinned-by: differential
- Cases: control-flow/for-loopvar-escape, functions/closure-loop-var-capture
- Discovered: 2026-07-25 (pre-merge adversarial audit of `seq-coverage-scoping`)
- Fixed: 2026-08-04 (control-flow slice stage 1,
  `docs/2026-08-04_control-flow-design.md`): `emitForPerIteration` desugars a
  captured-loop-var for-clause with a carrier POINTER — a fresh cell per
  iteration copied in at the TOP of the body, the carrier re-aimed at it, post
  running on the fresh cell — so `continue` needs no copy-back path and each
  iteration's captures see a distinct cell. Both pinned cases green.

A three-clause `for` declares its variable ONCE outside the loop in our
lowering, but Go ≥1.22 gives each iteration its own variable — a closure
escaping the iteration must see that iteration's value. With lambda-lifted
closures capturing by address, the shared cell was a **silent wrong answer**
(`for-loopvar-escape`: Go 01, we produced 22). The frontend now FAILS CLOSED
on any func literal capturing a for-clause loop variable, which also turned
`closure-loop-var-capture` red — its within-iteration capture was
observationally correct under the shared cell, but the cheap guard cannot
distinguish escaping from non-escaping captures (intentional red, recorded
here per the re-pin guard). Range loops are per-iteration already and are
unaffected (`range/range-loop-var-capture` stays green). The fix is a real
design item: the spec declares each subsequent iteration's variable before
the post statement, initialized from the previous one, and our
while-lowering cannot express that without a per-iteration copy-in that
survives `continue` (scoping note §8 has the re-entry sketch).

## BUG-002 — expression-step atomicity is wrong for concurrent Go (latent)

- Status: open
- Pinned-by: none (latent — `Rel` has no goroutine rules yet, so no
  concurrent claim is derivable today and no differential case can pin it;
  it becomes a live unsoundness the day concurrency lands without the fix)
- Discovered: 2026-07-22 (arc E loop-law review of the Goose divergence;
  classified a BUG, not a caveat, at user direction — concurrency is
  committed, so "coarser than Go" is wrong-by-default, not a scope note)

`ExprR` is a big-step premise relation inside statement steps, so a
compound expression reading several cells (`x == y`, `x == y+z`) is ONE
atomic `Rel` step. Real Go interleaves goroutines between the reads. If
goroutine rules are added over the current granularity, the model UNDER-
approximates real behaviors (misses torn reads), and Iris invariant
opening "around one atomic step" licenses reasoning across a multi-read
window — together enough to prove theorems false of real Go for racy
programs (e.g. invariant-mediated plain reads racing a two-step writer:
the model never shows the mixed pair a real schedule can produce). The
DRF escape ("coarse ≡ fine for race-free programs") is NOT self-enforcing:
the logic would verify such racy programs without complaint, so carrying
this granularity into a concurrent `Rel` violates fail-closed (a hidden
wrong answer, not a visible red).

**Consequence: the concurrency arc (F4) is BLOCKED on resolving this.**
Sequentially it is NOT a bug — GoCore `Expr` has no call constructor (the
frontend must lower calls out of expressions), so no sequential program
distinguishes the granularities; every current theorem is unaffected.

Fix paths (F4 decides; record the choice there):
1. **Refactor expression evaluation into the configuration language**
   (small-step expression machine): word-level granularity, `wp_bind` and
   `wp_atomic` become available (retiring two recorded workarounds), and
   the calls-in-expressions trigger in `Rel.lean` points the same way.
   The likely eventual fix; substantial correspondence rework.
2. **v1 confinement concurrency**: goroutine-confined heaps, ownership
   transferred only via channel externs (CSP-style) — no shared-memory
   invariants in v1, making expression granularity moot; matches the
   etcd-raft north star's actual architecture (single-threaded core,
   message passing). Defers (1) to a lock-free-code widening.
3. Law-discipline restriction (invariants openable only around
   single-access steps): fragile, easy to violate silently — likely
   reject.

See `docs/2026-07-22_arc-e-while-invariant.md` §2′ (the sequential
justification) and TODO.md F4 (the charter). This entry exists so the
constraint cannot rot in prose while goroutine machinery is built.

**Scope sharpening (2026-07-22, same day):** the full fix is bigger than
expressions. Even a small-step expression machine leaves `Step.assign`
bundling its reads and its write in one step — true word-level atomicity
requires decomposing statement steps into a HeapLang-style memory-op
machine, a major reshape of the trusted relation. This strengthens the
case for fix path 2 (confinement v1) and for making the F4 *decision*
early even while the *fix* is deferred: the rework cost of path 1 scales
with fragment size, so every Arc-E widening rung built before F4 decides
deepens the potential hole. Recommendation recorded: write the F4 note
before or alongside the next major fragment widening (structs/arrays),
not after.

**Direction pinned (2026-07-22, user):** fix path 2 (confinement-only
v1) is REJECTED as the target — it excludes most actually interesting
concurrent Go (mutex-protected shared state, sync/atomic, lock-free
patterns); "CSL-proofs-only is a trivial kind of concurrency." The target
is full shared-memory, fine-grained concurrency with the complete Iris
apparatus. Path 1 (the memory-op machine) is THE fix, and its scope is
larger than first recorded: the INTERPRETER is in scope too — it is the
executable side of the Choices split, and instantiating real schedules
requires preemption points at memory-op granularity (big-step `evalExpr`
cannot be preempted mid-expression; an earlier claim that the interpreter
survives unchanged was wrong). Alignment note: Go's sync/atomic is SC, so
an SC interleaving model at memory-op granularity honestly covers
atomics-based code; plain-access races remain out of verification scope
(UB-ish in Go — same position as Goose). Sequencing consequence: the
reshape is unavoidable and its cost scales with fragment size, so it
should be the next MAJOR arc after the current rung — BEFORE the
structs/arrays widening, which would otherwise be built twice.

**Reshape R1+R2 landed (2026-07-23, branch `reshape-smallstep`, stages
S0–S4 of `docs/2026-07-23_reshape-r1r2-machine-design.md`):** the
structural root is fixed. Expression evaluation is in the configuration
language (`GoLean/GoCore/Machine.lean`: `evalE`/`retV` configs, generic
`strictK` operand frames), loads and stores are individual `Step` rules,
and `Step.assign` no longer bundles reads with its write (target address,
RHS evaluation, and the store are separate steps around machine-evaluated
operands). The interpreter is the relation instantiated (`stepFn`,
iterated fuel-bounded), so preemption points exist at memory-op
granularity on the executable side too. The big-step rules (`ExprR`, old
statement rules, `Eval` cluster, T1/T2 correspondence) are DELETED per the
F4 §2 directive — validated by ZERO DRIFT on the full 718-case
differential plus 40/40 eval tests. Still open before this bug CLOSES
(R4): goroutine rules + scheduler `Choices`, and the granularity-ledger
re-audit of multi-cell apply steps (`appendSlice` spill, `copySlice`) —
coarse-but-recorded, fine sequentially, must not silently enter
concurrency claims.

## BUG-011 — anonymous `struct{}{}` literal stuck at named empty-struct types

- Status: fixed (2026-08-05, general-coverage slice 2 — corpus case FIRST
  (classified red, all six subjects), then the assignability-aware
  normalization: `emptyStructAssignable` (Ops.lean) retags the canonical
  unnamed `struct{}` value at a defined empty-underlying target (and the
  reverse direction) in `normalizeStructValueWith`, plus the same escape
  in `valueEqFuel`'s struct-tag checks for the mixed-operand comparison.
  Metatheory in the same commit: `normalizeStructValueWith_locSup`
  (StateWf) and the congruence/default-value lemmas (MachineSound) gained
  the escape branch. Design note D4,
  `docs/2026-08-05_embedding-interfaces-design.md`.)
- Pinned-by: differential
- Cases: structs/empty-struct-literal-at-named-type/var-init, structs/empty-struct-literal-at-named-type/param, structs/empty-struct-literal-at-named-type/return, structs/empty-struct-literal-at-named-type/map-store, structs/empty-struct-literal-at-named-type/reverse, structs/empty-struct-literal-at-named-type/compare
- Discovered: 2026-08-04 (sem-adequacy notions sub-branch audit, semantics
  reviewer probing beyond the diff; verifier reproduced independently)

`normalizeStructValueWith` (Ops.lean, the struct arm of value
normalization) compares the VALUE's carried `TypeId` against the target
defined type with raw disequality — Go type IDENTITY — where Go
assignment applies ASSIGNABILITY: an anonymous `struct{}{}` composite
literal is assignable to any defined type whose underlying type is
`struct{}`, so `var x T = struct{}{}` succeeds in Go and goes `.stuck`
here ("struct value type mismatch: expected main.T, got struct{}").
Same class as the conversion/assignability distinctions the interfaces
campaign handled elsewhere; fail-closed direction (visible red, no wrong
answer). Fix shape: assignability-aware normalization for identical
underlying struct types (or frontend-side retagging of untyped
composite literals at their assignment type); guardrail corpus case
FIRST per the standing rule.
