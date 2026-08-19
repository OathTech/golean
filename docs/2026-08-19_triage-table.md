# The bug-fix arc triage table — every open bug, every baseline red

Slice 5 of the arc chartered in `docs/2026-08-19_bugfix-arc-charter.md`.
Linked from `docs/bugfix-arc-log.md` §slice 5, which carries the slice's
judgment calls and gate records; this file is the TABLE itself, split out
because it does not fit in the log without burying it.

**The arc's law** (charter, user's formulation): *all bugs and
differentials are killed unless there is a profound reason they exist*.
Every row below lands in **exactly one** of three categories — there is
no fourth, and "known issue" is not a state this arc may end in:

- **(a) FIX IN THIS ARC** — cheap and diagnosed. Either already pulled
  into slices 1–4, or executed here as a mini-slice.
- **(b) FRONTIER** — red because a language feature is genuinely
  unsupported. The row names the feature, the refusal point (file:line +
  the error string as it appears in the source) and the spec anchor.
  These rows are slice 6's input; slice 5 does NOT build suites.
- **(c) PROFOUND-REASON PIN** — latitude (spec-open, implementation-
  dependent, optimizer-dependent) or impossibility. Each argument is
  written FRESH below to be judged; the ledger cross-reference is
  evidence, not a grandfather clause. **The (c) list is ratified by the
  user at the arc gate — profound-ness is the user's call, not ours.**

## 0. The denominators, re-derived at `0c21aa21`

The charter's counts were stated "at charter time; re-derive at
execution". Re-derived:

| quantity | charter | actual at `0c21aa21` | derivation |
| --- | --- | --- | --- |
| open `docs/BUGS.md` entries | "13" | **9** | `awk '/^## BUG-/{id=$2} /^- Status: open/{print id}' docs/BUGS.md` |
| baseline reds | 136 | **138** | `awk -F'\t' '$1=="FAIL"' baselines/native-full.tsv \| wc -l` |
| · differential | 12 | **7** | same, `$3` |
| · frontend-export | 87 | **92** | |
| · lean-observation | 35 | **37** | |
| · go-run | 1 | **1** | |
| · nondet | 1 | **1** | |

**The charter's "13 open" was never right.** At the charter commit
`df3adbfc` the open set was already 11 (`git show
df3adbfc:docs/BUGS.md`): BUG-002, 004, 005, 008, 014, 041, 056, 057,
058, 059, 061. Slices 1–2 closed 057 and 058, leaving **9**. Recorded
because the DONE conjunction counts "13/13"; the honest conjunction is
9/9 open entries + 138/138 baseline reds.

The 138 reds are grouped **by root cause**, not padded into 138 one-line
clones. The grouping is mechanical (exact refusal string, normalized over
type and variable names) and reproducible from
`artifacts/coverage/latest.tsv`, which is byte-consistent with the
tracked baseline at this tip (verified: the FAIL id+stage sets are
identical).

**The arithmetic that must close, and does:** the 9 open entries pin 20
baseline reds between them (BUG-002 pins none — it is `Pinned-by: none`,
latent). 138 − 20 = 118 reds are not on any open entry's `Cases:` line;
of those, 92 are `frontend-export` (outside the fidelity stages by
construction) and 26 are fidelity-stage. 45 fidelity reds total
(7 differential + 37 lean-observation + 1 nondet) − 20 explained = **25**,
which is exactly `scripts/check-bugs.sh --list` and exactly
`baselines/untriaged-ids` — the "untriaged-25". Three independent
derivations of the same 25; §5 is their cross-check.

## 1. The 9 open `docs/BUGS.md` entries

| bug | subject | reds pinned | category | disposition |
| --- | --- | --- | --- | --- |
| BUG-002 | expression-step atomicity wrong for concurrent Go (latent) | 0 (`Pinned-by: none`) | **(c)** | C-BUG-002 below |
| BUG-004 | panic abort rendering: eface boxing identity, multi-line payloads, `preprintpanics` rewrite | 4 | **(c)** | C-BUG-004 below |
| BUG-005 | map `range` snapshots entries (delete/clear/update invisible; race-invisible) | 5 | **(a)** | slice 4 — memo delivered, USER GATE open |
| BUG-008 | imported named types carry no wire declaration ⇒ comparability UNKNOWN | 1 | **(b)** | frontier: imported-type declaration emission |
| BUG-014 | untyped nil at defined-slice/map literal elements stays a raw nil | 2 | **(b)** | frontier: defined-type-aware typed nil (GoCore) |
| BUG-041 | race footprint over-approximation: value-path composite reads are whole-cell | 1 | **(b)** | frontier: path-precise element reads |
| BUG-056 | `&*p` on a nil pointer collapses instead of panicking | 5 | **(a)** | slice 3 — memo delivered, USER GATE open |
| BUG-059 | panic messages render multi-segment TypeId qualifiers as the import PATH | 1 | **(c)** | C-BUG-059 below |
| BUG-061 | the pruning rule under-approximates `staticinit` | 1 | **(c)** | C-BUG-061 below |

Category rationale for the four (b) rows (the (a) and (c) rows are
argued in §3 and §4):

- **BUG-008** — the fix the entry itself names is "emitting declarations
  for imported named types", and the mechanism already exists for
  imported INTERFACES. That is a frontend capability that does not exist
  yet, sized like a feature, not a patch: every imported named type in
  every analyzed package gains a `TypeDef`, which changes the wire for
  programs far outside the pinned case. Frontier, raft-path relevant
  (raft imports named types). Refusal point: `tyUncomparable`'s
  three-valued `none` arm, `GoLean/GoCore/Ops.lean`; observable error
  `map key hashability for unknown defined type sort.IntSlice`.
- **BUG-014** — the entry states the fix is a GoCore change (the
  nil-literal arm must resolve `.defined` targets through their
  underlying, or a defined-type-aware typed-nil representation) plus a
  frontend follow-on. GoCore-touching ⇒ inside this arc it would need
  the slice-3/4 class of user gate; and it is a missing capability
  (typed nil at defined composite types), not a mis-wired one. Frontier.
- **BUG-041** — the entry's own "fix shape" is "provenance-carrying array
  values or frontend address-based element reads (indexAddr+deref)" — a
  frontend/machine movement with its own guardrails, explicitly "not a
  detector patch". Frontier. Note the direction is fail-closed
  (over-REFUSAL of a race-free program, never a missed race), so it is
  never a silent wrong answer.
- **BUG-005 / BUG-056** are (a) and not (b) precisely because slices 3–4
  did the diagnosis work: both have delivered design memos with a
  recommended mechanism and a predicted flip set. They are (a)
  **conditional on the user gates the charter designed**, and the
  charter's own DONE clause 3/4 accepts a recorded gate outcome as a
  legitimate end state. If Mike declines both mechanisms, those 10 reds
  must be re-argued as (c) at that moment — they do NOT silently become
  frontier.

## 2. The 138 baseline reds, grouped by root cause (45 groups)

Every group carries: the cause, the refusal point as `file:line` plus the
error string **as it appears in the source**, the spec anchor, the
category, and (for (b)) the feature name slice 6's ledger will use.
Line numbers are at `0c21aa21` unless a mini-slice moved them.

### 2.1 `differential` — 7 reds, 4 groups

| # | cause | ids | cat |
| --- | --- | --- | --- |
| D1 | hidden-dependency initialization order: go/types' `InitOrder` and gc's `initorder` are two DIFFERENT conforming analyses | `init/hidden-dep-order` | **(c)** C1 |
| D2 | map `range` snapshots entries (BUG-005): delete/clear/update during iteration invisible | `maps/{clear,delete,delete-unreached,update}-during-range` | **(a)** slice 4 |
| D3 | `sourceHasInitWork` under-approximates gc's `staticinit` pruning (BUG-061) | `multipkg/init-order-staticinit/seq` | **(c)** C2 |
| D4 | panic messages print `TypeId.key` verbatim (import PATH) where gc prints the package NAME (BUG-059) | `multipkg/same-name-identity-panic` | **(c)** C3 |

### 2.2 `lean-observation` (37) + `go-run` (1) + `nondet` (1) — 39 reds, 17 groups

The charter called this "the least-understood block". It decomposes
cleanly: **14** of the 39 are already on an open entry's `Cases:` line
(BUG-004/005/008/014/041/056), and the other **25** are the tracked
untriaged set (§5). Nothing here is mysterious once the refusal string is
traced to its source line — which is the point of doing it.

| # | cause | refusal point + string | spec | ids | cat |
| --- | --- | --- | --- | --- | --- |
| L1 | no conversion arm for `[]rune(s)` / `string([]rune)`: the frontend classifier routes only `[]byte`↔`string` and `string(int)` to ops (`emit.go:5947-5962`), the rest falls to the machine's catch-all | `GoCore/Ops.lean:1164` — `unsupported s!"conversion to {repr other}"` | `spec#Conversions_to_and_from_a_string_type` | `spec-examples-decl/string-from-runes`, `spec-examples-lexical/string-to-runes`, `strings/{defined-slice-string-conversion,nil-slice-string-conversion,rune-invalid-values,rune-slice-conversion,rune-slice-to-string-copy,rune-string-conversion,string-to-rune-copy}` (9) | **(a)** GoCore-GATED |
| L2a | no `.array`-target arm for a `.slice` operand — the length-check panic path | `GoCore/Ops.lean:1164` (same catch-all) | `spec#Conversions_from_slice_to_array_or_array_pointer` | `spec-examples-decl/slice-to-array/{short-array,short-array-ptr,nil-to-longer-ptr}` (3) | **(a)** GoCore-GATED |
| L2b | the SUCCEEDING array-pointer form must alias the slice's backing segment; `Loc` (base/field/index) has no subarray-view constructor, so a slice with `offset≠0` or `cap>n` is unrepresentable as an array pointer | same | same | `spec-examples-decl/slice-to-array/ok-forms` (1) | **(b)** feature: array-pointer views over slice storage |
| L3 | the `min`/`max` fold refuses any float operand rather than getting NaN and ±0 silently wrong through `valueLess` | `GoCore/Machine.lean:478` / `:487` — `unsupported "min builtin over float operands"` | `spec#Min_and_max` | `spec-examples-stmt/min-max-float-specials/{infinities,nan,signed-zero}` (3) | **(a)** GoCore-GATED |
| L4 | out-of-range / NaN float→int conversion is spec-declared implementation-dependent; the machine refuses rather than pick a member | `GoCore/Ops.lean:1058-1061` — `unsupported "float-to-int conversion out of range/NaN (implementation-dependent in Go)"` | `spec#Conversions` (numeric-types clause) | `floats/to-int-out-of-range/{nan,range}` (2) | **(c)** C5 |
| L5 | `.indexGet` has no `.addr` auto-deref arm (the WRITE path got one at BUG-038; the read path did not) | `GoCore/Machine.lean:396` — `stuck s!"expected array, slice, or string value for index access, got {repr other}"` | `spec#Index_expressions` ("for `a` of pointer to array type, `a[x]` is shorthand for `(*a)[x]`") | `arrays/pointer-array` (1) | **(a)** GoCore-GATED |
| L6 | same missing-arm class for `.nil`: gc raises the recoverable nil-deref panic, we go stuck. BUG-038's entry NAMES this case as the deferred read-position sibling | `GoCore/Machine.lean:396` (same string, `got GoLean.GoValue.nil`) | `spec#Index_expressions` + `spec#Run_time_panics` | `pointers/nil-array-index-panic` (1) | **(a)** GoCore-GATED |
| L7 | `(*B)(a)` passes the pointer through but the heap cell keeps its mint tag, and field access checks the NOMINAL stored tag — while the spec says struct tags are ignored for conversion identity (and the wire already strips tags, so the two TypeIds have identical `FieldDef` lists) | `GoCore/Ops.lean:1003` / `:1031`, `GoCore/Machine.lean:354` — `stuck s!"expected struct {typeId.key}, got struct {actualType.key}"` | `spec#Conversions` (struct-tag clause) | `structs/tag-pointer-conversion` (1) | **(a)** GoCore-GATED |
| L8 | package init runs on the SEQUENTIAL driver; goroutine spawn is architecturally a pool step | `GoCore/StepFn.lean:513-514`, `:520-521` — `.unsupported "go spawn outside the thread pool (goroutine spawn is a pool step; go during package init is refused this slice)"` | `spec#Package_initialization` ("an init function may launch other goroutines") | `goroutines/spawn-in-init/in-init` (1) | **(b)** feature: `$pkginit` on the thread pool |
| L9 | select↔select rendezvous (the offer/retract protocol) is not built; only select↔plain-chan pairing is | `GoCore/Multi.lean:665-666`, `:674-675` — `.unsupported "select-with-select rendezvous (unmodeled this slice)"` | `spec#Select_statements` | `channels/select-select/core` (lean-observation), `channels/select-select/beside-loop` (nondet) (2) | **(b)** feature: select-to-select rendezvous |
| L10 | `go` of a nil func value: gc raises an unrecoverable runtime FATAL in the spawner, the machine refuses — **and the case's `expected_status panic` encodes a harness limitation that no longer exists** | `GoCore/Multi.lean:302-303` — `.unsupported "go of nil func value (gc raises an unrecoverable runtime fatal at the spawn; the fatal class is unmodeled this slice)"` | `spec#Go_statements` | `goroutines/spawn-edge/nil-func-fatal` (1, stage `go-run`) | **(a)** GoCore-GATED |
| L11 | BUG-056: the `&`-of-`*` composition collapses before the nil-indirection check fires | frontend wire (`&*p` and `&(*p)` are byte-identical) | `spec#Address_operators` | `spec-examples-decl/address-op-nil-indirection/{addr-deref-nil,addr-deref-nil-paren}`, `spec-examples-decl/addr-deref-nil-matrix/{two-deref-inner-nil,deref-arg,deref-call}` (5) | **(a)** slice 3 |
| L12 | BUG-004: eface boxing IDENTITY, multi-line payloads, and `preprintpanics`' method-rewrite are not decidable from the machine's value-level state — `renderPanicHead` returns none | `GoCore/Ops.lean` (`renderPanicPayload` / `renderPanicHead`) — `unsupported "panic abort rendering for payload …"` | `spec#Handling_panics` (+ gc runtime, spec-silent) | `panic-recover/{repanic-same-value-abort,panic-newline-abort,panic-defined-payload-methods/error,panic-defined-payload-methods/stringer}` (4) | **(c)** C4 |
| L13 | BUG-014: the nil-literal arm rejects `.defined` targets, so a defined-slice/map map-literal element stores a RAW `.nil` that goes unsupported at `len` | `GoCore` nil-literal arm — `unsupported "len for non-array/slice/map value GoLean.GoValue.nil"` at use | `spec#Composite_literals` + `spec#The_zero_value` | `maps/nil-literal-values/{defined-map-element,defined-slice-element}` (2) | **(b)** feature: defined-type-aware typed nil |
| L14 | BUG-008: imported named types get no wire `TypeDef`, so `tyUncomparable` answers `none` and the map-key hash precheck fails closed | `GoCore/Ops.lean` (`tyUncomparable`) — `unsupported "map key hashability for unknown defined type sort.IntSlice"` | `spec#Comparison_operators` (map key comparability) | `maps/imported-named-key-unhashable` (1) | **(b)** feature: declarations for imported named types |
| L15 | BUG-041: `stepAccesses` records a WHOLE-CELL read for a materialized composite, so a value-path array-element read over-approximates and REFUSES a `-race`-green program | `GoCore/Race.lean` (inventory O1) — observation `status: race` where `ok` is expected | mem model (`mem#restrictions`) | `race/free/array-read-write` (1) | **(b)** feature: path-precise element reads |
| L16 | BUG-005's fourth symptom: the snapshot range performs no per-iteration user-memory read, so a concurrent map write is invisible to the S3 detector | `GoCore/Race.lean` (inventory U1) — observation `ok` where `race` is expected | `mem#restrictions` + `spec#For_range` | `race/negative/map-range-iter` (1) | **(a)** slice 4 |

### 2.3 `frontend-export` — 92 reds, 24 groups

Every one is a refusal at the frontend boundary, i.e. fail-closed by
construction. This is the expected home of the frontier, and it is: 20 of
the 24 groups (77 of the 92 reds) are **(b)**.

| # | feature | refusal point + string | spec | ids | cat |
| --- | --- | --- | --- | --- | --- |
| F1 | complex numbers (`complex64/128`, imaginary literals, complex constants, `real`/`imag`/`complex`) | `wire.go:545` — `unsup("basic type %s", b)` | `spec#Numeric_types`, `spec#Imaginary_literals`, `spec#Complex_numbers`, `spec#Constants` | `complex/*` (21), `builtins/real-imag`, `constants/{default-types,typed-complex-binary,untyped-complex-context}`, `new/new-expr/untyped-defaults`, `spec-examples-decl/const-complex/untyped`, `spec-examples-lexical/imaginary-literals` (27) | **(b)** GoCore-touching; **not on the raft path** (zero `complex` in `deps/raft`) |
| F2 | range-over-func iterators (Go 1.23) | `emit.go:3209` — `unsup("range over %s", e.goTypeOf(rs.X))` | `spec#For_range` (function rows) | `range/range-func-basic`, `range/range-func-break`, `range/range-func-edge/*` (9) | **(b)** frontend desugar + loop-exit protocol; not raft-path |
| F3 | anonymous non-empty struct types as first-class types | `wire.go:495` — `unsup("anonymous non-empty struct type %s", ty)` | `spec#Struct_types` (+ `spec#Conversions` for the tag rows) | `generics/type-aliases/struct-literal`, `spec-examples-decl/{struct-tag-conversion,type-definitions-distinct}`, `spec-examples-stmt/{struct-tags,type-unify-struct-array}`, `structs/{tag-nested-conversion,tag-unnamed-conversion}` (7) | **(b)** structural TypeIds — an identity-design change; not raft-path (`chan struct{}` is the empty struct, already supported) |
| F4 | implicit boxing of tuple COMPONENTS into interface-typed targets | `emit.go:2225`, `:2529`, `:2601` — `unsup("implicit interface conversion in multi-value assignment (interfaces campaign, deferred)")` | `spec#Assignment_statements` + `spec#Assignability`; the shape is written verbatim in `spec#Type_assertions` | `imported-goose/unittest/interfaces`, `spec-examples-decl/assert-comma-ok`, `spec-examples-decl/var-comma-ok-matrix/{assert-typed-iface,index-typed-iface,recv-typed-iface,tuple-call-iface}` (6) | **(b)** a recorded interfaces-campaign deferral; three of the six were pinned red DELIBERATELY by slice 2 so the BUG-057 reroute could not relax into a silent unboxed store |
| F5 | `goto` over a declaration whose per-execution cell identity is observable (captured / address-taken / array-storage-sliced / pointer-method receiver) | `emit.go:1459`, `:1474`, `:1476`, `:1478` — `unsup("goto function hoists …")` | `spec#Goto_statements` (the jumps are LEGAL; the refusal is our hoisting lowering's honesty check — a backward jump gives Go a FRESH cell, the hoisted lowering one shared cell) | `control-flow/goto-backward-{array-slice,capture,elem-addr,field-addr,nested-recv}` (5) | **(b)** fresh-cell-per-execution goto lowering; not raft-path (no `goto` in `deps/raft`) |
| F6 | map elements as targets in a MULTI-assignment (`m[0], m[1] = m[1], m[0]`) | `emit.go:5125` — `unsup("map element as assignment target outside a single assignment")` | `spec#Assignment_statements` (two-phase) + `spec#Address_operators` (map elements not addressable) | `imported-goose/semantics/multiple-assign/multiple-assign-to-map`, `maps/{tuple-assign-key-eval,tuple-map-expr-targets,tuple-rhs-before-target-write,tuple-swap-values}` (5) | **(a)** mini-slice A3, QUEUED |
| F7 | method expressions in CALL position (`T.Mv(t, 7)`, `(*T).Mp(&t, .5)`) | `emit.go:6567` — `unsup("selector call %s is not a method value", sel.Sel.Name)` | `spec#Method_expressions` | `spec-examples-lexical/method-expressions/{pointer-receiver-expr,value-receiver-expr}`, `spec-examples-stmt/method-expr-five-forms` (3) | **(a)** mini-slice A2 — **FIXED in this slice** |
| F8 | the derived pointer-receiver function for a VALUE-receiver method (`(*T).Mv` deref adapter) | `emit.go:4919` — `unsup("method expression (*%s).%s over a value-receiver method (deref adapter not modeled)")` | `spec#Method_expressions` | `spec-examples-decl/method-expressions`, `spec-examples-lexical/method-expressions/derived-pointer-receiver-expr` (2) | **(b)** a SYNTHESIZED wire adapter, not routing — distinct from F7 |
| F9 | promoted/embedded and expression-position sync-primitive calls | `emit.go:6541` — `unsup("sync.%s.%s outside a direct statement/defer position (promoted, embedded, and expression-position sync ops are unmodeled)")` | n/a (sync stdlib surface; design note §9) | `sync/escapes/{defer-embedded,promoted}`, `sync/out-of-scope-trylock/trylock-uncontended` (3) | **(b)** — **the highest-priority raft-path frontier row in this table**: `deps/raft/storage.go:108` embeds `sync.Mutex` in `MemoryStorage` and `storage.go:139,147` are exactly the promoted-`defer ms.Unlock()` shape. TryLock is separately deferred to the atomics arc (its spin-wait termination class is a FairStream question) |
| F10 | sync methods through interface dispatch (`sync.Locker`, user interfaces) | stub at `emit.go:4679-4681`; quarantined by `NativeToIR.lean`'s `decodeFunc` — `"sync-primitive method sync.X.Y through interface dispatch (declaration-only stub: satisfaction answers; only direct statement/defer-position calls are modeled)"` | n/a (sync surface; design note §12) | `sync/iface-dispatch/{locker-box-dispatch,mutex-user-iface,wg-user-iface}` (3) | **(b)**; note the pin is itself an audit fix — before the stub pass this shape ESCAPED to runtime `stuck` |
| F11 | sync methods as method values / go-statement callees | `emit.go:4739` — `unsup("sync.%s.%s as a method value (only direct statement/defer-position sync ops are modeled)")` | `spec#Method_values` for the shape | `sync/escapes/{go-stmt,method-value}` (2) | **(b)** same family (audit fix round F4; previously a runtime `stuck`) |
| F12 | composite-literal construction of a sync primitive (`&sync.Mutex{}`) | `emit.go:5222` — `unsup("composite-literal construction of sync.%s (out of scope: `var` declarations and new() are the modeled construction surface)")` | `spec#Composite_literals` for the form | `sync/composite-literal/{mutex-addr-lit,waitgroup-value-lit}` (2) | **(b)** — see the JUDGMENT in §3 for why this near-(a) row is NOT taken |
| F13 | `sync.Cond` | `wire.go:385` — `unsup("sync.%s (only Mutex/RWMutex/WaitGroup/Once are modeled)")` | n/a (sync stdlib; design note §9 D4) | `sync/out-of-scope-cond/cond-signal-no-waiter` (1) | **(b)** GoCore + a genuine wakeup-envelope question |
| F14 | `copy` / `recover` in EXPRESSION-STATEMENT position | `emit.go` ExprStmt builtin switch — `unsup("builtin %s in statement position", id.Name)` | `spec#Expression_statements` (the not-permitted list excludes both) | `imported-goose/{semantics,unittest}/copy/copy-simple`, `goroutines/spawn-edge/child-recovers` (3) | **(a)** mini-slice A1 — **FIXED in this slice**; raft-path (`deps/raft/util.go`, `tracker/inflights.go`) |
| F15 | `go` with a BUILTIN callee (`go close(ch)`) | `emit.go:1899` — `unsup("go of builtin %s", id.Name)` | `spec#Go_statements` | `goroutines/go-builtin/close` (1) | **(b)** the faithful desugar needs a synthesized wire function; one row does not carry it |
| F16 | unnamed CHANNEL types as generic type arguments | `mono.go:964` — `unsup("type argument outside the mangling surface: %T (%s)", t, t)` | `spec#Instantiations` | `generics/chan-type-arg/first` (1) | **(a)** mini-slice A4, QUEUED |
| F17 | FUNCTION-LOCAL defined types as generic type arguments | `mono.go:903` — `unsup("function-local defined type %s as a type argument (gc renders these with a compiler-internal unique suffix, e.g. %s·1 — refused rather than guessed)")` | `spec#Instantiations` + `spec#Type_definitions` | `generics/local-type-argument` (1) | **(c)** C6 |
| F18 | `slices.Sort` at a non-integer element type | `emit.go:6909` — `unsup("slices.Sort at non-integer element type %s", sl.Elem())` | n/a (quorum-pilot extern policy) | `slices/slices-sort-non-integer-refusal` (1) | **(b)** — and a DELIBERATE red pin (pre-merge audit 2026-07-31 finding 12): it must stay refused until a real string-ordering model lands, so a silent widening shows as baseline drift |
| F19 | stdlib package surface beyond the `strings.Fields` shim (`fmt`, `math`, …) | `emit.go:6567` (`fmt.Sprintf` reaches the same "not a method value" string) and `emit.go:4718` — `unsup("field selector on anonymous struct type %s", recvType)` with `%s` = `invalid type` | `spec#Qualified_identifiers` (the construct is fine; the gap is stdlib coverage) | `spec-examples-decl/timezone-stringer`, `spec-examples-lexical/qualified-identifier` (2) | **(b)** — **raft-path in aggregate**: `deps/raft` non-test uses `fmt`, `math`, `strings`, `errors`, `slices`, `math/rand`. See §3's honesty note: both refusal STRINGS misattribute a stdlib gap |
| F20 | assignment-form range clause with non-identifier targets (`for i, x[i] = range x`) | `emit.go:3043` — `unsup("range assignment to non-identifier target (operands evaluate per iteration)")` | `spec#For_range` (assignment form) | `spec-examples-decl/assign-tuple-order/range-assign` (1) | **(b)** the range lowering is load-bearing and the case pins subtle old-`i` indexing; one row does not justify reshaping it this arc |
| F21 | anonymous non-empty struct as a generic TYPE ARGUMENT | `mono.go:960` — `unsup("anonymous non-empty struct as a type argument (%s)", ty)` | `spec#Satisfying_a_type_constraint` (the spec's own `struct{f any}`-satisfies-`comparable` row) + `spec#Instantiations` | `spec-examples-decl/compile-only-forms` (1) | **(b)** stacks on F3 — same ledger family, kept as its type-argument sub-row |
| F22 | the shadow-capture pre-bind hoists a TUPLE-typed comma-ok RHS whole (`var v, ok = m[v]`, initializer reading the OUTER `v`) | causing hoist `emit.go:2355`; refusal `wire.go:497` — `unsup("type %T (%s)", t, t)` (`*types.Tuple ((int, bool))`) | `spec#Declarations_and_scope` + `spec#Index_expressions` | `spec-examples-decl/var-comma-ok-matrix/shadow-capture` (1) | **(a)** mini-slice A5, QUEUED — a BUG-057-family edge, and this row was written as its guardrail |
| F23 | `len`/`cap` of a potentially-panicking operand inside a receive-bearing FUNCTION (BUG-032's fail-closed resolution; `fnHasRecv` is function-scoped since BUG-026) | `emit.go:6726` — `unsup("%s of a potentially-panicking operand in a receive-bearing function (hoisting would reorder its panic — BUG-032)")`; predicate `panicFreeOperand` `emit.go:7522-7548`; flag `fnHasRecv` `wire.go:87` | `spec#Order_of_evaluation` | `channels/recv-order/{dead-recv-len-operand,dead-recv-len-embedded}`, `bools/short-circuit-funclit/{e6-recv-len-in-sc,e6-recv-len-outside}` (4) | **(a)** mini-slice A6, QUEUED — see §3, and the NEW divergence it uncovered |
| F24 | a live channel RECEIVE directly in a short-circuit operand | `emit.go:7578` — `unsup("channel receive in %s (would change evaluation order)", …)` | `spec#Order_of_evaluation` (binary logical operations are ordered) | `spec-examples-stmt/operator-precedence/mixed-chan` (1) | **(b)** feature: extend the E3 conditional normalization to `hoistChanRecv`; E3 scoped it out explicitly and owes guardrail rows first |

## 3. Category (a) — the fix set

**46 baseline reds are category (a)** (derivation in §6). They split four
ways by what gates them, and the split is a fact about the charter's own
hard boundary ("No GoCore/semantic-core change without the slice-3/slice-4
gates — those are the arc's designed pauses"), not a preference:

### 3.1 Executed in this slice (frontend-only, no gate needed)

| mini-slice | subject | reds flipped | new ids |
| --- | --- | --- | --- |
| **A1** | `copy`/`recover` in expression-statement position (F14) | 3 | 7 (the edge enumeration, all PASS) |
| **A2** | method expressions in CALL position (F7) | 3 | 5 (the five paths `emitSelector`'s MethodExpr arm distinguishes, all PASS) |

Both recorded in `docs/bugfix-arc-log.md` §slice 5 with their judgment
calls, their guardrails-first colors and their gates (`scripts/ci --diff`
→ PASS at each). Commits `1ca434b2` and `357b7297`; the tip baseline is
2179 cases / 2047 PASS / **132 FAIL**.

**A2's drift is evidence for a triage split.** The four
"selector call X is not a method value" reds were ONE group by error
STRING and TWO groups by CAUSE: three are method expressions (F7) and
`spec-examples-decl/timezone-stringer` is blocked by `fmt.Sprintf`, i.e.
the stdlib surface (F19). A2 greened exactly the three and left
`timezone-stringer` red — which is what a correct grouping predicts and
a lazy one does not.

### 3.2 QUEUED frontend-only mini-slices (no user gate; a scheduling call)

Each is diagnosed to a named function with a stated mechanism; each is
deferred with a REASON, per the slice's brief (defer is permitted for
(a) rows; the obligation travels with the row and the arc's DONE is not
met while one is open).

| id | subject | reds | mechanism | why deferred here |
| --- | --- | --- | --- | --- |
| **A3** | map elements as multi-assignment targets (F6) | 5 | in `emitAssign`'s generic multi-target path, hoist base+key temps in TARGET order alongside the RHS hoists, then emit the existing `map-assign` store nodes in target order | ~1 day, and it lands inside the ASSIGNMENT SPINE that BUG-025/BUG-052 own (phase-1 operand order, inter-target order — an open-envelope area). It needs its own edge enumeration of the two phases, not a ride-along |
| **A4** | unnamed channel types as generic type arguments (F16) | 1 | a `*types.Chan` arm in `mono.go`'s `renderTypeArg` spelling `chan int` / `<-chan int` / `chan<- int` | ~half a day, but it moves the MANGLING/identity surface: the arm owes a reflect-spelling probe (every existing arm cites one), an injectivity argument, and an update to `TestManglingSurfaceFailsClosed`, which pins the refusal. Identity work deserves its own slice |
| **A5** | shadow-capture over a tuple-typed comma-ok RHS (F22) | 1 | in the `captures` branch, when `goTypeOf(r)` is a `*types.Tuple`, pre-bind the comma-ok SOURCE'S OPERANDS to temps instead of hoisting the whole RHS | ~half–1 day; a BUG-057-family edge whose oracle is the case's own expected `(7, true)` with the outer `v` |
| **A6** | scope the `len`/`cap` hoist predicate to the STATEMENT (F23) | 4 | `stmtHasRecv`, recomputed at `emitStmt` with save/restore and **defaulting true**, ANDed into `emit.go:6724` — so a receive-free statement keeps `len` inline (gc's realization; the receive-free control `channels/recv-order/len-embedded-no-recv` is already green end-to-end) and only a same-statement receive keeps the hoist and its residual refusal | **deferred on a finding, not on cost** — see §3.4. It also owes a new red guardrail row for the residual same-statement shape, which is currently unpinned |

**JUDGMENT (slice 5, A6 is deferred rather than taken).** The charter
named the receive-hoist family as an expected (a). It is — but not by
the fix the charter sketched, and not before a question this triage
opened is answered (§3.4). Taking it blind would have widened a live
divergence. Recorded because "the charter predicted (a)" is exactly the
pressure that makes a slice ship a fix it has not finished diagnosing.

**JUDGMENT (slice 5, F12 sync composite literals are NOT pulled in).**
`&sync.Mutex{}` is the zero value, so it could route to the existing
`new(sync.Mutex)` lowering in about half a day — genuinely cheap. NOT
taken, and NOT (a): it is a recorded design-note §9 scope pin
("PERMANENT-until-lifted"), so lifting it means amending §9, and the
VALUE-position form (`sync.WaitGroup{}`) raises the copy-a-sync-value
question §9 deliberately avoided. "Cheap" is not the same as
"diagnosed"; this one is cheap and undecided, so it stays (b) with the
decision named.

**JUDGMENT (slice 5, F18 and F17 are not opportunistic fixes.)**
`slices.Sort` at non-integer elements and the function-local-type
mangling refusal are both DELIBERATE pins whose whole value is that they
go red if someone widens the surface silently. Neither is touched.

### 3.3 GATED on the charter's GoCore pause — 19 reds

These are all diagnosed to a named arm with a mechanism (§2.2 rows L1,
L2a, L3, L5, L6, L7, L10), and every one is red→green-only movement over
a currently-refusing or currently-stuck path. **Every one is a change to
`GoLean/GoCore/*.lean` — the semantic core** — so the charter's hard
boundary puts them at the same class of user gate as slices 3 and 4.
They are listed here as a single ASK, not started:

| row | subject | reds | est. |
| --- | --- | --- | --- |
| L1 | `[]rune(s)` / `string([]rune)` conversions — 2 new StrictOps over the EXISTING `decodeRuneAt` (U+FFFD-correct) and `GoString.fromCodePoint` kernels | 9 | ~1 day |
| L2a | slice→array length-check panic arms | 3 | ~½ day |
| L3 | IEEE-aware `min`/`max` float fold over the existing `FloatBits.fcmp64` (NaN propagation, `min(-0,+0) = -0`) | 3 | ~½ day |
| L5+L6 | `.indexGet` `.addr` auto-deref and `.nil` nil-deref-panic arms, mirroring BUG-038's write-path arms | 2 | 1-2 h |
| L7 | relax the nominal struct-tag check to identical-underlying (the wire already strips tags, so both TypeIds map to identical `FieldDef` lists) | 1 | ~1 day |
| L10 | `go` of a nil func → `GoError.fatal "go of nil func value"` + correct the case's `expected_status` to `fatal` | 1 | 1-2 h |

**L10 deserves the user's eye specifically.** Its corpus comment says
"neither harness status class (ok\|panic\|deadlock) describes a non-panic
fatal" and its machine comment says "the fatal class is unmodeled this
slice". **Both are STALE.** The `fatal` expectation class landed at
spec-parity slice 2 (2026-08-09, two days after the pin was written) and
six cases pass through it today
(`sync/{mutex-unlock-fatal,rwmutex-misuse-fatal}/*`, all PASS in the
baseline). So this red is not a modeling limit; it is a pin whose stated
reason expired. Correcting an expectation whose justification has
expired is not "editing a case to make it pass" — but it IS the kind of
move that must be argued out loud, which is why it is here and not in a
commit.

**L2b is the honest split inside L2.** The three length-check-panic rows
are (a); `slice-to-array/ok-forms` is (b), because the SUCCEEDING
array-pointer form must alias the slice's backing segment
(`&s1[0] == &s[1]`, stores visible through the slice) and `Loc`
(base/field/index) has no subarray-view constructor. Splitting rather
than taking the whole group is what keeps "(a) = cheap and diagnosed"
meaning something.

### 3.4 A NEW divergence this triage found (and why A6 waits on it)

`spec#Order_of_evaluation` orders "all function calls, method calls,
receive operations, and binary logical operations" lexically
left-to-right, and `spec#Built-in_functions` says built-ins "are called
like any other function". So in `len(ch) + fill(ch)` the `len` must be
read BEFORE the call. gc agrees — probed at the pinned toolchain
(`artifacts/probe/triage-lencall`, scratch, go1.26.5):

```go
func lenVsCallObservable() int {
	ch := make(chan int, 4); ch <- 1
	return len(ch) + fill(ch)   // fill sends two more
}
```
`go run` → **1** (len read first). The frontend hoists CALLS out of
expressions (ANF) but leaves `len` inline in a receive-FREE function
(the `fnHasRecv` hoist is the only thing that ever hoists `len`), so the
machine should evaluate `fill(ch)` first and read `len(ch) == 3`. That
is a FORCED-point divergence — BUG-023's exact class on a different
axis (`len`-vs-CALL rather than `len`-vs-RECEIVE) — and it is
**pre-existing**, outside all 138 reds, in exactly the functions BUG-023
did not cover.

Two consequences, both recorded rather than acted on here:

1. It is a **corpus obligation**: the shape has no case, which is why no
   gate can see it. The machine side is REASONED, not run — the `go run`
   half is measured, the machine half is read off the emitter — so the
   first step is a guardrail case and a `diff-one`, not a fix.
2. It is exactly why **A6 waits.** Today a receive-BEARING function
   hoists `len`, and a hoisted `len` is appended to the accumulator
   before the call's hoist — so those functions get `len`-vs-call
   RIGHT, by accident. A6 makes `len` inline in receive-free STATEMENTS
   of receive-bearing functions, which would extend the divergence to
   them. The correct predicate is therefore "the statement's sweep
   contains an ORDERED EVENT" (receive **or call**), not "contains a
   receive" — a one-word difference in the mechanism, and precisely the
   kind of thing that is invisible until someone probes the neighbour.

## 4. Category (c) — the profound-reason pins, argued fresh

**7 rows, covering 9 baseline reds + 1 unpinned entry.** The charter
seeded three; two of those survive as seeded, one is re-scoped, and four
more are argued here for the first time. Each argument is written to be
JUDGED — if Mike rules any of them insufficiently profound, it converts
to a fix obligation in this arc or a named successor.

### C1 — `init/hidden-dep-order`: hidden-dependency initialization order

*1 red: `init/hidden-dep-order` (differential). Ledger: latitude
inventory E7; `baselines/untriaged-ids` header block.*

The spec says it in as many words (`spec#Package_initialization`): "If
other, hidden, data dependencies exists between variables, the
initialization order between those variables is unspecified." (`exists`
is the pinned spec's own typo, preserved inside the quote.) The pinned
witness is the spec's own shape: `hiddenX`'s initializer calls a method
through an INTERFACE, and the spec's dependency analysis counts only
"variables, functions, and (non-interface) methods declared in the
current package" — so `hiddenX` has no dependency and is ready at step
one. The machine realizes go/types' `InitOrder` (`[hiddenX, hiddenB,
hiddenA]` → 4242); gc runs a separate, coarser `initorder` and gets
`hiddenX` last (→ 4624242). **Both conform.** Forcing our answer to gc's
would be modeling one compiler's analysis pass, which is the doctrine's
exact anti-goal — and the direction of the divergence is the
soundness-relevant one (too narrow), so the honest resolution is an
ENVELOPE over conforming orders, not a different singleton. **Profound
because the spec explicitly declines to order it.** Re-envelope
obligation (E7, already recorded): a Choices site over the linear
extensions of the lexical-reference partial order with hidden-dep
variables freed (MODERATE — `$pkginit` becomes schedule-bearing), or the
cheap interim of a frontend DETECTOR for the shape that fails closed,
converting today's unguarded silent divergence into a visible refusal
(LOW). **The interim detector is worth the user's attention**: today
nothing in the frontend detects the shape, so a program with hidden
deps gets a silently-different order and only this one pinned case
notices.

### C2 — BUG-061: the `staticinit` pruning residual

*1 red: `multipkg/init-order-staticinit/seq` (differential). Ledger:
`docs/spec-divergence-ledger.md` L-011 (`spec-ambiguity`).*

gc schedules a PRUNED package set: only packages with residual
initialization work get an `..inittask` record, and "residual" means
what survives `cmd/compile/internal/staticinit`. The frontend
approximates that syntactically and therefore UNDER-prunes, keeping an
edge gc deleted. Ten of the eleven measured flavors are chaseable by a
mini-`staticinit` port — at the cost of a port whose own failure mode is
OVER-pruning, which deletes a REAL edge (the unsafe direction). The
eleventh, `callinit` (`var X = f()` for a foldable `f`), is **not
chaseable at all**: `go run` and `go run -gcflags=all='-N -l'` produce
DIFFERENT observable orders for the same source. **That is what makes
this profound.** At that point gc is not single-valued, so there is no
"gc's answer" to match; matching the optimized build would pin the
machine to an optimizer artifact. L-011's own sharp question — does the
spec's "sorted by import path" algorithm bind for a package whose
initialization is unobservable? — is a genuine spec ambiguity, not a
gap in our reading. **Scope note (this is the charter's "BUG-061
residual" made exact):** the (c) claim covers the `callinit` flavor and
the ambiguity; the other ten flavors are a chaseable fix whose cost/risk
we judge unfavourable today. If the user rules that insufficient, the
honest successor is the mini-`staticinit` port with an explicit
over-pruning guard, and the `callinit` red survives it.

### C3 — BUG-059: non-injective panic-message rendering

*1 red: `multipkg/same-name-identity-panic` (differential).*

Identity DECISIONS are correct (path-keyed TypeIds, the BUG-010 fix).
The divergence is only in the message CHANNEL: GoCore's renderers print
`TypeId.key` verbatim, so a multi-segment import path shows as
`red/inner.T`, where gc prints the package NAME — and, for two types
with the same name from different packages, gc deliberately prints the
SAME string twice plus a disambiguating parenthetical: `interface
conversion: interface {} is inner.T, not inner.T (types from different
packages)`. **The impossibility is precise: no single key string can be
both path-injective (which identity requires) and byte-equal to gc's
deliberately ambiguous name-qualified message.** So this is not "we
render it wrong"; it is "one field is being asked to carry two
incompatible obligations". The structural fix is separating DISPLAY from
IDENTITY in GoCore (a display-name table or a TypeId field) — a
semantic-core change. Scope, measured: the divergence exists only where
import path ≠ package name; for the whole vendored-raft scope (short
paths, path == name) rendering is exact, and dotted paths are refused at
the frontend boundary. **Profound as an impossibility-under-the-current-
representation, NOT as latitude** — gc's string is a forced point we
cannot currently express, and saying so plainly is the honest form. If
the user rules that a display field is owed, it is a small, well-scoped
GoCore change and this row converts.

### C4 — BUG-004: panic ABORT rendering at its unmodelable edges

*4 reds: `panic-recover/{repanic-same-value-abort,panic-newline-abort,
panic-defined-payload-methods/error,panic-defined-payload-methods/
stringer}`. Ledger: latitude inventory R10.*

Three distinct impossibilities, all in gc's abort-line output (which the
spec does not describe at all — this is `preprintpanics` behavior):

1. **`[recovered, repanicked]` collapse is eface IDENTITY** — a bitwise
   type-word + data-pointer compare. Constant-folded literals share a
   box and collapse; runtime-computed equal values do not. The machine
   has no allocation-identity model, so for EQUAL payloads the collapse
   is genuinely undecidable at the value level and `renderPanicHead`
   returns none. Modeling it means modeling gc's boxing/allocation
   identity — a representation commitment far beyond a render arm, and
   one that would pin us to gc's constant-folding.
2. **`preprintpanics` REWRITES the payload before printing** — a payload
   implementing `error` prints `v.Error()`, one implementing
   `fmt.Stringer` prints `v.String()`. Rendering that means **CALLING A
   METHOD AT ABORT TIME**, which the terminal rule cannot do: the abort
   is the end of the derivation, not a configuration that can take
   another step. The machine detects the method set and refuses rather
   than printing the `main.T(v)` form — which is what it did once, and
   it was a fail-closed→wrong-answer regression caught by audit.
3. **Multi-line payloads**: gc's first line stops at an embedded `\n`.

**Why (c) and not (b):** items 1 and 2 are not missing features; they
are demands that the machine's own structure cannot satisfy without
changing what the machine IS (allocation identity; evaluation inside a
terminal). Item 3 alone is cheap — and that is the honest weak point of
this row. **If the user wants the row split, `panic-newline-abort` is
(a)-shaped and the other three are (c).** We have not split it because
the entry treats them as one rendering surface and a partial fix
re-opens the "unconditional arm" regression class; but the split is
legitimate and we flag it rather than hide it.

### C5 — out-of-range / NaN float→int conversion

*2 reds: `floats/to-int-out-of-range/{nan,range}`. Ledger: latitude
inventory R6; floats design note §3.3; `baselines/untriaged-ids` header.*

`spec#Conversions`: "if the result type cannot represent the value the
conversion succeeds but the result value is implementation-dependent."
The spec constrains the result to nothing beyond "some value of the
target type", and this really does diverge across gc's OWN targets:
amd64 (`CVTTSD2SI`) yields `0x8000…0`, arm64 saturates. So the honest
envelope is a full-width nondeterministic choice over the target kind,
which would poison every downstream observation for zero corpus value,
and the too-wide direction has no oracle (one `go run` platform
witnesses one member). **Profound because the spec declares it and gc is
not single-valued across its own ports.** The machine refuses, visibly
(`unsupported`), which is the honest resolution of an unoracleable
point: a refusal is never a wrong answer, and picking amd64's value
would be modeling one port. Re-envelope obligation: a value-envelope
Choices site over `{amd64 point, saturation, …}` — worth building only
if a target program does this deliberately.

### C6 — function-local defined types as generic type arguments

*1 red: `generics/local-type-argument` (frontend-export). Recorded as
audit response M3, probe 2026-08-05.*

gc renders a function-local defined type with a compiler-internal unique
suffix (`score·1`) that is OBSERVABLE — in panic text and reflect names.
A bare `pkg.Name` key can neither reproduce that string nor stay
injective: two same-named locals in different functions collide, and the
collision would be SILENT. Any numbering we invented would be a guess at
a compiler-internal counter, i.e. modeling gc's implementation rather
than Go. **Profound as an impossibility: the observable name is not a
function of anything the language defines.** The refusal message says so
in the source — "refused rather than guessed" — which is the doctrine
working as designed. A lift requires an identity-design decision (what
IS the semantic identity of a function-local defined type across two
executions of the enclosing function?), not a feature build. Note this
is the ONE frontend-export red claiming (c); every other refusal in
§2.3 names a feature that could be built.

### C7 — BUG-002: expression-step atomicity (latent, 0 reds)

*`Pinned-by: none` — `Rel` has no goroutine rules, so no differential
case can pin it.*

Included because the arc's law is about BUGS as well as reds, and this
entry must not fall through the table for lack of a case. It is (c) in a
different sense from C1-C6: not latitude and not impossibility, but a
**known-unsound-under-concurrency granularity that is provably
unobservable today** — GoCore `Expr` has no call constructor, so no
sequential program distinguishes the granularities, and the entry itself
records that the concurrency arc (F4) is BLOCKED on resolving it. The
profound reason is that the fix is a decision F4 must make (small-step
expression machine vs confinement concurrency vs law-discipline
restriction), not work this arc can do; and the entry exists precisely
so the constraint cannot rot in prose while goroutine machinery is
built. **If the user rules this is not a legitimate (c),** the
conversion is not a fix but a re-scoping: BUG-002 would have to move to
F4's charter as a blocking precondition, which is where it already
points.

### The (c) list, in one place, for ratification

| row | reds | one-line argument |
| --- | --- | --- |
| C1 hidden-dep init order | 1 | the spec says the order between hidden-dependency variables "is unspecified"; go/types and gc realize two DIFFERENT conforming orders and we hold the spec-shaped one |
| C2 BUG-061 staticinit residual | 1 | the un-chaseable flavor is one where `go run` and `go run -gcflags=-N -l` disagree — there is no single gc answer to match, only an optimizer artifact |
| C3 BUG-059 panic-message qualifier | 1 | no one key string can be both path-injective (identity) and byte-equal to gc's deliberately ambiguous name-qualified message |
| C4 BUG-004 abort rendering | 4 | the collapse is eface ALLOCATION identity and the rewrite requires CALLING a method at abort time — both outside what the machine's terminal rule can express (weak point flagged: `panic-newline-abort` alone is (a)-shaped) |
| C5 float→int out of range | 2 | the spec declares the result implementation-dependent and gc's own ports disagree (amd64 wrap vs arm64 saturate); a refusal is the honest resolution of an unoracleable point |
| C6 local defined type as type argument | 1 | gc's observable name carries a compiler-internal counter (`score·1`) that is not a function of anything the language defines; guessing it would be modeling gc, and a bare name is not injective |
| C7 BUG-002 atomicity | 0 | unobservable today by construction (no call constructor in `Expr`); the fix is a decision F4 must make, and the entry is the record that keeps it from rotting |

## 5. The untriaged-25 cross-check (the charter's cross-cutting obligation)

The charter asks for the "P3 untriaged spec-example dispositions"
re-run against the fixed machine. **What that set actually is**, made
exact: `docs/spec-archaeology/spec-examples-dispositions.tsv` has no
untriaged marker — the untriaged-25 is the tracked fidelity backlog
`baselines/untriaged-ids`, enforced by `scripts/check-bugs.sh` check 4b
(a NEW entrant fails the gate; a departed id must be removed in the same
commit). Three independent derivations agree on the same 25 ids
(`check-bugs.sh --list`, the tracked file, and §0's arithmetic).

**Outcome: no member of the 25 was explained by slices 1–2's fixes.**
Derived, not asserted — the fidelity-red set (`differential` +
`lean-observation` + `nondet`) at each arc commit:

| commit | fidelity reds |
| --- | --- |
| `df3adbfc` (charter) | 48 |
| `740f09f8` (BUG-058 fixed) | 45 |
| `2d840744` (BUG-057 fixed) | 41 |
| `0c21aa21` (slices 3+4 probes) | 45 |

The 7 fidelity reds slices 1–2 killed were every one of them already on
BUG-057's or BUG-058's `Cases:` line (i.e. already EXPLAINED, never in
the backlog): `spec-examples-decl/{index-comma-ok/var-form-present,
receive-comma-ok/typed-form,receive-comma-ok/untyped-form-live,
var-decl-forms/found-present}`, `spec-examples-lexical/panic-values/
panic-error`, `spec-examples-stmt/if-init-hoist-order/{cond-call-after-
init,init-panic-first}`. The 4 that entered at `0c21aa21` are on
BUG-005's and BUG-056's. So the backlog is unchanged at **25/25**
throughout the arc, and "found-by-fix" produced nothing here — the
honest negative result, with its derivation.

**What this slice DOES change for the 25.** Ten of them carried NO
justification at all in `baselines/untriaged-ids` — they were bare ids
under an older block's comment. Every one of the 25 now has a written
disposition (a §2.2 row with its refusal point, or a §4 argument), and
this commit writes the ten missing justifications into
`baselines/untriaged-ids` with their triage cross-reference:

| id(s) | now |
| --- | --- |
| `strings/{defined-slice,nil-slice}-string-conversion`, `strings/{rune-invalid-values,rune-slice-conversion,rune-slice-to-string-copy,rune-string-conversion,string-to-rune-copy}` (7) | row L1 — `[]rune`↔`string` conversion, category (a), GoCore-gated |
| `arrays/pointer-array` | row L5 — `.indexGet` missing `.addr` arm, (a), GoCore-gated |
| `pointers/nil-array-index-panic` | row L6 — `.indexGet` missing `.nil` arm, (a), GoCore-gated |
| `structs/tag-pointer-conversion` | row L7 — nominal tag check vs `spec#Conversions`' tags-ignored rule, (a), GoCore-gated |

**A metric finding, recorded and NOT acted on.** The backlog counts a
baseline FAIL at a fidelity STAGE that no `docs/BUGS.md` entry explains.
But `lean-observation` is also where the INTERPRETER's fail-closed
refusal of an unmodeled construct lands — and BUGS.md's own preamble
says such a construct "is not a bug… tracked as coverage, not here". So
rows like `channels/select-select/core` (frontier) and
`floats/to-int-out-of-range/*` (latitude) can never leave the backlog by
being fixed OR by being triaged, and the ratchet's "toward zero" is
unreachable by construction for them. The clean resolution is a
`coverage` / `latitude` disposition column in `untriaged-ids` that the
check subtracts — a change to a GATE, which this slice deliberately does
not touch. Slice 6's coverage ledger is the natural owner; flagged here
so the number is read honestly in the meantime.

## 6. Counts, and the end-state check

At `0c21aa21` (before this slice's A1), by RED and by GROUP:

| category | reds | red groups | bug entries |
| --- | --- | --- | --- |
| **(a)** fix in this arc | **46** | 16 | 2 (BUG-005, BUG-056) |
| **(b)** frontier | **82** | 23 | 3 (BUG-008, BUG-014, BUG-041) |
| **(c)** profound-reason pin | **10** | 6 | 4 (BUG-002, BUG-004, BUG-059, BUG-061) |
| total | **138** | 45 | 9 |

The (a) 46 decompose as: **6 fixed in this slice** (A1 3 + A2 3) +
**11 queued frontend-only mini-slices** (A3 5, A4 1, A5 1, A6 4) +
**19 gated on the GoCore pause** (§3.3) + **10 already at the charter's
slice-3/4 gates** (BUG-056 5, BUG-005 5). After A1 and A2 the tip
baseline is 2179 cases / 2047 PASS / 132 FAIL — 11 new green ids and 6
reds retired, with zero unpredicted drift at either gate.

The (b) 82 decompose as: 74 `frontend-export` + 8 fidelity-stage
(L2b 1, L8 1, L9 2, L13 2, L14 1, L15 1).

**Zero rows outside the table.** Every one of the 138 reds appears in
exactly one group of §2, every group carries exactly one category, and
all 9 open BUGS.md entries appear in §1. The arithmetic closes three
ways (§0). After A1 the tip baseline is 2174 cases / 2039 PASS / 135
FAIL; the table's own numbers are stated at `0c21aa21` on purpose, so
that the categorisation and the fix record cannot drift into each other.

**What the arc still owes before its end-state claim is true** (charter:
"every baseline red is category-(b) frontier … or category-(c)
profound-reason … every BUGS.md entry is fixed or category-(c)"):

1. the 11 queued frontend-only (a) reds — A3…A6, mechanisms in §3.2;
2. the 19 GoCore-gated (a) reds — ONE user gate, §3.3;
3. the two design gates already open (BUG-056, BUG-005);
4. user ratification of the 7-row (c) list, §4;
5. the len-vs-call divergence of §3.4 — a corpus obligation (guardrail
   case + `diff-one`) before A6 can be written correctly.

None of these is a "known issue" parked without a reason: each is an
open obligation with a named owner and a written mechanism, which is the
state the charter's law permits and the state this table exists to make
checkable.

**POSTSCRIPT (2026-08-19, same day):** obligation 2 — the 19
GoCore-gated (a) reds — is DISCHARGED: the user approved the §3.3 ask
as one slice of six arm-family commits (`eca39e4d`…`d6df87cc`, L1,
L2a, L3, L5+L6, L7, L10), 19/19 red→green with zero unpredicted drift
and the batch-end `--slow` re-certification green. Execution record:
`docs/bugfix-arc-log.md` §19-red. The table above deliberately keeps
its numbers at `0c21aa21`; the L10 row's expectation correction and
the L2a/L2b split landed exactly as written here.

**POSTSCRIPT 2 (2026-08-19, same day — slice 5b / H-3).** The
per-declaration quarantine now covers METHODS
(`docs/bugfix-arc-log.md` §H-3), which adds **four** baseline reds and
retires none. All four are the CALL rows of the H-3 guardrail suite —
`methods/quarantine-sibling/quarantined-call`,
`methods/quarantine-interface/dispatch-quarantined`,
`methods/quarantine-embedded/promoted-call`,
`methods/quarantine-pointer-receiver/pointer-call` — and all four are
**F19** (`fmt.Sprintf` reaching `emit.go`'s "selector call … is not a
method value"), i.e. category **(b)**, the stdlib-surface frontier row
that §2.3 already marks raft-path-in-aggregate. F19's id list goes 2 →
6 and the (b) column 82 → 86; the table's own counts stay pinned at
`0c21aa21` per its stated convention. Zero rows outside the table
still holds: these four are red for a feature the table names, and
their eight green siblings are the fix's flips, not reds.

**POSTSCRIPT 3 (2026-08-19, slice 6 — the whole-language bar).** The
frontier map's authority moves to **`docs/language-coverage-ledger.md`**
(§4 frontier features FR-1…FR-15, §6 design questions Q-*); the F-row
ids above remain as the historical record and the ledger cross-refs
them. Slice 6 adds 26 baseline ids (+15 tranche A `5a8f7002`, +11
tranche B): 4 new greens (3 position/accident-green controls + the
delegated `unsafe/boundary/sizeof-const` constant) and 22 new reds,
each in exactly one category, so zero-rows-outside-the-table still
holds:

- **(a)**: `builtins/len-vs-call-order/{chan,slice}` — the §3.4
  divergence, now MEASURED on both sides and filed as **BUG-062**
  (Cases: those two ids; owner mini-slice A6, whose predicate the
  entry restates).
- **(b)**: the frontier suites — `channels/recv-short-circuit/*` 3
  (F24), `range/assign-form-nonident/*` 3 (F20),
  `goroutines/go-builtin/*` +4 (F15: 1 → 5),
  `sync/atomic-frontier/*` 5 (NEW row: sync/atomic, the ledger's
  Q-ATOMIC), `sync/out-of-scope-cond/*` +2 (F13: 1 → 3),
  `goroutines/goexit-marker/child` 1 (NEW row: mem#goexit,
  Q-GOEXIT), `generics/stencil-quarantine/sibling` 1 (NEW row: the
  H-3 method-stencil residual, measured).
- **(c)-class, NEW ROW C8 — the unsafe boundary marker**:
  `unsafe/boundary/pointer-roundtrip`. Argument: Package_unsafe is
  OUT-OF-LANGUAGE (the ledger's row carries the justification — the
  spec's own implementation-specific guard; modeling its observables
  means modeling gc's layout; the type-safety escape defeats the
  machine's memory model), and the red exists so that boundary is
  visible rather than grey. Joins the §4 ratification list: if the
  user rules unsafe in-language, the row converts to a frontier
  feature with a design question, not silently.

Two of the 22 reds surface at fidelity-adjacent stages
(`atomic-frontier/{value,mp-litmus}`) and entered
`baselines/untriaged-ids` with justifications (ceiling 7 → 9, reason
in `baselines/untriaged-count`) — the §5 metric finding's class,
whose clean resolution (a disposition column) the ledger records as
T-5, an operator decision.
