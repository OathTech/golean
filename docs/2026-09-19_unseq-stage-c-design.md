# Stage C — the native `unseq` pilot: grammar, census, wire schema, decoder spec (C0 records, 2026-09-19)

[AGENT] Lane `core/unseq-stage-c-0919` (worktree `.claude/worktrees/unseq-stage-c`), base main
`6a7beb3d` (train r43 closed; C1 complete modulo its owed list). Design of record:
`docs/2026-09-16_evaluation-order-model-v2.md` (v2.1) §3.1 (the occurrence contract and the
bounded first-fragment grammar), §3.2–§3.6, §7 row C; the second review
`docs/2026-09-16_evaluation-order-model-v2-review.md` §2 row C / §3 (the acceptance matrix); the
landed construct: `docs/2026-09-16_unseq-stage-b-handoff.md` (§2 representation choices, §5
Stage C's entry point, §9 the fix round's named refusals). Authority: the mechanism ruling
[USER] Mike 2026-09-16 «the Cerberus model is the correct one» (relayed); the sequencing «(1)
agreed» [USER] 2026-09-18 (relayed); the three Stage C rulings, [USER] Mike 2026-09-19, verbatim
«Agree, merge», relayed by the [AGENT] coordinator — cite as relayed
(`docs/2026-08-31_qrow-rulings.md`, «The C1 completion and Stage C rulings record»): (3) width
of P = ALL mutable reads, STAGED — the pilot carries the minimal P(ii) reads its fixtures need,
then widens; (4) N1 = SPLIT — base/header and index producers plus ONE checked access; (5) N3 =
REFUSE by name when a membership row's enumeration budget is exhausted, never silently
sequentialise, rows may go red. Everything below is [AGENT] unless marked. This note is the C0
record: the pilot grammar as the emitter's decision procedure, the census, the predicted flips
and lane moves, the wire schema, the decoder spec and the lowering rules the C1/C2 slices
implement; the lane handoff is `docs/2026-09-19_unseq-stage-c-handoff.md`.

## 1. The pilot grammar, as the whole-sweep decision procedure

THE BOUNDARY RULE (v2.1 §3.7; Stage B audit N2): one sweep — a block-level statement in
`emitStmtList` — is lowered EITHER as ONE `unseq` graph OR by the legacy E13 probe path, never
a mixture, never by fixture name. The decision is the ONE function `unseqClassify`
(`tools/nativefrontend/unseq.go`), syntactic over the typed AST, shared by the census
(`nativefrontend --unseq-census`) and the emitter (C2):

    admitted  :=  form ∈ FORMS  ∧  every operand ∈ EXPR  ∧  calls ≥ 1  ∧  nonEvents ≥ 1

**FORMS** (block-level statements): `x := e` · `x = e` (x a local identifier — a parameter, named
result or body local; never blank, never a package variable, never a variable read through a
capture pointer inside a lifted body) · `a[i] = e` (a slice element) · `x op= e`, `a[i] op= e`,
`x++`/`x--`, `a[i]++` · `return e₁, …, eₙ` (n ≥ 1; or `return f()` forwarding a 2-result call) ·
a call statement `f(args)` (0–2 results, discarded) · `print(args)`/`println(args)` (≥ 1 basic
operand). Sub-accumulator sweeps (if/for/switch heads, range operands, case values) are not
block-level statements and stay legacy by construction.

**EXPR** (operands): a constant of integer/bool/string type · a LOCAL identifier of an admitted
type — PRIVATE (address never taken: not captured by a func literal, no `&x`, no array slicing,
no method receiver) → an order-transparent ATOM (v2.1 §1); ADDRESS-TAKEN → a READ occurrence
(the pilot's P(ii) reads — ruling (3)'s minimal set: the W1/W6/R1/R6 witnesses' `a`, `x`, `x`/`y`,
the slice header `a`) · `s[i]` on a SLICE (base and index ∈ EXPR; N1 SPLIT — ruling (4): the
base/header and index are producers, the checked access is ONE occurrence) · `s[lo:hi(:max)]`
on a slice (a failing pure op) · `len(s)`/`cap(s)` on a non-constant slice (an E1-ordered EVENT
occurrence — spec#Built-in_functions «called like any other function», BUG-062 — with no effect
and no failure on a slice value) · `f(args)`: a same-package, non-generic, non-variadic
top-level function, a func-typed local (its read is an occurrence when address-taken), or an
immediately-invoked func literal; arguments ∈ EXPR, no tuple forwarding, no spread; 0–2
results of admitted types (≥ 1 in value position) · `e₁ op e₂` for arithmetic, bitwise, shift
and comparison operators on admitted basic operand types (never an interface comparison) ·
`-e`, `^e`, `!e` · `e.(T)` single-value, on an empty-interface operand, to an admitted type ·
`e₁ && e₂`, `e₁ || e₂` (a GUARD entry + region + completion). **TYPES**: integer kinds, bool,
string, slices of admitted types, the empty interface (`any`); aliases transparent. Outside
(→ the whole sweep legacy, BY NAME): package variables, pointers/`*p`/`&x`, fields and
selectors, methods, maps, arrays, strings indexing, named types, floats, funcs as values,
conversions, allocations (composite literals, `make`, `new`, `append`, `[]byte(s)`), receives,
sends, `recover`, comma-ok forms, multi-target and blank assignment, other statements.

**THE TRIGGER.** `calls` counts the call occurrences (the events with EFFECTS); `nonEvents` counts
the occurrences observable AGAINST an event: reads of address-taken locals, slice-element
checked accesses, failing pure ops (slice expression, type assertion, `/`/`%` by a non-constant,
a shift by a non-constant signed count), slice-element target plans, a compound target's read
of an address-taken local, guards. A sweep with no call has nothing with an effect to reorder
against (E12(ii)'s read-vs-read axis and `len`-vs-read are unobservable orders — Stage E widens
if a fused-panic observable ever demands it); a sweep with a call but no such occurrence has
every edge forced (`x := f()`, `x += f()` with x private, `f(g())`). Both stay legacy — the
legacy path realizes them without a tape choice, exactly as today. THE CENSUS (§2) is this
rule's measurement.

## 2. The census (2026-09-19, C0 frontend `.tmp/nativefrontend`, corpus at `6a7beb3d`)

`scripts`-free lane tooling: `nativefrontend --unseq-census --dir <pkg>` prints one TSV row per
sweep (unit, file:line, function, form, admitted, events, calls, nonEvents, reason) over EVERY
unit of the program; `docs/evidence/2026-09-19_unseq-stage-c/` has the aggregation.

- Corpus: 1353 packages, 107 773 sweeps (all units), **120 admitted** in **28 packages**, all in
  MAIN units (0 in imported units); forms: 50 compound (44 of them the four injected fmt shim
  helpers' `out += goleanShimFmt…(verb, args[ai])`, all-forced), 32 return, 26 assign (25 the
  imported-goose `ok = ok && (f(x) == 0)` chains, all-forced), 7 define, 5 elem-assign.
- The raft twin (`baselines/pins/twin-chdriver.wire.json`'s assembly): 10 203 sweeps across 20
  units, **0 admitted** → the twin pin does not move at C2 (stated for C3 per the brief).
- Rows in the 28 packages: 345 (227 strict PASS, 37 membership PASS, 27 FAIL/frontend-export,
  4 FAIL/differential; the 50 rows whose SUBJECT contains an admitted sweep are listed in
  `affected-rows.tsv`). The observable consequence per row is derived in §3; it is CONFIRMED at
  C2's gate (`ci --diff`) and every moved row is named there.
- C0 is WIRE-NEUTRAL: the main-tip frontend (built from `git archive main`) and the C0 frontend
  emit byte-identical wires (or identical refusals) on all 1353 packages
  (`census-summary.txt`).

## 3. Predictions (derived from the graphs of §6; gc's draws measured 2026-09-19 at the pin)

**FLIPS, FAIL → PASS/membership (4 rows; each set ∋ gc's draw):**

| row | sweep | graph members (output · result) | gc draw |
|---|---|---|---|
| `builtins/e13-sibling-panic-order/assert-ok-early-len-hoist` (BUG-101; FAIL/lean-observation) | `return iv.(int) + len(b[j:]) + f()`, `iv` captured, f: `iv = "s"` | {`mut` · ok 6, `mut` · panic «interface conversion: interface {} is string, not int»} | `mut` · 6 |
| `…/slice-value-early-len-hoist` (BUG-101; FAIL/differential) | `return a[i:][0] + len(b[j:]) + f()`, `i` captured, f: `i = 1` | {`mut` · 12, `mut` · 22} | `mut` · 12 |
| `…/compound-call-target-vs-call` (BUG-104; FAIL/differential) | `x[fnine()] += wit(5)` | {`f` · panic [9]/1, `f wit 5` · panic [9]/1} | `f wit 5` · [9] |
| `…/compound-call-target-vs-len` (BUG-102 designed red; FAIL/frontend-export) | `x[fnine()] += len(b[j]) + wit(5)` | {`` · panic [5]/1, `f` · panic [5]/1, `f` · panic [9]/1} — `wit` never runs (E1: `len` before `wit`, and `len`'s operand `b[j]` panics) | `f` · [5] |

**NOT FLIPPED (outside the pilot, stay red on their entries):** BUG-104's `map-compound-index-key-vs-
{call,recv,method}` (map-element targets — the machine's own Stage E refusal) and
`compound-call-target-vs-recv` (a receive operand); BUG-102's five structural-allocation rows
(composite literals). Named here so C3 files no undisclosed flip.

**LANE MOVES strict → membership (the E12/E2 VALUE axis enveloped on exactly these rows; each
set ∋ the strict row's current gc value):** `noodler/latitude/args-index-vs-call` {15, 1005} ·
`noodler/latitude/concat-var-vs-call` {`ab`, `zb`} · `noodler/latitude/index-call-index`
{4, 103, 301, 400} · `noodler/latitude/return-operands` {(1,5), (100,5)} · `noodler/maps/
slice-compound-call-mutates` {15, 105} · `multi-assign/index-target-rhs-call-order` {752, 1209}
(E2's `xs[i] = bump()`, `i` captured) · `builtins/e13-sibling-panic-order/assert-right-call`
(`wit(5) + iv.(int)`: E13 residual (1) removed — the operand RIGHT of the event is unordered
against it; {`` · conversion, `wit 5` · conversion}).

**MEMBERSHIP PINS RE-DERIVED (sets ⊇ today's; v2.1 §3.5 «each widening named»):** the 19
`e13-sibling-panic-order` membership rows whose subject enters the pilot and `binop-order/
operand-panic-vs-call/{call-before-left,call-before-left-div}`. Widenings expected where an
operand sits between or before SEVERAL events (`assert-middle`: the assertion before `wit(1)` is
a third member; `two-index-left-call`; `index-middle`) — the probe realized endpoints, the graph
every linear extension; `width=` rises to the ready-set bound where it exceeds 2. Exact counts
come from the enumerator at C2 (the `members=` guard fails by name on a moved count); a
NARROWING is a STOP, never a re-pin.

**DEPTH DECLARATIONS (identical observations, more wide picks than the fixed streams hold):**
`spec-examples-stmt/continue-label` (`row[x] = data + bias(x, y)` in a nested loop — one wide
pick per iteration, ~9, plus `return enc(rows[0]), …`'s 2: ≈ 11 > 8) → `depth=64` by the 4·w
convention (`docs/coverage-suite-structure.md`), the ONE predicted declaration. Strict rows
whose graphs are all-forced (0 picks: the goose `ok = ok && …` chains, the fmt shim helpers,
`s := expensive()[:]`, `xs := source()[lo():hi()]`, `ok := isPos(a) && isPos(b)`, the recursive
closure rows, `len(b[j]) + wit2(5)`) and rows with ≤ 2 picks and singleton sets
(`noodler/evalorder/*`, `noodler/arith/compound-index-order`, `scoping/closure-shadow-binding`,
`forced-arg-only`, `slice-left-len-call`) stay strict PASS; any other movement at C2's gate is a
STOP.

## 4. The wire node (schema `golean-native-v1`, statement tag `unseq`)

    {"stmt":"unseq",
     "cells":[{"id":"$u0","type":T}, …],                                    // VALUE binders, typed
     "occs":[                                                                  // canonical RANK order
       {"name":"read0",  "kind":"eval",   "bind":"$u0", "head":EXPR},          // EXPR carries "type"
       {"name":"call1",  "kind":"invoke", "binds":["$u1"], "callee":EXPR, "args":[EXPR…],
                         "resultTypes":[T…], "after":["len3"]},
       {"name":"target2","kind":"target", "bind":"$t0", "lhs":TARGET},         // sort TARGET
       {"name":"load3",  "kind":"load",   "bind":"$u2", "target":"$t0"},
       {"name":"guard4", "kind":"guard",  "test":"$u3", "when":false, "out":"$u4"},
       {"name":"join5",  "kind":"eval",   "bind":"$u4", "head":EXPR, "region":"guard4"} ],
     "stores":[{"target":"$t0","value":"$u5"}],                                // phase 2, left to right
     "then":STMT }                                                             // the completion

Keys per kind (exact-key discipline): `eval` name·kind·bind·head[·after·region]; `invoke`
name·kind·binds·callee·args·resultTypes[·after·region]; `target` name·kind·bind·lhs[·after·
region]; `load` name·kind·bind·target[·after·region]; `guard` name·kind·test·when·out[·after·
region]; a store target·value; the node stmt·cells·occs·stores·then. `after` = ORDER
prerequisites (E1/F), `region` = the guard whose region the occurrence belongs to (absent =
top level); value dependencies are IMPLIED by binder mentions (v2.1 §3.2). Binder names are
`$u<n>` (cells) / `$t<n>` (targets); occurrence names `<kind><n>`. The map is 1:1 onto
`UnseqGraph`/`UnseqOcc`/`UnseqBody` (Syntax.lean): `eval`→`.eval`, `load`→`.load`,
`invoke`→`.invoke`, `target`→`.target`, `guard`→`.guard`.

## 5. The decoder spec — every check a refusal BY NAME (`GoLean/NativeToIR.lean`, the `unseq` arm)

The machine's `UnseqGraph.wellFormed?` and its dynamic refusals stay the enforcement (Stage B
§9.1); the decoder is the STATIC net at the wire boundary, refusing before a graph exists:

| # | check | refusal names |
|---|---|---|
| D1 | exact keys on the node, every occurrence (by kind), every store | `unknown key …` (the standing discipline) |
| D2 | `cells`: `decodeParam` each; ids distinct; every id `$`-prefixed | `duplicate binder cell '$x'`; `binder '<x>' is not a reserved $ slot name` |
| D3 | occurrence names distinct and non-empty; `occs` non-empty | `duplicate occurrence name`; `empty graph` |
| D4 | `kind` ∈ {eval, invoke, target, load, guard} | `unknown occurrence kind '<k>'` |
| D5 | every `bind`/`binds` of eval/load/invoke is a declared cell; every cell produced by EXACTLY one occurrence; target binds `$`-prefixed, distinct, not cells | `result binder '<b>' is not a declared cell`; `duplicate result: binder '<b>' produced twice`; `cell '<c>' is produced by no occurrence`; `sort mismatch: '<b>' is both a TARGET and a VALUE binder` |
| D6 | sorts: `load.target` is a target binder; a target binder never appears as a value (heads, callee, args, guard test, store value, `then`); store target is a target binder, store value a cell | `sort mismatch: …` |
| D7 | LIST ORDER IS A LINEAR EXTENSION: every `after` name, every cell/target binder an occurrence consumes, and its `region` guard refer to an occurrence of STRICTLY LOWER rank (cycles included) | `list order is not a linear extension: '<o>' (rank i) depends on '<p>' (rank j ≥ i)` / `unknown occurrence reference '<p>'` |
| D8 | NORMAL FORM: an `eval` head is one of `ident` (a read of a cell or a source local), `index-get(atom, atom)`, `slice(atom, atom, atom \| builtin-len(base atom), [atom])`, `builtin-len/cap(atom)`, `binary(op ∉ {&&, \|\|}; atom, atom)`, `unary(atom)`, `type-assert(atom)`; an atom is `ident`/`int`/`bool`/`string`; `args` are atoms or `to-interface(atom)`; `callee` is an `ident` or a `func-value` whose captures are `ref`/`ident`; no `recover`, no `unseq-probe`, no allocation head anywhere | `hidden read in a pure node: <head>.<operand> is not an atom`; `logical operator in a head (guards are occurrences)`; `recover() inside an unseq occurrence`; `head '<expr>' outside the Stage C fragment` |
| D9 | an `eval` head carries `type`; `decodeTy(head.type) = cell type` | `head type <T> disagrees with cell '$u' declared <T'>`; `eval head carries no type` |
| D10 | `invoke`: 0 ≤ binds ≤ 2; `resultTypes` arity = binds; each = the cell's type | `invocation with n results outside the fragment`; `resultTypes arity …`; `result type … disagrees with cell …` |
| D11 | `guard`: `test` and `out` are bool cells; `out` produced by exactly one occurrence whose `region` is this guard | `guard '<g>' tests '<c>', not a bool cell`; `… completion '<c>' is not produced inside its region` |
| D12 | STATIC G (v2.1 §1): a binder produced inside region G by an occurrence other than G's completion is consumed only by occurrences whose region chain contains G — never by a store, `then`, or an occurrence outside | `invalid branch join: '<o>' uses '<b>', confined to region '<g>'` |
| D13 | `target.lhs` is `{"target":"var","id":<source local>}` or `{"target":"addr","expr":{"expr":"index-addr","base":atom,"index":atom}}`; the id is not `$`-prefixed | `target plan outside the Stage C fragment`; `a binder cannot be a store target` |
| D14 | `then` decodes (`decodeStmt`); contains no `unseq`, no `unseq-probe` (the whole-sweep boundary, machine-side defence in depth — audit N2), no `recover` | `nested unseq`; `legacy unseq-probe inside an unseq completion (mixture)` |

Byte-input controls (C1, `scripts/check-wire-boundary` extended): duplicate binder (D5), a
cycle / forward reference (D7), a skipped-branch value used without a join (D12), a sort
mismatch (D6), a non-`$` binder (D2), an unknown slot (D8/D5), plus the positive control (the
wire runs to its reference set).

## 6. The lowering (C2, `tools/nativefrontend/unseq.go` `emitUnseqSweep`)

- **Atoms.** A constant → its folded wire; a private local → `ident`; a slot → `ident $u`.
- **Reads.** An address-taken local → `eval $u ident` (its declared type). A slice element →
  base atom, index atom, `eval $u index-get(base, index)` (the checked access). A slice
  expression → `eval $u slice(…)` (the default high is `builtin-len` of the same base atom).
- **Ops.** Every arithmetic/comparison/unary op and every type assertion is an `eval`
  occurrence on atoms (v2.1 §1: unreduced graphs; no ordering optimization).
- **Events.** `len`/`cap` → `eval $u builtin-len(atom)` with E1 `after`; a call → `invoke`
  with result cells (0–2; a statement-position call with results gets DISCARD cells `$d<n>` —
  a targetless value frame is stuck-closed), `callee` = `func-value{func}` for a top-level
  function, `ident` for a func local (a slot when address-taken), the lifted `func-value` for a
  literal; args atoms or `to-interface(atom)` (`wrapInterfaceConversion`); E1: `after` the
  previous event anchor; the anchor becomes this occurrence. Nested `f(g())`: g's occurrence
  precedes f's (post-order); `f(g())`'s data edge is implied.
- **Guards.** `l && r` / `l || r`: the test cell = l's slot (or an `eval` copy of a constant /
  private atom into a bool cell); `guard` with `when` = `true` for `&&`, `false` for `||`,
  `after` the current anchor (E1 at the ENTRY for earlier events); r lowered with `region` =
  the guard and a fresh anchor; the completion `eval $out r-atom` in the region; the anchor
  becomes the completion (E1 at the COMPLETION for later events). Regions nest by chaining.
- **Targets and stores.** `a[i] = e` / `a[i] op= e`: `target $t addr(index-addr(base atom,
  index atom))` — the header FROZEN through the atom (a captured `a` reads its header into a
  slot first; a private `a`'s header is read at the plan step; never `ref a` — Stage B F2) —
  then for `op=` a `load $rd $t`, an `eval $op binary(op, $rd, e)`, and `stores [[$t, $op]]`
  (the value must be a CELL: a constant or atom value is copied into one). Plain local
  targets use `then`: `x := e` → `assign define x = atom`, `x = e` → `assign x = atom`,
  `x op= e` → `eval $op binary(op, x-read, e)` where x-read is a READ occurrence when x is
  address-taken and the bare `ident` when private (order-transparent — the read cannot be
  observed; a `load` would mint a spurious wide pick per loop iteration in the fmt shims),
  then `assign x = $op`.
- **Completions.** `return` → `{"stmt":"return","results":[atoms]}` (interface results wrapped);
  a call statement → an empty block; `println`/`print` → `{"stmt":"print",…}` over atoms.
- **Canonical order = today's ANF** (v2.1 §3.5): the occurrence list is EVENT-LIST ++ RESIDUAL,
  where the event list holds, in lexical order, each call/len/guard with the occurrences of
  its argument subtree (and a guard's left operand and region) immediately before it, and the
  residual holds every other read/op/target/load in lexical order. The all-zero tape then
  realizes calls first, reads late (gc's realization where gc is call-first; BUG-104's
  targets move late — the intended flip).
- **Mixture guard.** The lowering runs with `probeSuppress` raised and asserts the hoist
  accumulator is unchanged afterwards; a hoist produced inside a graph lowering is refused
  (`unseq lowering produced a legacy hoist — mixture refused`), never emitted.

## 7. [AGENT] choices and the alternatives not taken

| choice | taken | alternative | why |
|---|---|---|---|
| the trigger | calls ≥ 1 ∧ nonEvents ≥ 1 | every in-grammar sweep (incl. `len`-only and call-only) | 120 vs 186 admitted; `len`-vs-read and read-vs-read orders are unobservable (no effect, no failure on a slice value); the excluded sweeps have no tape choice on either path, so the legacy path is exact for them; E12(ii) stays (b) with its obligation |
| private compound targets | the read folded into the op head, the store in `then` | `target` + `load` + store for every target | a private local's read is order-transparent (v2.1 §1); the load would add one wide pick per iteration in every fmt shim loop, moving strict rows for no semantic content |
| `len`/`cap` | E1-ordered `eval` occurrences (with `after`), not a trigger | (i) trigger; (ii) not an event | BUG-062's forced order against calls is kept; a `len`-only sweep has nothing to observe |
| graph shape for `x := e` | `then: init x; x = $u` (Stage B handoff §5) | a target occurrence for x | a plain-var plan has no operands and checks nothing; K2/K3 already test the idiom |
| decoder D7 | list order = a linear extension (all references backward) | a separate cycle check with forward references allowed | one check gives acyclicity, dominance and «list order not a linear extension» at once; the emitter's rank is a linear extension by construction |
| census unit | a frontend mode (`--unseq-census`) over the emitter's own classifier | a separate Python census over Go source | one implementation of the boundary; the census cannot drift from the emitter |

## 8. PENDING [USER] (posed, not ruled)

1. The predicted lane moves (§3) enveloping E2/E12's VALUE axis on 7 named rows — [AGENT]
   proceeds (v2.1 §5 item 1: «ratify at the merge ask»); ratification asked at the merge.
2. Any C2 movement outside §3's list is a STOP and is reported PENDING [USER].

## 9. Owed to Stage D / E (recorded, not claimed)

Stage D: the workload ladder (repeated sweeps, a wide argument list, a loop, the E13 family)
with recorded budgets; route α (certify `unseqNext` in the dedup engine) — the fmt shim loops
and `continue-label` are the first measured product shapes. Stage E: widen P (globals,
pointers, fields, maps, receives, comma-ok, methods, conversions, allocations); the
`len`-only / call-only sweeps if a fused-panic observable ever demands them; remove
`unseqProbe`/`probeK`/`unseqPanic` after every caller moved; the twin re-pin when its sweeps
enter.
