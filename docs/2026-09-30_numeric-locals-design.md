# B6 — numeric locals (`VarId := Nat`): design note

[AGENT worker, lane `core/numeric-locals-0930`] 2026-09-30. Window row 5 (charter rev. 2, [USER]-RULED 2026-09-24,
relayed; `docs/2026-09-23_batched-window-charter.md` §1 row 5; `docs/2026-09-24_window-plan.md` row 5). Conditions:
the logic team's response §4 «B6 / numeric locals» (2026-09-23) and their 2026-09-28 request 3. B6 has no named design
gate; every genuine choice below is **[AGENT] choice, PENDING [USER] ratification at the merge ask** (D1–D6), never a
default. Acceptance: ZERO behaviour change (the `--diff`/`--slow` gate red only on the 5a pair; baseline unchanged; the
whole-corpus choice trace byte-identical in observations). Before = `main` @ `131a7313`; after = the lane tip.

## 1. What a local is today, and after

Today a local is a `String` at run time: `Param.id`, `Expr.var/ref`, `Assignee.var`, `Stmt.mapRange`'s vars, the
`unseq` binders, `Scope := List (String × Loc)`; `LocalEnv.lookup` walks scopes inner→outer comparing spellings;
the frontend emits source spellings (`localRename`d where a local shadows a named result: `x$shadow1`; capture
pointers `x$cap`) and `$`-temporaries of its own; the decoder synthesizes ~25 more `$`-temporaries (`$ta`, `$rcoll`,
`$ret{i}`, …). After: **`abbrev VarId := Nat`**, every one of those positions numeric; `Scope := List (VarId × Loc)`;
the scope walk is TEXTUALLY unchanged (key equality only) — the machine's binding discipline (fresh cell per
declaration execution, shadowing by scope depth, argument/result slots at frame entry, captures as leading pointer
parameters) is not touched; C4 owns the env restructuring.

**D1 — ids are DECLARATION ids, per function, assigned by the frontend from go/types objects.** Every `types.Object`
a function body declares or uses as a local (params, results, receiver, capture pointers, `:=`/`var`/range/select/
type-switch binders) gets one index in that function's table, allotted at first encounter; a `:=` that REUSES `err`
is a use (go/types `Defs[err] = nil`), so same-block short-declaration reuse is preserved; the per-iteration loop copy
(`emit.go` `loopVar`) re-declares the SAME object in a nested scope, so one id may have several declaration SITES —
the runtime walk (innermost binding of that id) keeps today's meaning. Two shadowing `x`s are two objects, two ids.
The decoder CROSS-CHECKS every source reference: the innermost in-scope declaration of the SAME SPELLING in its
scope-exact R1 environment (Stage E6a, audited construct by construct) must carry the same id — two independent
resolvers (go/types; the decoder's lexical walk) must agree or the program REFUSES BY NAME. That agreement is the
pure-renaming certificate: the runtime's walk by spelling (before) and by id (after) pick the same binding at every
reference. Alternatives: (a) decoder-only per-SPELLING interning — a bijection, no wire change, but no declaration
identity (shadowed `x`s share an id; the table cannot tell them apart); (b) decoder-only per-declaration split — one
resolver, no cross-check; a scoping divergence would be adopted silently instead of refused.

**D2 — `$`-temporaries stay spelling-interned, by the decoder, per function.** Frontend temps (`$f0`, `$lvp3_0`,
`$tryOk`, …) and decoder temps are interned on first sight into ids `≥ N` (`N` = the wire table's size), appended to
the table with `kind := .temp`; a `$`-spelling carries NO wire index and a non-`$` spelling MUST (a frontend site that
forgot one refuses by name — the omission cannot pass). Per spelling per function = exactly today's shadowing among
nested desugars (a bijection), so no locality argument is needed. Decoder state: `LowerM` gains a `StateT` layer
(temps + base), reset per function; the reader keeps the R1 environment, now `Array LocalDecl := {name, id, typ}`.

**D3 — the table: `Func.locals : Array LocalName`, `VarId` = index.**
`LocalName := { name : String, kind : LocalKind, pos : String := "", wire : String := "" }` — `name` is Go's
identifier (`obj.Name()`; for a temp its `$`-spelling), `kind ∈ {recv, param, result, capture, local, temp}`,
`pos` = `basename.go:line:col` of the declaring identifier ("" for temps/synthesized), `wire` = the lowering's
spelling when it differs from `name` (`x$shadow1`, `x$cap`; "" otherwise). Source spellings are RETAINED verbatim; ids
are NOT stable across source edits (an edit renumbers; the customer reconstructs a binding by `(function, name, pos)`
or by declaration order — the charter's clause, restated in `Syntax.lean`'s docstring). Home: `Func` (beside `args`/
`results`, default `#[]` for hand-built programs) — the machine never reads it (architecture rule: no frontend
artifact as a semantic fact); like `Program.typeDisplays` it is carried, checked data. Alternative: no `pos`.

**D4 — the wire moves to `golean-native-v3`.** Per function `"locals": [{name, kind, pos?, wire?}]`; `"local": n`
beside the spelling on every SOURCE ident/ref/`declare`/`var` target/param/result/receiver/`var`-decl entry,
`"keyLocal"`/`"valueLocal"` beside a range's `keyVar`/`valueVar`. Spellings stay on the wire (human-readable; the
redundancy is what the decoder checks). v1/v2 refuse by name. The twin wire (`baselines/pins/twin-chdriver.wire.json`)
is RE-PINNED with the JSON diff as the written reason; the certified slow-tier row's `wire-sha256` moves the same way
(r55 precedent — the coordinator records the move at the train; this lane records what changed). Alternative: keep v2
and derive everything in the decoder (= D1's alternatives).

**D5 — what the decoder checks (each with a mutant test, refused by name).** (c1) index `< N` and the table's
spelling (`wire` or `name`) equals the node's spelling; (c2) the table: no `$`-prefixed source name, `kind`
consistent with the signature (params/receiver/captures first, then results); (c3) scope: a source reference's id is
declared in the R1 environment at that statement; (c4) agreement (D1); (c5) after the body: `Func.localsOk f = true`
— the CORE's total check that every id the tree names (`Unseq.lean`'s `Stmt.names`, now `List VarId`) is `< f.locals.size`
and the signature's ids are pairwise distinct. A wire failing any of these is refused; nothing is repaired.

**D6 — observable text.** No spelling of a local reaches the observation channel: `print`/panic texts, race
reports (keyed by `Loc`) and the choice trace carry none. The only texts that print a local are REFUSALS —
`unbound GoCore variable address: {id}`, `unbound GoCore result variable`, `unseq: unbound target operand`, the graph
validator's binder texts — none appears in any baseline row; they now print the numeric id (and the decoder's checks
make the unbound cases unreachable for a decoded program). `Tests/GoCoreAdmission.lean`'s one pinned text is restated.

## 2. The name-table interface (request 3) — by intended name, pinned in `BridgeSet.lean` (RE-PIN 6)

- Types: `VarId := Nat`; `Param.id : VarId`; `Expr.var : VarId → Expr`; `Expr.ref : VarId → Expr`;
  `Assignee.var : VarId → Assignee`; `Scope := List (VarId × Loc)`; `LocalName`, `LocalKind`; `Func.locals`.
  (Answer to «whether `Param.id`/`Expr.var` become numeric»: yes, both, and every other binder position.)
- `Func.localName? (f : Func) (id : VarId) : Option LocalName := f.locals[id]?` — the table lookup;
  `Func.localsOk : Func → Bool` (D5 c5); `localsOk_covers : f.localsOk = true → id ∈ f.names → (f.localName? id).isSome`
  — «source spellings are retained» for every id the function names.
- The activation's runtime slot: `LocalEnv.lookup_declare_self`, `LocalEnv.lookup_declare_ne`,
  `LocalEnv.lookup_pushScope`; `bindParams_lookup` (arguments bind in order: with the ids pairwise distinct, argument
  `i` is at `.base ⟨s.heap.size + i⟩` and holds the normalized argument); `allocDecls_lookup` (declared locals /
  results likewise, after the arguments); `enterFrame_lookup_arg` / `enterFrame_lookup_result` — through
  `enterFrame_declared` (P's row): `LocalEnv.lookup frameEnv (f.args[i].id) = some (.base ⟨s.heap.size + i⟩)` and
  `… (f.results[j].id) = some (.base ⟨s.heap.size + f.args.size + j⟩)`, so «table lookup agrees with the activation's
  runtime slot» reads: `f.localName? (f.args[i].id)` is the `i`-th entry of kind param/recv/capture AND that id is bound
  to the `i`-th entry cell. These are B6's statements of the argument/result slots; C4 restates the layout as a function.
- Added to `Tests/GoCoreAudit.lean`'s required list.

## 3. The change, by surface

`GoLean/GoCore/`: `Syntax.lean` (types, table, `localName?`, `localsOk`), `State.lean` (`Scope`), `Unseq.lean`
(`names : List VarId`), key-type edits in `Machine`/`StepFn`/`Ops`/`MachineSound`/`StateWf`/`UnseqSound`/
`MachineEqb`/`SyntaxEqb`/`Multi*`/`EnumDedup*`; `stepFn`/`Step` coherence re-proved in the same commit (the rules'
text is unchanged; `Param`'s `BEq` and `Repr` follow). `GoLean/NativeToIR.lean`: the `StateT` layer, `LocalDecl`,
table decode, `local` on each source node, c1–c5, temps via `tmp`. `tools/nativefrontend`: `localID(obj)` +
per-function table (saved/restored around lifted literals like `captureParam`), `local` at each source site,
`locals` at each function emission, schema v3, `go test` fixtures. Tests: hand-built programs through a test-local
injective `String → VarId` helper (declare/use stay consistent; readable); hand-built wires get `local`/`locals`;
mutants for c1–c5. Records: `docs/2026-09-30_numeric-locals-handoff.md`, changelog rows (semantics + tool-interface:
schema v3, `decodeProgram`'s signature unchanged, `RunResult` unchanged, frontend flags unchanged).

## 4. Acceptance and measurement

`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` red only on the 5a pair; baseline unchanged; the whole-corpus
choice trace vs `main` byte-identical in observations (`scripts/choice-trace-corpus --dump`, the `.tmp/ct/<side>/`
path the only normalization); twin re-pinned with the diff; every theorem and the packet A/B statements proved AS
STATED; elaboration A/B interleaved on Machine/StepFn/MachineSound/StateWf/MachineEqb/StepErrors/BridgeSet (C3's
1.5× stop rule applies: a module past 1.5× is reported and fixed by proof-local edits, never by a heartbeat setting).
