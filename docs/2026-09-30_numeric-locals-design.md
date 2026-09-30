# B6 — numeric locals (`VarId := Nat`): design note

[AGENT worker, lane `core/numeric-locals-0930`] 2026-09-30. Window row 5 (charter rev. 2, [USER]-RULED 2026-09-24,
relayed; `docs/2026-09-23_batched-window-charter.md` §1 row 5; `docs/2026-09-24_window-plan.md` row 5). Conditions:
the logic team's response §4 «B6 / numeric locals» (2026-09-23) and their 2026-09-28 request 3. No named design
gate; D1–D6 below were [AGENT] choices posed at the merge ask and are **RATIFIED** — [USER] Mike 2026-09-30, verbatim,
relayed by the [AGENT] coordinator (cite as relayed): «Agree, go ahead and fix, agree on all 6» — with a fix round
before landing (audit `docs/2026-09-30_numeric-locals-audit.md` F1–F5; §5). Acceptance: ZERO behaviour change
(the gate red only on the 5a pair; baseline unchanged; the whole-corpus choice trace byte-identical). Before =
`main` @ `131a7313`; after = the lane tip.

## 1. What a local is today, and after

Today a local is a `String` at run time (`Param.id`, `Expr.var/ref`, `Assignee.var`, `mapRange`'s vars, the `unseq`
binders, `Scope := List (String × Loc)`); `LocalEnv.lookup` walks scopes inner→outer comparing spellings; the frontend
emits source spellings (`x$shadow1`, `x$cap`) and `$`-temporaries; the decoder synthesizes ~25 more. After:
**`abbrev VarId := Nat`** at every one of those positions; the scope walk is TEXTUALLY unchanged (key equality only)
— the binding discipline (fresh cell per declaration execution, shadowing by scope depth, argument/result slots,
captures as leading pointer parameters) is untouched; C4 owns the env restructuring.

**D1 — ids are DECLARATION ids, per function, assigned by the frontend from go/types objects.** Every `types.Object`
a function declares or uses as a local (params, results, receiver, captures, `:=`/`var`/range/select/type-switch
binders) gets one index in that function's table, allotted at first encounter; a `:=` that REUSES `err` is a use
(`Defs[err] = nil`), so same-block reuse is preserved; the per-iteration loop copy re-declares the SAME object in a
nested scope (one id, several declaration SITES — the runtime walk keeps today's meaning). Two shadowing `x`s = two ids.
The decoder CROSS-CHECKS every source reference: the innermost in-scope declaration of the SAME SPELLING in its
scope-exact R1 environment (Stage E6a, audited construct by construct) must carry the same id — two independent
resolvers (go/types; the decoder's lexical walk) must agree or the program REFUSES BY NAME. That agreement is the
pure-renaming certificate: the runtime's walk by spelling (before) and by id (after) pick the same binding at every
reference. Alternatives: (a) decoder-only per-SPELLING interning (a bijection, no wire change, no declaration
identity); (b) decoder-only per-declaration split (one resolver, no cross-check — a divergence adopted silently).

**D2 — `$`-temporaries stay spelling-interned, by the decoder, per function.** Frontend and decoder temps are
interned on first sight into ids `≥ N` (`N` = the wire table's size), appended with `kind := .temp`; a `$`-spelling
carries NO wire index and a non-`$` spelling MUST (a forgotten site refuses by name). Per spelling per function =
today's shadowing (a bijection). `LowerM` gains a `StateT` layer (temps + base), reset per function; the reader
keeps the R1 environment, now `Array LocalDecl := {name, id, typ}`.

**D3 — the table: `Func.locals : Array LocalName`, `VarId` = index.** `LocalName := {name, kind, pos := "",
wire := ""}` — `name` Go's identifier (a temp's `$`-spelling), `kind ∈ {recv, param, result, capture, local, temp}`,
`pos` = `basename.go:line:col` of the declaring identifier ("" for temps), `wire` = the lowering's spelling when it
differs from `name`. Spellings RETAINED; ids NOT stable across source edits (the charter's clause, in `Syntax.lean`'s
docstring; a consumer reconstructs a binding by `(function, name, pos)` or declaration order). Home: `Func` (default
`#[]`) — the machine never reads it; like `Program.typeDisplays`, carried checked data. Alternative: no `pos`.

**D4 — the wire moves to `golean-native-v3`.** Per function `"locals": [{name, kind, pos?, wire?}]`; `"local": n`
beside the spelling on every SOURCE ident/ref/`declare`/`var` target/param/result/receiver/`var`-decl entry,
`"keyLocal"`/`"valLocal"` beside a range's `keyVar`/`valVar`. Spellings stay on the wire (the redundancy is what
the decoder checks). v1/v2 refuse by name. The twin wire is RE-PINNED with the JSON diff as the written reason; the
certified slow-tier row's `wire-sha256` moves the same way (r55 precedent — the coordinator's step at the train).
Alternative: keep v2, derive everything in the decoder (= D1's alternatives).

**D5 — what the decoder checks (each with a mutant test, refused by name).** (c1) index `< N` and the table's
spelling (`wire` or `name`) equals the node's; (c2) the table: no `$`-prefixed source name, signature kinds, and —
F1 (a) — a `wire` renaming's base spelling (before the first `$`) IS `name` (`x$cap` → `x`), `pos` well-formed
(`basename.go:line:col`); (c3) scope: a source reference's id is declared in the R1 environment at that statement;
(c4) agreement (D1); (c5) `Func.localsOk f = true` — the CORE's total check, in BOTH directions since F1 (b)/(c):
`tableCovers` (tree ⊆ table), `tableNamed` (table ⊆ tree — no dead entry), `sigDistinct`, and the kinds where the
ids occur (`argKinds` recv/param/capture/temp, `resultKinds` result/temp, `recvFirst`, `bodyKinds` local/temp — a
body local cannot claim `recv`). Nothing is repaired. NOT certified (audit F1): `pos`'s CONTENT (recorded
unverifiable); per-object identity beyond what the tree forces (two same-spelled objects folded into one id with
the other entry dropped reads as legal; with the entry kept it is refused as unused).

**D6 — observable text.** No spelling of a local reaches the observation channel (`print`/panic texts, race
reports keyed by `Loc`, the choice trace). The only texts that print a local are REFUSALS — `unbound GoCore
variable address: {id}`, `unbound GoCore result variable`, `unseq: unbound target operand`, every `wellFormed?`
message quoting a binder (`result binder`, `cell … produced by no occurrence`, `sort mismatch`, `guard …
tests/completion`, `store target/value`), `Machine.lean`'s `binder cell '{bind}' is not declared` / `target binder
'{tgt}' has not been produced` — none in any baseline row; they now print the number. For SOURCE locals the
decoder's checks make the unbound cases unreachable; an undeclared `$`-temporary (audit M15) decodes (D2 interns
on sight) and reaches `stuck "unbound GoCore variable address: <n>"`, as `main` did with the spelling (F2). The two
`$`-SPELLING checks that left `wellFormed?` live at the decoder; F3 restores their intent AT THE MACHINE over ids:
`unseqEntryCheck?` (`Machine.lean`), `Step.unseqEnter`'s second premise, consulted by `stepFn` at ENTER — no cell
or target binder already bound in the enclosing environment, every mentioned slot a cell or a bound local — refused
by name before any cell exists; unreachable for a decoded program (binders unique per function; source atoms in
scope — 0 of 1354 corpus wires). `Tests/GoCoreAdmission.lean`'s one pinned text is restated.

## 2. The name-table interface (request 3), pinned in `BridgeSet.lean` (RE-PIN 6)

- Types: `VarId := Nat`; `Param.id`, `Expr.var`/`ref`, `Assignee.var` numeric (the answer to «whether they become
  numeric»: yes, and every other binder position); `Scope := List (VarId × Loc)`; `LocalName`, `LocalKind`, `Func.locals`.
- `Func.localName? f id := f.locals[id]?`; `Func.localsOk` (D5 c5) with `localsOk_covers` («source spellings are
  retained»), `localsOk_named` (no dead entry), the kind lemmas, `localsOk_sigDistinct`.
- The activation's runtime slot: `LocalEnv.lookup_declare_self`/`_ne`, `lookup_pushScope`; `bindParams_lookup`
  (argument `i` at `.base ⟨s.heap.size + i⟩`, ids pairwise distinct); `allocDecls_lookup`; `enterFrame_lookup_arg` /
  `_result` through `enterFrame_declared` (P): `lookup frameEnv (f.args[i].id) = some (.base ⟨s.heap.size + i⟩)`,
  `… (f.results[j].id) = some (.base ⟨s.heap.size + f.args.size + j⟩)` — «table lookup agrees with the activation's
  runtime slot»: `f.localName? (f.args[i].id)` is the `i`-th entry (kind recv/param/capture, `localsOk_argKind`) AND
  that id is bound to the `i`-th entry cell. C4 restates the layout as a function. All in the core audit's required list.

## 3. The change, acceptance, measurement (detail: the handoff)
Core: `Syntax`/`State`/`Unseq`/`Locals` (types, table, `localsOk`), key-type edits in the machine and proof modules,
`stepFn`/`Step` coherence in the same commit. Decoder: the `StateT` layer, `LocalDecl`, c1–c5. Frontend: `locals.go`,
`local` at each source site, `locals` at each function, schema v3. Tests: a test-local injective `String → VarId`
helper; hand-built wires numbered; mutants. Acceptance: `ci --slow` red only on the 5a pair, baseline unchanged, the
choice trace byte-identical, the twin re-pinned with its diff, every theorem AS STATED, elaboration A/B under C3's 1.5× rule.

## 5. Fix round (2026-09-30; audit F1–F5, [AGENT] coordinator dispositions) — in D5/D6 above; lemmas
`localsOk_named`/`_argKind`/`_resultKind`/`_recvFirst`/`_bodyKind` (BridgeSet 126–132, row 116 re-pinned); gate
controls M1/M6/M13/M14(format)/M16; `b4`/`mBareTarget`/`mUnknownSlot` re-pointed to the ENTER check; handoff §3a.
