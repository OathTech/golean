# B6 — numeric locals: lane handoff (`core/numeric-locals-0930`)

[AGENT worker, lane `core/numeric-locals-0930`] 2026-09-30. Window row 5 (charter rev. 2, [USER]-RULED
2026-09-24, relayed). Design note `docs/2026-09-30_numeric-locals-design.md`. Before = `main` @ `131a7313`;
after = the lane tip. Branch complete + the audit ask posed is this lane's end state; merge/push are the
coordinator's and the [USER]'s.

## 1. State (what landed)

`abbrev VarId := Nat` is every local's identity in the core: `Param.id`, `Expr.var`/`ref`, `Assignee.var`,
`Stmt.mapRange`'s variables, the `unseq` binders (`UnseqBody`, `UnseqGraph.stores`), `Scope := List (VarId ×
Loc)`. The scope walk (`LocalEnv.lookup`/`declare`) is textually unchanged. The name table `Func.locals :
Array LocalName` (`{name, kind, pos, wire}`, `LocalKind ∈ {recv, param, result, capture, local, temp}`) is
carried, checked data — never read by the machine. New core module `GoLean/GoCore/Locals.lean`:
`Stmt.declIds`, `Func.ids`, `Func.localsOk` (the decoder's final check), `Func.localsOk_covers`,
`Func.localsOk_sigDistinct`; env-lookup laws in `State.lean`; `namesDistinct_cons`/`_append` in `Unseq.lean`;
the activation-slot lemmas in `Machine.lean` (`Store.alloc_shape`, `bindParams_heap_size`/`_lookup_preserve`/
`_lookup`, `allocDecls_*` likewise, `enterFrame_lookup`/`_arg`/`_result`). `BridgeSet.lean` RE-PIN 6: rows 1–107
byte-identical, rows 108–125 added; `Tests/GoCoreAudit.lean`'s required list gains `GoLean.GoCore.Locals` and
the nine lemmas (144 → 153).

Frontend (`tools/nativefrontend`): `locals.go` (`beginLocals`/`freshLocals`/`localID`/`localIdent`); per-object
declaration ids from go/types (`emitParams`/`emitResults`, the receiver, `emitIdent`, `emitAssignTargetPhase1`,
`emitAddressOf`, `emitLValuePhase1`, `emitFuncLit` — captures pre-registered as kind `capture` under `x$cap`,
the enclosing function's references numbered in its own table — the per-iteration loop copies, the type-switch
binder, `emitDeclStmt`, the range's `keyLocal`/`valLocal`, the goto hoists' `var` and their `declare`→`var`
conversions, `unseq_lower.go`'s `varTarget`, the sync stubs' `forceParamID` drops the index when it forces a
`$a{i}` temporary); every function/method map carries `locals` (a fresh table per declaration/literal/stub;
`[]` for the `$`-only synthesized functions). Unnamed parameters and receivers (spelling `""`, never
referenced) became the `$p{i}` / `$recv` temporaries. Schema `golean-native-v3`.

Decoder (`GoLean/NativeToIR.lean`): `LowerM := ReaderT LowerCtx (StateT LowerSt (Except String))` — the
reader carries the function's wire table and the scope-exact R1 environment (`Array LocalDecl`), the state
interns `$`-temporaries densely after the table (`tmp`); `declLocal` (c1/c2 at a declaration site), `refLocal`
(c3 scope + c4 agreement at a reference), `decodeLocalsTable` (c2), `checkSignatureLocals`, `checkLocalsOk`
(c5); the two spelling checks that left `UnseqGraph.wellFormed?` live here (`binder`, «unknown slot» in
`unseqCheckLocalAtoms`); v1/v2 wires refuse by name.

## 2. Acceptance (evidence: `docs/evidence/2026-09-30_numeric-locals/`)

1. `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow`: PENDING (this section is filled at the run).
2. Whole-corpus choice trace vs `main`: PENDING.
3. Twin: RE-PINNED `baselines/pins/twin-chdriver.wire.json` 0b58402a… → 8a158eff…, reason = the JSON diff
   (schema v2→v3; +12641 `local`, +60 `keyLocal`, +66 `valLocal`, 924 `locals` tables / 2879 entries; 49
   unnamed receivers/parameters `""` → `$recv`/`$p{i}`; every other node identical, key by key). The certified
   slow-tier row's `wire-sha256` moves the same way — the coordinator's step at the train (r55 precedent).
4. Frontend+decode smoke over all 1782 corpus fixtures with the new frontend and the new decoder: 1353
   decode+run OK, 428 frontend-side refusals (the negative/unlowerable fixtures, unchanged classes), 1 decoder
   refusal = the pre-existing BUG-078 materialization budget row; ZERO B6 refusals — no scoping disagreement
   between go/types and the decoder's lexical walk anywhere in the corpus (design D1's certificate held on
   every fixture).
5. Every existing theorem and the packet A/B statements proved AS STATED; totality kept (no `sorry`/axiom/
   `native_decide`; no `partial` in `GoLean/GoCore/`).
6. Elaboration A/B: PENDING.

## 3. PENDING [USER] ratification at the merge ask ([AGENT] choices; design note D1–D6)

- D1 per-object declaration ids from the frontend, cross-checked by the decoder (alternatives: decoder-only
  per-spelling interning; decoder-only per-declaration split).
- D2 `$`-temporaries interned by spelling per function, after the table.
- D3 the table's shape and home (`Func.locals : Array LocalName` with `pos`; alternative: no positions).
- D4 the wire moves to `golean-native-v3` with `local`/`keyLocal`/`valLocal` + `locals`; the twin re-pin.
- D6 the refusal texts that named a local now print its number; the two `$`-spelling checks moved from
  `UnseqGraph.wellFormed?` to the decoder; the three `Tests/UnseqScheduler.lean` rows that pinned them were
  retargeted/retired (`mUnknownSlot` → the machine's unbound-read refusal; `b4`, `mBareTarget` retired), the
  wire mutants `mut-nondollar`/`mut-unknown-slot` keep their named refusals at the decoder.
- Unnamed parameters/receivers respelled `""` → `$p{i}`/`$recv` (an env key only; never referenced).

## 4. Changelog lines (for `docs/changelog/61958f2e-WINDOW.md`)

See the «Row 5 — B6» section and the tool-interface lines added there in this lane's records commit.

## 5. Refresh data for later lanes

- 5b (the `Intn` pick site): the frontend's function maps ALL carry `locals`; a new machine-op's stdlib
  callee rows need no table work; a new source-visible local in a shim is a `$`-temporary or gets an id.
- C4 (block-entry allocation): «declared locals of a block» is `Array Param` with `Param.id : VarId`; the
  slot lemmas state today's entry layout (`s.heap.size + i` / `+ args.size + j`); `Func.localsOk_sigDistinct`
  is the distinctness premise C4's layout function inherits.
- Packet D (equations): `Locals.lean` is in the core aggregator and the audit's required list; the
  `fun_cases stepFn` case list is unchanged (no arm added or removed).
