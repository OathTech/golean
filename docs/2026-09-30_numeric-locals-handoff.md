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

## 2. Acceptance (evidence: `docs/evidence/2026-09-30_numeric-locals/`, README has the commands)

1. `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at the runtime commit `0fb43dcd`: EXIT 1 on exactly the 5a
   pair — `certificate provenance` STALE (changed dependency files; the train's 5a business) and the ONE drift line
   `imported-goose/channel/google-search PASS/membership → FAIL/membership` (the certified slow-tier row — the same
   line packet C and r55 reported). `cases=3791 pass=3553 fail=238` = the pin's 3554 / 237 with that row; every
   other step ok (core audit 153 required; wire boundary incl. the 11 B6 controls; unseq wire 56 mutants; frontend
   pins; eval tests 298; Go tests); `baselines/native-full.tsv` UNCHANGED. Wall 1018 s. Tail: `ci-slow-tail.txt`.
2. Whole-corpus choice trace vs `main` (pre = a detached checkout at `131a7313` with its own frontend and binary,
   post = the lane): BYTE-IDENTICAL — all 30 tsv files identical modulo the `--out` path; 26417 dump rows on both
   sides, concatenated dumps sha256 `1d621c3a…` on both; the same 34 frontend refusals; `summary.txt` identical up to
   the absolute path in the pre-existing BUG-078 line. `choice-trace.txt`.
3. Twin: RE-PINNED `baselines/pins/twin-chdriver.wire.json` 0b58402a… → 8a158eff…, reason = the JSON diff
   (`twin-diff.txt`: schema v2→v3; +12641 `local`, +60 `keyLocal`, +66 `valLocal`, 924 `locals` tables / 2879
   entries; 49 unnamed receivers/parameters `""` → `$recv`/`$p{i}`; every other node identical, key by key).
4. The certified slow-tier row's wire moves dc232a8c… → f448d579… with the same class of diff (zero residual beyond
   the B6 fields; `google-search-wire-diff.txt`) — the coordinator's wire-hash step at the train (r55 precedent);
   this lane records what changed and does not touch `baselines/certified/`.
5. Frontend+decode smoke over all 1782 corpus fixtures with the new frontend and decoder: 1353 decode+run OK, 428
   frontend-side refusals (the negative/unlowerable classes; main's frontend refuses the same 34 non-negative ones),
   1 decoder refusal = the pre-existing BUG-078 budget row; ZERO B6 refusals — no go/types-vs-lexical scoping
   disagreement anywhere in the corpus (design D1's certificate held on every fixture). `smoke.txt`.
6. Every existing theorem and the packet A/B statements proved AS STATED; totality kept (no `sorry`/axiom/
   `native_decide`; no `partial` in `GoLean/GoCore/`); BridgeSet rows 1–107 byte-identical.
7. Elaboration A/B (interleaved, same box, box load 0.5–3.7; `elaboration.txt`), wall s pre → post: StepFn 0.93 → 0.86,
   Machine 3.49 → 3.65 (1.05×, the maximum), MachineEqb 4.41 → 4.42, BridgeSet 0.80 → 0.85 (18 rows more), StateWf
   14.88 → 14.62, MachineSound 59.79 → 60.27 (1.01×), StepErrors 202.82 → 203.78 (1.00×). The C3 1.5× stop rule is NOT
   triggered; `maxHeartbeats`/`maxRecDepth` settings: the same count pre and post, none new or raised.

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
