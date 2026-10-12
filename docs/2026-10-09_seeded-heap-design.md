# Seeded-heap entry for function-level runs (gc-verified's a2): design note — a named design gate, HARD STOP

[AGENT] design worker, lane `design/seeded-heap-1009` (worktree `.claude/worktrees/seeded-design`, off `main` @ `8b53af43`), 2026-10-09
(the worktree clock reads 2026-10-08). Authority: [USER] Mike 2026-10-09, verbatim, relayed by the [AGENT] coordinator — cite as relayed:
«Approved» — for a DESIGN NOTE FIRST; no implementation; every decision below is [AGENT], PENDING [USER]. The request: gc-verified session
gc-verified-e8's [USER]-approved draft (read-only for us: `~/projects/gc-verified/worktrees/integration/next/docs/ai/2026-10-09_mem0-probes.md`
§6.1–6.3; their `docs/ai/2026-10-07_golean-coordination.md` row a2 already says «[USER-GoLean]: trusted surface»). Standing rules: CLAUDE.md
(fail closed with named refusals; total core; latitude on the tape; trusted surface = interpreter + frontend + differential apparatus);
[USER] 2026-10-07 «semantic widenings only if they match real Go» — this request is NON-semantic: `stepFn`, the relation, the drivers'
loops and every pinned statement are untouched; it adds a DRIVER ENTRY beside `runProgramSetupM`, a readout, two CLI flags and a harness
mode. Evidence (11 KB): `docs/evidence/2026-10-09_seeded-heap-design/`.

## 0. What the probes settled today (outputs in the evidence dir; nothing in the repo changed)

- **P1** `go run` (go1.26.5) of hand-written prologues over gc-verified's `p0b/subject.go`: `addNaive(&c0,&c0)` on `[5,7]` → `12 19`; two
  distinct cells → `12 12 / 5 7`; `sum2` over a two-cell CYCLE → `5 2 3`; `swap2(&c0,&c0)` → `42`. **P2** the same package through the pinned
  frontend and `golean native-json-run` (train-r75 build @ main's tip): identical on all four — the whole-program twin works today unchanged.
- **P3** (`probe-seeded-store.lean`: `#eval` through the EXISTING `Store.allocCell`/`storeLoc`/`bindParams`/`allocDecls`/`pinResultLocs`/
  `runConfig`): a two-phase hand seed (zero cells at `b, b+1, …`, then the stores) after `runPkgInitM` runs `inc` (41 → 42), aliased/distinct
  `addNaive` (`12 19` vs `12 12 / 5 7`) and the cyclic `sum2` (result 5; the cells' final values hold `.addr (.base 1)` / `.addr (.base 0)` —
  the raw ids §5 renders seed-relative); `StateWf` holds after the bind in every seeded case. P3 also pins TWO gaps of today's entry
  (unreachable from any CLI flag, so not bugs — but the seeded entry must close them): `bindParams` ACCEPTS a dangling `.addr (.base 99)` at a
  `*int` parameter, the entry store is then NOT `StateWf` (`(wf before, wf after) = (true, false)`) and the run refuses only at the deref
  (`stuck "unbound GoCore heap location"`); an `.int 5` at a `*int` parameter passes normalization (`normalizeValueForTyTy`'s pointer arm is
  the catch-all `return value`) and refuses at the deref. Hence §2's resolver checks every reference BEFORE any cell is written.

## 1. Data types and the seed file

```lean
inductive SeedPathElem where | field (name : String) | index (i : Nat)
inductive SeedValue where
  | int (v : Int) | bool (b : Bool)
  | struct (fields : Array (String × SeedValue))      -- NAMED fields (their JSON example is keyed; their Lean sketch was positional)
  | array (elems : Array SeedValue) | ref (cell : Nat) (path : List SeedPathElem) | nil
structure SeedCell where typ : Ty; value : SeedValue
inductive SeedArg where | scalar (v : GoValue) | ref (cell : Nat) (path : List SeedPathElem) | nil
```
Home: a new total module `GoLean/GoCore/Seed.lean` (after `Multi` in the DAG; nested arrays recurse in the `normalizeListWith` mold, no
`partial`): the types, the resolver, `seedCells`, the three entries and `seedRelative?`. Statements go to `SetupStatement.lean`, proofs to
`SetupSound.lean` (the G-R grain), pins to `BridgeSet.lean` as one RE-PIN with rows ADDED only. Seed file, schema `golean-seed-v1` — parsed
by the CLI through the strict byte parser (`StrictJson.parseBytes`: duplicate keys, bad UTF-8, unpaired surrogates refuse there — BUG-110's
discipline), then exact-key decoding (`requireExactKeys`, the observation decoder's rule):
```
{"schema":"golean-seed-v1","cells":[{"type":<TypeSpelling>,"value":<SeedJson>}, …]}
SeedJson ::= <integer> | true | false | {<field>: SeedJson, …} | [SeedJson, …] | {"ref":{"cell":<nat>,"path":[PathElem…]}} | {"nil":true}
PathElem ::= "<field>" | <nat>      TypeSpelling ::= bool | int | int8 | … | uint64 | [<nat>]T | *T | <Ident>
```
`<Ident>` is the Go spelling of a declared type, resolved over the program's table by `TypeId.unqualified` (the observation channel's own
naming: `main.Node` ↔ `Node`); the SAME spelling is pasted verbatim into the Go twin's prologue (§7) — one file, two consumers. Refused BY
NAME at the CLI (status `error`, exit 1, before any machine step): a schema other than the literal; missing/extra keys at any level; `cells`
not an array; a type spelling outside the grammar — `uintptr`, `float32/64`, `string`, `[]T`, `map`, `chan`, `func`, `interface`, anonymous
`struct{…}`, `sync.*` — each named «not in golean-seed-v1»; an `Ident` naming no declared type or MORE THAN ONE (ambiguity refuses, never
picks); a `ref` whose `cell` is not a nat or whose `path` is not a list of strings/nats; `{"nil": x}` with `x ≠ true`; a `ref`/`nil` object with
extra keys; a number with a fraction or exponent. Value-against-type checking is the core resolver's (§3): the CLI decodes the SHAPE, the
core decides the TYPING once.

## 2. Placement and the two-phase allocation

`runProgramSetupSeededM fuel program name seed args (choices := [])` repeats `runProgramSetupM`'s steps VERBATIM through `runPkgInitM` (find →
arity `func.args.size = args.size` → reserved prefix → `seedGlobals` from `{}` → the existing `StateWf` assert → `runPkgInitM` → `(s₁, choices₁)`),
then: `b := s₁.heap.size` (= `s₁.nextAddr`, the post-init allocator bound — init may ALLOCATE, so `b` is a run quantity, not a program constant:
this is why the core takes seed-RELATIVE values and resolves inside setup rather than pre-resolved `GoValue`s from the CLI, D1); `seedCells
pctx s₁ seed = (sS, seedLocs)`; the arguments resolved against `func.args` (`resolveSeedArgs`); then `bindParams pctx [] sS …`, `allocDecls`,
`pinResultLocs` and the entry config exactly as today. Result `(pctx, c₀, s₃, resultLocs, seedLocs, choices₁)` — the draft's extra `Array Loc`.
`seedCells pctx s₁ seed : Except Stop (Store × Array Loc)`, two phases. Phase 1, `k` in order: `Store.alloc pctx s zero_k typ_k`, `zero_k =
defaultValue typ_k` (the `seedGlobals` mold: address pinned `= .base ⟨b+k⟩`, `.internal` otherwise — provably never fires). Phase 2, `k` in
order: `storeLoc pctx s (.base ⟨b+k⟩) v_k`, `v_k = resolveSeedValue types b seed typ_k value_k` (`storeLoc` normalizes at the declared type; the
empty path is the whole-root write). Every cell exists before any value is stored, so sharing and cycles are plain stores. Resolution of
`ref j path` at an expected `*T`: `j < seed.size`; `seedPathTy types seed[j].typ path` walks the DECLARED type — `.field f` needs a struct
(through `.defined idx` → `.struct fields`, `f` declared; `.defined` over `.defined` descends; `.interfaceDef`/`.opaqueDecl` refuse), `.index i`
needs `.array len _` with `i < len`; the leaf type must equal `T` (`Ty.eqb`; positional `.defined` identity); the `Loc` is built root-first —
`.base ⟨b+j⟩`, then `.field loc (nameOf? idx) f` / `.index loc i` per element — the very `Loc` the machine's own `&c.f[i]` evaluates to. A `ref`
resolves to `.addr loc`; `nil` at a pointer type to `.nil`. `resolveSeedArg` is the same resolver at the parameter's type, with `.scalar v ↦
.ok v` UNCHECKED (the CLI's `entryArgValues` guards scalars, exactly as today — what keeps S4 unconditional, D5).

## 3. Normalization and the refusal catalogue

Resolution yields values already normal at their types (ints range-checked at their kind; struct fields emitted in DECLARED order, the
object's key order irrelevant; arrays of the exact length), and `Store.alloc`/`storeLoc` normalize anyway, so S2 states the cell with
`normalizeValueForTy` applied (honest; a `resolve_isNormal` corollary can drop it later). Core refusals are `Stop.stuck` prefixed `seed:`,
naming the cell, the path and both types — the driver-error precedent (`runProgramSetupM`'s lookup/arity refusals are `stuck` «pending a
driver error type»; a bad seed is a DRIVER INPUT error, neither Go behaviour nor a frontend bug): `seed: cell k: ref to cell j out of range
(n cells)` · `… path .f on non-struct T` / `index i out of range for [n]T` / `unknown field f of T` · `… ref j.path has type *T, *U expected`
(arguments: `argument i: parameter p has type *U; --arg-ref j.path points at T`) · `… nil at non-pointer type T` (v1: `nil` ONLY at `.pointer`;
func/interface cells are non-goals, slices/maps/chans — Go-nilable too — out of v1, all «not in golean-seed-v1», D9) · `… int v out of range
for int8` (no silent wrap) · `… expected array(3), got …` · `… struct T: missing field f` / `unknown field g` / `duplicate field f` (every declared
field REQUIRED, no zero-fill, D3) · `… value at type T not in golean-seed-v1` for a string/float/slice/map/chan/func/interface/sync/unsupported
type ANYWHERE in a cell's type (a struct with a string field is unseedable in v1 — named; strings and floats are the first deferred
candidates). At the CLI: `--arg-ref` at a non-pointer parameter, `--arg-int`/`--arg-bool` at a pointer parameter (the existing «cannot supply»
arm), `--arg-ref`/`--arg-nil` without `--seed` (usage, exit 2), arity as today.

## 4. Exact statements (names = the owed BridgeSet rows; `b := s₁.heap.size`, `n := seed.size`; `seedLoc b k := .base ⟨b + k⟩ = entrySlot s₁ k`)

**S1, the seeded setup equation** (G-R1's sibling, the same premise shape, NO `StateWf` premise — D4):
```lean
def runProgramSetupSeeded_init_stmt : Prop := ∀ {fuel program name seed args choices func s₀ s₁ choices₁ sS seedLocs vals env frameEnv s₂ s₃ resultLocs},
  findFunctionIn? program.funcs ⟨name⟩ = some func → func.args.size = args.size → program.typeDefs.hasReservedPrefix = true →
  seedGlobals ⟨program⟩ {} program.globals = .ok s₀ → runPkgInitM ⟨program⟩ fuel s₀ choices = .ok (s₁, choices₁) →
  seedCells ⟨program⟩ s₁ seed = .ok (sS, seedLocs) → resolveSeedArgs ⟨program⟩ s₁.heap.size seed func.args args = .ok vals →
  bindParams ⟨program⟩ [] sS func.args.toList vals.toList = .ok (env, s₂) → allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
  pinResultLocs frameEnv func.results.toList = .ok resultLocs →
  runProgramSetupSeededM fuel program name seed args choices
    = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs, seedLocs, choices₁)
```
**S2, seed cell `k` at its slot; the frame below `b`; the slot list:**
```lean
def seedCells_cell_stmt : Prop := ∀ {ctx s₁ seed sS locs}, seedCells ctx s₁ seed = .ok (sS, locs) → ∀ (k : Nat) (hk : k < seed.size),
  locs[k]? = some (.base ⟨s₁.heap.size + k⟩) ∧ ∃ v w, resolveSeedValue ctx.types s₁.heap.size seed seed[k].typ seed[k].value = .ok v
    ∧ normalizeValueForTy ctx seed[k].typ v = .ok w ∧ Heap.lookup sS.heap (.base ⟨s₁.heap.size + k⟩) = some (.value seed[k].typ w)
def seedCells_frame_stmt : Prop := … → ∀ j < s₁.heap.size, sS.heap[j]? = s₁.heap[j]?
def seedCells_locs_stmt  : Prop := … → locs = (Array.range seed.size).map (fun k => Loc.base ⟨s₁.heap.size + k⟩)
```
**S3, heap size:** `seedCells_heap_size_stmt : … → sS.heap.size = s₁.heap.size + seed.size`. The entry layout is then G-R3 at the pre-bind store
`sS`: `setup_lookup_arg_from`/`_result_from`/`setup_resultLocs_from`/`setup_heap_size_from` apply VERBATIM with `s₁ := sS` (parameter `i` at
`entrySlot sS i = .base ⟨b + n + i⟩`; `s₃.heap.size = b + n + args + results`). **G-R3 generalizes as is, no siblings; G-R1 and
`runProgramSetup_noInit` are untouched** — S4 ties them to the seeded entry.
**S4, empty-seed erasure** — ONE `Except` equation, errors included (by `seedCells ctx s #[] = .ok (s, #[])` and `.scalar v ↦ .ok v`):
```lean
def runProgramSetupSeeded_empty_stmt : Prop := ∀ (fuel : Nat) (program : Program) (name : String) (args : Array GoValue) (choices : Choices),
  runProgramSetupSeededM fuel program name #[] (args.map SeedArg.scalar) choices
    = (fun (pctx, c, s, locs, ch) => (pctx, c, s, locs, #[], ch)) <$> runProgramSetupM fuel program name args choices
```
**S5, `seed_wf`:** `seedCells_wf_stmt : StateWf ctx s₁ → seedCells ctx s₁ seed = .ok (sS, _) → StateWf ctx sS` (phase 1 by `alloc_wf` on zero
values, `defaultValue_locSup`; phase 2 by `storeLoc_wf`, the resolver's range check being exactly `GoValue.locSup v_k ≤ b + n = sS.nextAddr`),
and `runProgramSetupSeeded_wf_stmt : StateWf ⟨program⟩ s₁ → … = .ok (…, s₃, …, _) → StateWf ⟨program⟩ s₃` (the bind by `alloc_wf`). The premise
`StateWf s₁` is dischargeable in-repo by an OPTIONAL row **S0** `runPkgInitM_wf_stmt : StateWf ctx s → runPkgInitM ctx fuel s ch = .ok (s₁, ch₁)
→ StateWf ctx s₁` (induction over `runInitConfig` with `stepFn_preserves_wf`; the init config is `MachineWf` from `seedGlobals_wf`, env `[]`,
loc-free text — half a session; it also makes a re-asserted check provably never fire).
**S6, the run and the readout:** `runProgramSeededM fuel program name seed args choices : Except Stop SeededReadout`, `structure SeededReadout
where readout : Readout; seedFinal : Array GoValue` := the seeded setup, `runConfig`, `loadMany` of the results, `loadMany pctx sF seedLocs`
(the raw final cells). `runProgramSeededM_eq_stmt` is the definition unfolded (the `runProgramM` shape); `runProgramSeededM_empty_stmt :
runProgramSeededM … #[] (args.map .scalar) ch = (fun r => ⟨r, #[]⟩) <$> runProgramM … args ch`. The pool twin `runProgramPoolSeededOutM`
(`runProgramPoolOutM`'s wiring over the seeded setup — the CLI's driver) carries the same erasure statement. For the logic team: ADDITIVE —
new names only; rows 397, 399–402, 512–527 unchanged; `Readout` unchanged (D6); a seeded entry's `Dom` = S1's premises + S2 + G-R3 at `sS`.

## 5. The `seedFinal` readout

`seedRelative? (b n : Nat) (l : Loc) : Option (Nat × List SeedPathElem)` (pure, `Seed.lean`): `some (rootBase l − b, path)` when `b ≤ Loc.rootBase l
< b + n`, the path read from `Loc.rootPath` (`.field _ f ↦ .field f`, `.index i ↦ .index i.toNat`; a negative index refuses), else `none`.
`CLI.goValueJson` gains a seed MODE `(b, n)`: `.addr l` renders `{"tag":"seedRef","cell":k,"path":["next",0,…]}` under `some`; under `none` the
WHOLE observation becomes the named refusal `Stop.unsupported "seed readout: cell k holds a pointer outside the seed (root address a: a
parameter, result, global or run-allocated cell) — not expressible seed-relative"` (status `unsupported`, exit 1 — never a partial seed).
With a seed the mode applies to `values` too (D7): a pointer-valued RESULT into the seed renders seed-relative and the Go twin can match it
(today the harness refuses every pointer-kind result). The observation gains `"seed": [ <goValueJson of each cell's final value> ]`,
kind-carrying (F15: the leaf kind is part of the observation on both sides; cell `[3]int` = `{"tag":"array","values":[{"tag":"int","kind":
"int","value":11},…]}`) — NOT the bare grammar of the draft's example (disagreement (d), §9). Unseeded runs: mode `none`, `goValueJson`
unchanged (raw `addr` ids), NO `seed` key — output byte-identical. `decodeObservation`: status `ok` accepts the exact key set `{output,
schema, status, values}` (today) OR `{output, schema, seed, status, values}`; `decodeGoValueObservation` learns `seedRef` (`cell` nat, `path` of
strings/nats, exact keys); non-`ok` statuses carry no `seed` (the Go twin cannot observe cells after a panic/fatal).

## 6. CLI flags and parse/refusal rules

`golean native-json-run --input <file> --function <name> [--seed <file.json>] [--arg-int n | --arg-bool b | --arg-ref k[.f|[i]]* | --arg-nil]*
[--fuel n] [--choices …]`, arguments POSITIONAL in command-line order (the `--arg-bool` precedent). `--seed` at most once (duplicate → usage,
exit 2). `--arg-ref` grammar `k ( "." ident | "[" nat "]" )*` — `0`, `0.next`, `1[2]`, `0.a[3].b`; a parse failure exits 2 naming the flag.
`EntryArg` gains `.ref k path | .nil`; `entryArgValues` becomes `entryArgs : … → Except String (Array SeedArg)` keeping every existing arm and
message BYTE-IDENTICAL for `.int`/`.bool` (the wire-boundary controls pin them), adding: `.ref` at a pointer parameter pre-checked against the
seed's declared types with the same `seedPathTy` (the refusal names the flag and the position; the core re-checks — the equation's premise
is the core's); `.ref`/`.nil` at a non-pointer parameter refused; `--arg-ref`/`--arg-nil` without `--seed` refused. Without `--seed` the CLI
calls today's `runProgramPoolOutM` — the unseeded path is not touched; with it, `runProgramPoolSeededOutM`. `coverage-observations` (the
hand-mirrored enumerator driver), `choice-trace` and `enumSetup` REFUSE `--seed` by name in v1 (seeded rows are strict-lane only; mirroring
the seeded setup into the copied drivers is deferred, D6). Pins to update: `scripts/check-wire-boundary` (the entry-argument controls
section: positive and refusal controls), `Tests/GoCoreEval.lean` (decoder exact-key pins), the usage string.

## 7. Differential validation on our side

Row format: strict-lane `params` gains `seed=<file>` (relative to the row's `go_dir`, e.g. `seeds/alias.json`; may co-occur with `depth=`); the
`args` column widens, ONLY when `seed=` is set, to tokens `<int>` | `ref:<k>[.f|[i]]*` | `nil` (`ref:0,ref:0,ref:1`). `scripts/coverage-manifest`
validates both — a `ref:`/`nil` token without `seed=`, `seed=` outside the strict lane, a missing seed file refuse the ROW at manifest time,
never a fall-through. `scripts/diff-coverage` maps tokens to `--arg-ref`/`--arg-nil`/`--arg-int` and passes `--seed` to EVERY machine run of
the row — the default stream AND the three invariance streams: a seeded row keeps the full strict claim. The Go twin:
`tools/coverageharness --seed <file> --args <tokens>` generates in `main()` the prologue `var _golean_c0 T0; …` (phase 1), the scalar and
pointer fills in cell order (phase 2: `_golean_c0.next = &_golean_c1` — sharing and cycles as in P1), the call with `&_golean_cK.path` / `nil` /
`T(v)` arguments, the result observation through a pointer-aware encoder (a `reflect.Pointer` is matched by (address, element type) against
a table of every addressable sub-object of every cell, built BEFORE the call — the type disambiguates `&c` from `&c[0]`; zero-size
sub-objects refuse by name), then `"seed": [...]` = `_goleanObservationValue(&_golean_cK)` per cell through the same encoder. The row then
runs EXACTLY like any other: harness JSON vs machine JSON through `observation-eq`; status/reason policy unchanged; `panic` rows unchanged
(no `seed` key on either side). gc-verified's `seed2go.py` is NOT vendored: it emits a function returning int leaves (their function-level
oracle; pointer leaves unobserved); ours is the OBSERVATION harness — same prologue shape, our encoder, our trust (D8). TRUST:
`tools/coverageharness` is trusted surface #2 and `runProgramSetupSeededM`/`seedCells` join #1 — both flagged. First rows: the P1/P2 shapes
(`inc`; `swap2` aliased/distinct; `sum2` cyclic; `add3` aliased; `addNaive` aliased/distinct — expected BORN PASS, with the baseline re-pin's
written reason) plus refusal controls in `check-wire-boundary` (bad seed file, out-of-range ref, type mismatch, `return &local`).

## 8. Cost and slicing (sessions; the pre-merge audit on top)

- **Slice A — core + statements (~1 session, Fable for the wf proofs):** `Seed.lean` (types, resolver, `seedCells`, the three entries,
  `seedRelative?`), S1–S6 stated and proved (+ S0 optional), BridgeSet RE-PIN (rows added only), `#eval`-then-`rfl` controls (the P3 shapes),
  `scripts/mem-callsites.tsv` rows for `seedCells`' raw `Store.alloc`/`storeLoc` sites (`check-mem-callsites`), core-audit enrolment. THIS is the
  first slice for their initial scope (non-nil pointer arguments): the statements are the deliverable; `nil` is one resolver arm.
- **Slice B — CLI + observation (~1 session, Opus):** seed-file decoder, `EntryArg` extension, the flags, `seedRef` rendering + decoder arms,
  `check-wire-boundary` controls, GoCoreEval pins, usage. **Slice C — differential (~1 session, Opus):** harness `--seed`, manifest/diff-coverage
  tokens, the first seeded rows + refusal controls, baseline re-pin with its reason, `scripts/ci --diff` green.
- Deferred, not costed (D9): string/float leaves; seeds in the enumerator/tracer; a `MachineWf` corollary for `c₀`; their optional «prologue
  state ≅ seeded setup» lemma — DECLINED for now: a statement about a LOWERED program's run up to the call under the allocator-renaming
  quotient, not cheap; the differential row is the evidence that the two twins agree.

## 9. Decisions (all [AGENT], PENDING [USER]) and disagreements with the draft

- **D1** Placement after `runPkgInitM`, before `bindParams`; `b = s₁.heap.size`; the core takes seed-RELATIVE `SeedValue`s and resolves inside
  setup (init may allocate). **D2** Type spelling = §1's Go grammar; `Ident` resolved by `TypeId.unqualified`, ambiguity refuses. **D3** Struct
  values name their fields; every declared field REQUIRED (no zero-fill); arrays exact length. **D4** NO runtime `StateWf` re-assert after
  seeding (deviation from draft item 4): the theorem `seedCells_wf` says what the check would, and S4 stays unconditional so every existing
  proof carries over; alternative: re-assert + S0 (then the check provably never fires). **D5** Scalars pass through the core unchecked
  (`entryArgValues` guards them, as today); refs and nil are checked in the core AND at the CLI. **D6** `SeededReadout` beside `Readout`
  (unchanged); sequential `runProgramSeededM` + pool `runProgramPoolSeededOutM`; the enumerator, tracer and `enumSetup` refuse `--seed` by
  name in v1. **D7** `seed` key on `ok` only when `--seed` is given; new tag `seedRef`; with a seed, pointer-valued results render seed-relative
  too; an escaping pointer refuses the whole observation (`unsupported`); unseeded output byte-identical. **D8** Corpus: `params` `seed=`, `args`
  tokens `ref:`/`nil` under `seed=`, strict lane only; the Go twin is `tools/coverageharness --seed` (TRUSTED SURFACE #2 change); `seed2go.py` not
  vendored; `runProgramSetupSeededM` joins #1. **D9** v1 = int/bool/struct/array/ref/nil exactly as their non-goals; everything else refused by
  name; strings/floats first on the deferred list. **D10** Refusal classes: file/flag → CLI `error` (exit 1) or usage (exit 2); resolution/
  typing → `Stop.stuck` «seed: …»; readout escape → `Stop.unsupported`.
- Disagreements with §6.3 of the draft: (a) the post-seed `StateWf` assertion (D4); (b) `nil` «at pointer, func or interface types» → pointer only
  in v1 (D9); (c) `SeedValue.struct` named, not positional (their own JSON example is keyed); (d) `seedFinal` observed kind-carrying through
  `goValueJson` + `seedRef`, not `[[11,22,33],…]` (F15; the Go twin's reflect encoder is the existing one); (e) `seedFinal` in the core is the raw
  `Array GoValue` — the seed-relative rendering with its refusal lives in the observation layer over the pure `seedRelative?`; (f) the
  prologue-isomorphism lemma declined (§8). Everything else — the API shape, the order, the two phases, the five proof obligations, the CLI
  flags, the additive observation key, the Go-prologue oracle — adopted as drafted.

## 10. Rulings (2026-10-12)

[USER] Mike 2026-10-12, firsthand («Agree on the two strategic questions, let's do it»), on the
[AGENT] classification that of D1–D10 two are strategic, six are the customer's interface, the rest
engineering: **GO** — the entry is built, three slices, with the trusted-surface #2 change (the
harness's `--seed` mode) and the new entry joining #1 accepted; **D4 RULED** — no runtime `StateWf`
re-assert after seeding, the theorem stands. D2, D3, D6, D7, D9, D10 and the six disagreements go to
gc-verified for confirmation: `docs/2026-10-12_seeded-heap-note-to-gc-verified.md`. D1, D5 and the
v1 refusals of the enumerator/tracer are engineering, [AGENT]. Slice A starts on their answer.

**gc-verified's answer (2026-10-12, relayed by the [USER] Mike, cite as relayed): CONFIRMED — all six
deviations (a)–(f) and the v1 value set.** Their reasoning, as relayed: their M-mem-0 statement draft
had already reconciled with this note on 2026-10-09 (its §9.2); (a) nothing in their statement package
or checker consumes `StateWf`, neither G-R1 nor S1 carries that premise, so the optional S0 row is NOT
needed now; (d) their statement reads raw `GoValue` cells, never JSON, and their harness reads only
`status` and `values`, the `seed` key appearing only under `--seed`, so the existing lanes are
unaffected; (b), (c), (e), (f) and the value set are adopted on the draft or strictly inside what they
need. Downstream on their side when slice A lands: a GoLean re-pin (a pins ruling), then the
`SeededSetup` instance on their `mem0/statement-draft`, closing that draft's Q2 (source-side
inhabitation). **Slice A starts** (lane `core/seeded-heap-a-1012`).

**Slice A landed on the lane (2026-10-12, [AGENT worker, lane `core/seeded-heap-a-1012`]).** Delivered as
designed with three engineering choices inside D1/D5: (i) the recursive positions of `SeedValue` are
`List`s (kernel-reducible structural recursion; the JSON shape is the CLI's); (ii) the pool twin lives in
`SeedPool.lean` (it needs `Multi`; `Seed.lean` stays light), its erasure theorem beside it; (iii) the
type-admission check of §3 is the resolver's own refusal at the leaf (an int at `string`, a struct
missing its string field) — the same refusal, no second walk. One statement refined: S5's
`runProgramSetupSeeded_wf` carries the premise «every scalar argument is loc-free» (D5 passes scalars
unchecked; the CLI's are ints and bools). Also: the resolver RANGE-CHECKS ints at their kind (the
normalizer would wrap); refusal texts render types through `Ty.dynamicName`; `seedLocs` is the `List`
form so the controls pin by `rfl`. Controls (`#eval` first, 21): the P3 shapes over a hand table (a
cycle between two `Node` cells, `&c0.next`, `&c0[1]`, seed-relative resolution over a non-empty store),
the refusal catalogue by name (the `seed: cell k:` / `seed: argument i:` prefix on all three diagnostic
classes; a type mismatch names the path, `ref 0.next has type *Node, *int expected`; a struct with a
blank field `_` is refused by name — Go literals cannot set one), the S4/S6 instance on the G-R control
program. The pre-merge audit (Fable, 2026-10-12) found no blocker; its HIGH (the prefix promised to
gc-verified had been stripped by a bad edit) and MEDIUM (a duplicate RE-PIN number — this is RE-PIN 18)
and the LOWs (phase-1 refusals now cell-marked; the pool driver module upstream of the proofs; the
docstring's «checked BEFORE any cell is written» corrected to «a refusal discards the whole setup») were
fixed before the merge ask. **Slice B (CLI + observation) starts from here**: the seed-file decoder maps
the §1 grammar onto `SeedCell`/`SeedValue` — type spellings resolve to `Ty` by `TypeId.unqualified` over
the table with ambiguity refusing (D2; `TypeEnv.lookupName?` matches the full key and is NOT that scan —
slice B writes its own); `EntryArg` gains `.ref`/`.nil` → `SeedArg`; the flags of §6 call
`runProgramPoolSeededOutM` (`SeedPool.lean`, upstream of the proofs); `goValueJson` gains the seed mode
over `seedRelative?` (§5).

**Slice B landed on the lane (2026-10-12, [AGENT worker, lane `cli/seeded-heap-b-1012`]).** No core edit. The
decoder is `GoLean/SeedFile.lean` (total, fuel-bounded by the parse's nesting bound); `EntryArg` gains
`.ref`/`.nil`, the per-argument check is factored (`entryFunc`/`entryArgCheck`) so `entryArgValues`' texts stay
byte-identical and `entrySeedArgs` adds the seed arms; `goValueJson` is one walk with a location renderer
(`goValueJsonWith`: raw ids for unseeded runs, `seedLocJson` over `seedRelative?` for seeded ones); `seededObs`
adds the `seed` key. Engineering choices inside §1/§5/§6, [AGENT]: (i) `SeededReadout` does not carry the seed
base `b`, so the CLI reads it from `runProgramSetupSeededM`'s slot 0 — the same pure call the pool entry makes
first (init runs twice on a seeded run; a `base` field in `SeededReadout` would be a core change, not made); (ii)
under seed mode the seed-relative rule covers EVERY location (slice/map/chan bases too), not only `.addr` — an
in-run allocation refuses rather than leaking a raw id; (iii) the number rule is enforced on the TOKEN (a
lexical pre-scan), since the parsed `JsonNumber` of `1e2` equals that of `100`; (iv) an object with a `ref` or
`nil` key IS that form (§1), so ANY struct with a field named `ref`/`nil` is not expressible in v1 (the
refusal names this limit — review LOW-1); (v)
`byte`/`rune` refuse with a hint (`uint8`/`int32`) — §1's grammar does not list them; (vi) a declared type
spelled like a builtin (in v1 or outside it) makes the builtin spelling ambiguous (D2's rule applied); type
literals are recognised only after the `<Ident>` branch, so `channel`/`funcTable` resolve as declared types
(review MEDIUM-1); (vii) a `seedRef` decodes only
in an observation carrying `seed`, with `cell` below its length; (viii) `--arg-ref`/`--arg-nil` at a
frontend-quarantined parameter refuse at the CLI (no pointer type to resolve against). Slice C (harness
`--seed`, manifest/diff-coverage tokens, the first seeded rows, the re-pin) starts from here. **Slice C also
carries a CORE RE-PIN** (slice B pre-merge review LOW-2, 2026-10-12): `SeededReadout` gains `base : Nat`
(the post-init bound `b`), retiring the CLI's second `runProgramSetupSeededM` call (init twice per seeded
run; pure and inert, measured unmeasurable). S6 `runProgramSeededM_eq_stmt` (BridgeSet row 599) and the
two erasure statements (rows 600–601) spell the `{ readout := …, seedFinal := … }` literal, so this is a
RE-PIN with CHANGED rows, not rows added only — it needs its own written reason and the logic team's notice.

**Slice C landed on the lane (2026-10-12, [AGENT worker, lane `cli/seeded-heap-c-1012`], stacked on `train4/stage-1012`).** No core
edit; the `SeededReadout.base` re-pin above stays OPEN (slice C did not need it: the CLI's second setup call is untouched). Delivered:
**the Go twin** `tools/coverageharness --seed <file> --args <tokens>` (`tools/coverageharness/seed.go`; trusted surface #2): at
GENERATION the file's bytes, envelope, value shapes and type spellings are checked and refused by the classes `GoLean/SeedFile.lean`
refuses (strict UTF-8, duplicate keys, number tokens with a fraction or exponent, the `ref`/`nil` forms and their v1 limit, every type
class outside v1, qualified names); the generated `main` then allocates every cell with `new(T)` (the spelling pasted — an undeclared
or function-local `<Ident>` is a compile error at `go run`, loud), fills them in cell order BY REFLECT with the resolver's typing (ints
range-checked at their reflect kind, never wrapped; every declared struct field required and no other; a blank field refused; arrays of
the exact length; `nil` only at a pointer; a `ref` walked along the DECLARED type — no pointer followed — and its target type required
to equal the pointer's element type), binds the arguments (`ref:` by a type assertion to the parameter's type, `nil`, `T(v)`), calls
the subject and observes. **How a pointer becomes seed-relative, and why it is exact:** the pointer is matched by (address, element type)
against every addressable sub-object of every cell (roots, struct fields, array elements, recursively), walked from the live cells at
observation time (heap objects; gc's collector does not move them). For a non-zero-size element type the match is unique — two distinct
sub-objects at one address overlap, so one contains the other; equal types mean equal sizes, so the containment is at offset 0 with
nothing beside it, i.e. a type containing itself by value, which Go forbids — and no non-seed object can sit at that address either
(live non-zero-size objects do not overlap). So «found» is exactly «this cell, this path» (field names as declared, indices as ints:
the machine's `seedRelative?` path) and «not found» is exactly «outside the seed», which refuses the WHOLE observation with status
`unsupported` and GoLean's text class («seed readout: result i / cell k holds a pointer outside the seed …»; the Go side names no root
address). A zero-size element type has no such guarantee and refuses by name. **The manifest and the runner:** strict-lane
`params` take `seed=<file>` (relative to the case dir, no `.`/`..`, must exist; may co-occur with `depth=`; each key once); `args` take
`<int>` | `ref:k(.f|[i])*` | `nil` (a `ref:`/`nil` token without `seed=` refuses the row; `seed=` on an enumerating lane refuses), all
by name in `scripts/coverage-manifest` AND re-validated in `scripts/diff-coverage`, which maps the tokens to `--arg-int`/`--arg-ref`/
`--arg-nil` and passes `--seed` to the default run, the three invariance streams and the depth guard. **Rows:** 12, all BORN PASS under
`Corpus/coverage/exec/seeded/` (tag `seeded`): the G-R control program widened by an allocating initializer (the empty seed — S4's
erasure — and a cell added to the global and the init-allocated box), `addNaive` aliased (20/20, one cell 20) and distinct (12/19), a
two-cell cycle returning a pointer into the seed (`seedRef` cell 1) and relinked (the `seed` key shows the mutated pointers), a pointer
argument into an array field (`ref:0.a[1]`), a pointer result into one (`seedRef` cell 0 `["a",2]`, through a `*int` cell pointing at
`a[1]`), a nil-terminated list walked from a `ref` and from `nil`, a nil dereference past its end (panic, no `seed` key on either
side), and a result-less `swap` of two `int8` cells (the `seed` key alone is the observation). The seed files sit beside each case's `main.go` (`seed-<name>.json`; §7's example `seeds/alias.json` would be a husk case directory to `scripts/check-coverage`). Each row's two observations were read
and compared by hand as well as by the runner.
Engineering choices, [AGENT], and where the code departs from §7 (the code wins): (i) the fill is REFLECT at run time, not generated
assignments — the typing checks need the program's types, which the generator does not have, and unexported fields are reached
through `reflect.NewAt` (the assignment the prologue would write); (ii) the address table is walked AT OBSERVATION, not built before
the call (§7) — the same table, since the cells' layout is static and they do not move; (iii) **`choice-trace` SEEDS** (single-case
mode; refused in `--batch`): §7 did not mention that a strict PASS includes the depth guard, which runs the tracer, and the tracer
refused `--seed` in v1 — so a seeded row could never complete its strict claim. The tracer's v1 refusal was engineering («D1, D5 and the
v1 refusals of the enumerator/tracer are engineering, [AGENT]», §10), so it is lifted for the tracer only: `CLI.EnumProgram` gains
`seeded?`, placed after init by `EnumProgram.entryStore` (the core's own `seedCells` then `resolveSeedArgs`, `runProgramSetupSeededM`'s
order), and the tracer's driver agreement compares the tracer and the enumerator driver against `runProgramPoolSeededOutM` on the raw-id
rendering; `explore` and the dedup seed refuse a seeded program by name, and `coverage-observations` still refuses the flags (D6);
(iv) the ESCAPING POINTER is two CONTROLS, not a corpus row: both sides refuse with status `unsupported`, and a refusal never passes, so
the row would be red by design — the machine's refusal is `scripts/check-wire-boundary`'s `seed-escape` (slice B), the Go twin's is
`tools/coverageharness/seed_test.go` (`escaping result`, `escaping cell`); (v) the Go side refuses EVERY `\u` surrogate escape (Go's
decoder would turn an unpaired one into U+FFFD silently; GoLean accepts a paired one — the harness refuses it, fail closed); (vi) a
`ref:`/`nil` argument needs a parameter SPELLED `*T` on the Go side (a named pointer type refuses there); (vii) a seeded `ok` subject
may return nothing (its cells are observable; an unseeded one still must return a value); (viii) the unseeded generator output is
byte-identical (the template's three insertions are empty), checked over all 3953 unseeded rows. **What v1 does not cover** (named
refusals on one or both sides, never a silent pass): the enumerating lanes (no seeded membership/confluent/racy rows); string, float,
slice, map, channel, function and interface values in cells; a slice/map/chan observation based in the seed (the machine renders its
base seed-relative, the Go twin refuses the kind); a pointer to a zero-size type in an observation; structs with a field named `ref` or
`nil`; function-local types in a seed (ambiguous or unnamable from `main`); named pointer parameter types; variadic subjects; paired
surrogate escapes; and the init-twice cost of a seeded run (the `base` debt above).
