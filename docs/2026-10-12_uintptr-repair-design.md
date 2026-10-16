# `uintptr` runtime identity — the REPAIR half, design note and measured scope (2026-10-12)

Lane `core/uintptr-repair-1012` (worktree `.claude/worktrees/uintptr-repair-1012`, off `main`
@ `d4be5dca`). Authority: [USER] Mike 2026-10-12: (D6: both halves agreed — refuse now, repair soon) (`docs/2026-10-12_release-readiness.md` §5 D6, item 26; relayed by the [AGENT]
coordinator). The REFUSE half landed on `main` the same day (BUG-124, FR-38, lane
`fix/uintptr-refuse-1012`). This lane is a NAMED DESIGN GATE — a hard stop: the deliverable is
this note; nothing under `GoLean/` is touched here. Every decision below is [AGENT] unless marked.

**The gate line.** For the recommended shape — a distinct `IntKind.uintptr` whose width is the
platform's `intBits` (D1 = I1 + W1 below), the two observation seams left as they are (D2 = O1) —
§2 finds: NO pinned statement text moves (BridgeSet, the equation set, the frozen pool surface),
NO wire schema moves (`golean-native-v3` already spells `{"int":"uintptr"}`; the decoder is the
only side), NO observation-format move, and the proof work is mechanical (two `cases` sites,
both closed by their existing tactic combinators, zero text edits expected). **Under that shape the
gate is open and the implementation is a plain lane.** Two things keep this a [USER] decision
rather than a self-adjudication: the shape itself (D1/D2) and one customer-visible, non-pin cost
(§2.6: the logic repository has two exhaustive `match`es over `IntKind` that stop compiling at
its next re-pin — two one-line arms on its side). The alternatives (W2, O2) close the gate: W2
edits a definition the layout proofs consume; O2 is an additive observation-format change. The
lane STOPS here either way.

## 1. What the repair is in today's core

### 1.1 Where `uintptr` collapses

One site. `GoLean/NativeToIR.lean:384-399` `intKindOfName` is the decoder's only reading of a
wire `int` name (one caller, `decodeTy` `:450-452`), and `:398` is `| "uintptr" => pure .uint64`.
`GoLean/GoCore/Value.lean:7-19` `inductive IntKind` has no `uintptr` constructor (`int`, `uint`,
`int8`…`uint64`, `unbounded name`). After decoding, `uintptr` and `uint64` are the same `Ty`
(`.int .uint64`), so every identity comparison in the core is right about the Ty it sees and
wrong about the program.

The wire is NOT part of the defect: `tools/nativefrontend/wire.go:788-789` emits
`intType("uintptr")`; `mono.go:1225-1226` (`renderTypeKey`, the stencil key) and
`declaration.go:123` (the I1 declaration layer) spell it distinctly; `docs/cli.md:178` lists it
among the `int` names of `golean-native-v3`. The declaration layer on the Lean side keeps it
distinct too: `GoLean/GoCore/Declaration.lean:24` `Basic.uintptr`, `GoLean/NativeDeclaration.lean:40`
(and `Declaration.lean` mentions `IntKind` nowhere — no bridge to change).

### 1.2 What reads the kind — every site, by class

**(a) Width, arithmetic, conversion — must stay 64-wide (gc linux/amd64).** All generic in the
kind through `IntKind.bitsAt`/`bits?`/`signed`/`normalize` (`Value.lean:38-78`):
`Ops.lean:387-393` `tySizeAlignTy` (`.int kind => kind.bitsAt p`; layout), `:2163` the normalizer
arm (`kind.normalize value`), `:2287-2289` `isNormalForTyTy`, `:3223` `defaultValueTy`
(`.int 0 kind`), `:3509` `valueAsIntValue`, `:3850-3895` the arithmetic/bitwise results (through
`IntKind.compatibleResult`, `Value.lean:153` — `==`/`isFlexible`, no constructor list),
`:3859-3867` `intKindBitWidth`/`intKindUnsignedNat` (through `bits?`), `Seed.lean:87` `seedIntFits`
(through `bits?`/`signed`), `Machine.lean:1506-1512` `renderPrintOperand` (`.unbounded` arm +
wildcard: gc's `printuint` decimal — `builtins/print/uints` prints a uintptr today and stays
PASS), `CLI.lean:97-99` `--arg-int` (through `normalize`). Three functions enumerate the
constructors and need an arm: `IntKind.name` (`Value.lean:21-32`), `IntKind.bitsAt` (`:38-50`),
`IntKind.signed` (`:55-66`). `Ops.lean:205/211` `floatBitsApply` names `.uint64` for
`math.Float64bits` — correct and untouched (that function returns uint64, not uintptr).

**(b) Identity — the comparison sites, all through `Ty`'s structural equality** `Ty.eqb`
(`Value.lean:610-627`: `.int k₁, .int k₂ => k₁ == k₂`; the `BEq Ty` instance `:634`), so a
distinct constructor fixes all of them at once with no edit:
- type assertion to a concrete target: `Ops.lean:3329-3349` `typeAssertValue`
  (`dynTy == targetTy`; the slice/pointer probes go through `Ty.eqb`'s structural descent);
- type switch: the frontend lowers it to assertions (`tools/nativefrontend/emit.go:4990`
  `emitTypeSwitch`), the same site;
- interface `==`/`!=`: `Ops.lean:3549` `valueEq`, the box-vs-box arm (`:3631-3632`, `if dynL != dynR`: different
  dynamic types → false);
- `map[any]` keys: `Ops.lean:3801-3810` `mapEntryIndex?` compares through `valueEq` at the key
  type (an interface key type → the box-vs-box arm), from `mapLookupValue` `:4037`;
- interface satisfaction (the old branch's `method-parameters`/`method-results` rows, NOT among
  today's six): `Ops.lean:1927-1934` `satisfiesMethodSig` compares `params == req.params &&
  results == req.results` (Ty lists), reached by `firstUnsatisfiedMethod?` `:2038` /
  `dynamicImplementsInterface` `:2078`.

**(c) Names — identity never keys on them (S3), but they become right:** `Ty.dynamicName`
(`Value.lean:647-649`, `.int kind => kind.name` — the observation `dynamic` field, contract
`reflect.Type.Name()`, which answers `uintptr`); `Ops.lean:1539-1540` `goTypeNameForMessage`
(panic text: `interface conversion: interface {} is uintptr, not uint64` — today the machine
would spell `uint64` there).

**(d) The atomics family — the one place the kind is ENUMERATED in the core:**
`Machine.lean:2757-2759` `atomicKindOk : IntKind → Bool` (`.int32 | .int64 | .uint32 | .uint64`)
and the decoder twin `NativeToIR.lean:1105-1107` `asAtomicOp?` (`.int k@.int32 | … | .int k@.uint64`).
Both must admit `.uintptr` in the same commit, or the five PASS rows `atomics/ops/{load-store,
add,swap,cas}-uintptr` and `atomics/typed/uintptr` go red at decode. `Machine.lean:2815`
`atomicCompute` and `StateWf.lean:6771` `atomicCompute_locSup` are generic in the kind. The
frontend side (`tools/nativefrontend/atomics.go:76` `"Uintptr": "uintptr"`, `:174`) already
emits the distinct name; the stdlib register row `docs/stdlib-admission-register.md:443`
(`shadow-type sync/atomic.Uintptr`) and `scripts/check-stdlib-register` (frontend tables byte for
byte) are untouched — only `atomics.go:69-70`'s comment («realizes as uint64 — the R1 pin») is
stale.

**(e) The observation seams — refuse `uintptr` by name today, on both sides:**
`GoLean/CLI.lean:296-301` `goValueJson` emits `kind.name` (generic — after the repair a
`.int v .uintptr` value WOULD spell `{"kind":"uintptr"}`), `:510-532` `decodeGoValueObservation`'s
string table has ten kinds and refuses `"uintptr"` (`unknown integer kind`; comment `:514-517`
states why: the machine could never emit it); `tools/coverageharness/main.go:574-575` the Go
observer refuses `reflect.Uintptr` (`unsupported Go observation kind uintptr`). `docs/cli.md:255`
documents «ten concrete integer kinds (`uintptr` is lowered as `uint64`)».
`Tests/GoCoreEval.lean:3123-3125` pins the Lean-side refusal. Whether these move is D2 (§5).

**(f) Everything else that mentions the kind is a quantifier, not a constructor:**
`Syntax.lean:232` (`intLit`'s default kind), `:803` `atomicStmt (kind : IntKind)`,
`Machine.lean:2740` `AtomicOp.kind`, `:1542` `intElems`, the congruence lemmas
`MachineSound.lean:3818-3911` (`{k : IntKind}`), `IntKind.normalize_zero` `:4305`,
`StateWf.lean:1798` `IntKind.normalize_idem` (both case on `bits?`, not the kind), the `Eqb`
modules (`SyntaxEqb.lean:203/872`, `MachineEqb.lean:384`, `StateEqb.lean:186/286` use
`IntKind.beq_sound`), `Equations.lean:995/1365`, `BridgeSet.lean:2468/2808`,
`Tests/EquationClient.lean:1299/1631`.

### 1.3 The old branch as the guide (not a rebase)

`origin/typed-uintptr-identity` @ `5f185fb3` (2026-09-06, off `47195683` 2026-09-05) is 64
commits / 1166 files behind-and-beside `main`, but its REPAIR is ONE commit, `5f185fb3`, whose
code footprint is small: `Value.lean` +4 (constructor and three arms, width `8 * p.wordBytes`),
`Machine.lean` `atomicKindOk` +1 arm, `NativeToIR.lean` the two arms, `Platform.lean` a
docstring, `Syntax.lean` a docstring, `CLI.lean` the decoder's eleventh kind,
`Tests/GoCoreEval.lean` three tests, `tools/coverageharness/main.go` the observer's `Uintptr`
arm, 8 corpus rows `ints/uintptr-identity/*`, and a 246-file evidence tree with `--slow`
certificates (retired apparatus). Its design note (`5f185fb3:docs/2026-09-06_uintptr-identity-repair.md`)
cites spec#Numeric_types / spec#Type_identity / spec#Method_sets / spec#Type_assertions — the
same ruling this note relies on. Every line of it maps onto today's core at the sites in §1.2;
the only divergences this note recommends are the width arm (W1, §5) and keeping the observation
seams (O1, §5).

## 2. Proof and pin impact

### 2.1 Proofs that case on the constructors — the mechanical set

Exactly two proof sites split on `IntKind` (grep of `cases kind|cases k|cases a <;> cases b`
over `GoLean/GoCore/`; the other hits are `ConvKind`, `FloatKind`, `SyncKind`, `LocalKind`, `Nat`):

1. `Ops.lean:936-972` `tySizeAlignTy_align_pow2`, the `.int kind` leaf at `:967-971`:
   `cases kind <;> simp only [IntKind.bitsAt, …] at hb <;> subst hb <;> (first | exact hp.1 |
   exact ⟨0, by decide⟩ | … | exact ⟨3, by decide⟩)`. With W1 (`| .uintptr => some p.intBits`)
   the new goal is `(p.intBits / 8).isPowerOfTwo`, the `.int`/`.uint` goal, closed by
   `exact hp.1` — zero text edits. (With W2, `some (8 * p.wordBytes)`, the goal is
   `(8 * p.wordBytes / 8).isPowerOfTwo`, which `Platform.PowTwoAligns` (`Ops.lean:840-841`:
   `(p.intBits / 8).isPowerOfTwo ∧ p.maxAlign.isPowerOfTwo`) cannot discharge: a third conjunct,
   `gcAmd64_powTwoAligns` `:844` gains a component, and the `wideIntPlatform` control `:1184`
   (`intBits := 48`, `wordBytes` 8) becomes a platform whose `uintptr` is wider than its `int` —
   a definition change, not a re-elaboration.)
2. `StateEqb.lean:102-107` `IntKind.beq_sound`: `cases a <;> cases b <;> first | rfl |
   exact congrArg _ (eq_of_beq h) | exact Bool.noConfusion h` — 12×12 → 13×13 goals, the
   diagonal by `rfl`, the off-diagonal by `Bool.noConfusion` on the derived `BEq` — zero edits.

Everything else re-elaborates unchanged: the `deriving Repr, BEq, Inhabited, DecidableEq`
instances; `IntKind.normalize_idem` and `normalize_zero` (case on `bits?`); the `*_int_congr`
family and `atomicCompute_locSup` (kind-generic); `isNormalForTyTy_sound` (`StateWf.lean:1950-1959`,
through `normalize_idem`); the `Ops.lean:4868-4875` pins (`rfl` on a kind variable); the three
`Eqb` modules (through `beq_sound`). No `StateWf` invariant enumerates kinds. Classification by
inspection of the tactic text; the implementation lane's step 0 is the probe build that measures
it (§4).

### 2.2 Pinned statements — none move

- `GoLean/GoCore/BridgeSet.lean`: the two rows that mention the kind, `:2468` (`evalE_intLit`,
  `(kind : IntKind)`) and `:2808` (`exec_atomicStmt`, `{kind : IntKind}`), quantify over the
  TYPE. Their text is unchanged; their proofs are the equation lemmas, kind-generic.
- The equation set `Equations.lean:995/1365` and the client's pins `Tests/EquationClient.lean:1299/1631`
  (`scripts/check-equations`: exhaustive enrollment, type-identical pins): unchanged text.
- The frozen pool surface (`scripts/check-pool-spec`: `PoolStep.lean` + `PoolStatement.lean`
  hashed whole, `docs/specs/pool-relation/FROZEN.sha256`): zero mentions of `IntKind` or
  `uint64` in `Pool*.lean`/`Multi*.lean` (`grep` count 0). The hash does not move.
- `GoLean/GoCore/Platform.lean:30` already documents `intBits` as «Width of `int`/`uint` (and
  `uintptr`)»: W1 is the documented reading; the old branch's W2 rewrote this line.

### 2.3 Wire schema — unchanged

`golean-native-v3` spells `{"kind":"int","int":"uintptr"}` today (`wire.go:789`, `docs/cli.md:178`);
every program that lowers today lowers to the same bytes after (the guard only REFUSES; it never
rewrites). The raft twin (`scripts/check-frontend-pins`, byte-exact) contains no `uintptr`
(`grep -rl uintptr raftsubject raftharness` is empty) and is unaffected either way.

### 2.4 Observation format — unchanged under O1, additive under O2

Today a `uintptr` value is unobservable by construction: the frontend refuses boxing/assertion
positions (BUG-124), the machine cannot produce the kind, the Go observer refuses `reflect.Uintptr`
at `go-observation`, the Lean decoder refuses `"uintptr"` at `lean-observation`. After the repair
under **O1** (seams untouched): a program RETURNING a `uintptr` (or a box holding one) is still
red by name at BOTH seams — the machine emits `{"kind":"uintptr"}`, its own decoder refuses it
(`CLI.lean:532`), the harness refuses first (`main.go:575`) — so `golean-observation-v1`'s
documented kind set stays ten and `docs/cli.md:255` changes only its parenthesis (`uintptr` is
no longer «lowered as uint64»; it is «refused at the observation seam»). The six probe rows
return `bool`/`int`, so they PASS without touching the seams. Under **O2** (the old branch's
choice): both seams accept `uintptr` with the unsigned 64-bit range, `docs/cli.md:255` says
eleven, `Tests/GoCoreEval.lean:3123` flips to a genuinely unknown kind (`uint128`) plus the two
range tests of `5f185fb3`, and two readout rows are born — an ADDITIVE format change, consumer-
visible (a kind value that was refused is accepted). D2 in §5.

### 2.5 The refusal's records — the two atomics twins

`Machine.lean:2757` `atomicKindOk` and `NativeToIR.lean:1106` are the decoder/machine twin of one
decision (the wave-1 kind set, `docs/2026-09-03_atomics-w1-design.md` §1: «`uintptr` is realized
as `uint64` throughout the frontend — inventory R1's pin»). Admitting `.uintptr` in both is the
intended widening, with no new op, no new choice site, no pool-statement text (the atomic rules
are kind-generic through `atomicPlan`).

### 2.6 The downstream customer — a non-pin, customer-visible cost

`~/projects/golean-logic` (pin `provenance/pins.json` `golean.rev = 20d3946d`) matches
exhaustively on `IntKind` twice: `packages/golean-iris/GoLeanIris/Logic/IntegerSemantics.lean:27-32`
(`Scalar.bits`, every constructor listed) and `Logic/Source.lean:33-36` (`IntType.ofKind?`,
`| .uint64 => none | .unbounded _ => none`). At its next re-pin both become non-exhaustive
(a compile error — fail closed, two one-line arms: `| .uintptr => 64` and `| .uintptr => none`,
or an `IntType.uintptr` member if the logic wants to reason at that kind). Not a pinned statement
of this repository; it belongs in the changelog row and the next offer's limits list.

## 3. The retirement of the refusal — exact edits

The guard is 1,817 lines in three files plus hooks; it goes in the same commit as the core change
(`tools/lowerdiag`'s calibration test compares the static judge with the wire, so the two sides
cannot be retired apart).

| what | edit |
|---|---|
| `tools/nativefrontend/uintptrid.go` (714) | delete |
| `tools/nativefrontend/uintptrid_test.go` (581; 37 refusing + 25 lowering shapes) | delete; replace with a ~40-line regression test that the six R1 probe shapes and the method-set shapes EXPORT (the frontend cannot evaluate; the gc answers are the corpus's) |
| `tools/nativefrontend/emit.go:1154-1162`, `:1835-1840`, `:2281-2291` | the three `checkUintptrIdentity` hooks and their comments removed |
| `tools/lowerdiag/uintptr.go` (522) | delete |
| `tools/lowerdiag/static.go:544-550` | the `uintptrIdentity` hook removed |
| `tools/lowerdiag/causes.tsv:97` (`uintptr-identity`) | row removed |
| `tools/lowerdiag/testdata/calib/uintptr_fr38.go` (26); `tools/lowerdiag/lowerdiag_test.go:775-782`, `:1144-1145` | fixture and the two test tables' entries removed |
| `Corpus/coverage/exec/interfaces/uintptr-identity/cases.tsv` | the header comment rewritten (no longer red by design); the six rows unchanged (`ok`, `-`) — they now PASS with gc's `false false 1 2 false false`; the six controls unchanged |
| `…/uintptr-identity/main.go` | header comment rewritten; subjects unchanged; BORN rows ported from `5f185fb3`'s `ints/uintptr-identity`: `method-param` (`M(uintptr)` is not `M(uint64)`: gc 8), `method-result` (gc false), `array-assert` (`[1]uintptr` is not `[1]uint64`), `wrap` (`^uintptr(0)+1 == 0`), and a new `assert-panic` (the non-comma-ok assertion's gc text `interface conversion: interface {} is uintptr, not uint64`, status panic) — the readout rows only under O2 |
| `baselines/native-full.tsv` | six FAIL/frontend-export → PASS; +5 born PASS under O1 (the four ported rows and `assert-panic`), +7 under O2; 3953 = 3714 PASS / 239 FAIL → 3958 = 3725 / 233 (O1), 3960 = 3727 / 233 (O2); header reason citing D6 and this note; `scripts/ci --diff` fresh, every row |
| `docs/BUGS.md` BUG-124 | heading «GUARDED by name» → «FIXED 2026-10-12 (the repair lane)»; `Status: fixed`; `Pinned-by: differential` (the «none» paragraph goes); **`Expect: FAIL` line deleted** in the same commit as the baseline flip (`scripts/check-bugs.sh` rule 5 fails a PASS row under `Expect: FAIL`); the Cases line keeps the six ids and gains the born rows; a FIX record paragraph |
| `docs/language-coverage-ledger.md:380` FR-38 | the frontier row closed («RETIRED 2026-10-12 — the repair»); §8 a movement entry with the figures |
| `docs/cli.md:255` | O1: the parenthesis; O2: «eleven», `uintptr` listed |
| `docs/release.md:81-82` | the stated limit removed |
| `docs/2026-10-12_release-readiness.md` item 26 | REPAIR half LANDED |
| `docs/changelog/20d3946d-WINDOW.md` | one consumer-facing row: the identity, the constructor, §2.6's re-pin note |
| docstrings/comments naming the collapse | `Machine.lean:2754-2756`, `Syntax.lean:423-424`, `NativeToIR.lean:1085-1086`, `:1107` (the refusal text), `CLI.lean:512-517`, `atomics.go:69-70`, `coverageharness/main.go:565-569` |
| `docs/2026-08-11_latitude-inventory.md` R1 (`:2228-2235`) and `docs/2026-08-21_w7-desugar-inventory.md:2740-2742` J-8 | amended per D4 (§5) |

The handoff's numbering note (`docs/2026-09-05_typed-consumer-sprint-handoff.md` decision 2 and
§«BUG numbering reconciliation»: «the `uintptr` item takes the next free number at landing») is
discharged: the number is BUG-124, allocated by the refuse half; the repair marks it fixed, no new
number. The staged «BUG-107» of the sprint stays a historical label.

## 4. Scope and cost, measured

**Core (`GoLean/`), ~20 lines in 5 files:** `Value.lean` +4 (constructor, `name`, `bitsAt`
`some p.intBits`, `signed false`); `Machine.lean:2758` +1 arm and the docstring; `NativeToIR.lean:398`
one token, `:1106` +1 alternative, two strings; `Syntax.lean:423` docstring; `Platform.lean` nothing
(W1). O2 adds `CLI.lean:532` +1 arm and the comment. Proofs: 0 expected edits (§2.1).
**Tests:** `Tests/GoCoreEval.lean` — O1: the `:3123` test stays (its comment `:3117-3118` is
reworded: the refusal is now the seam's, not the frontend's); O2: the three tests of `5f185fb3`.
**Frontend/tooling:** −1,817 lines of guard, −~50 lines of hooks/fixtures/table entries, +~40 lines
of export regression (§3). **Records:** the eleven record files of §3 (BUGS, the ledger, `cli.md`, `release.md`, the punch list, the changelog, the latitude inventory, w7, the baseline, `cases.tsv`, `main.go`) plus the seven docstring sites.

**Proof hours:** the honest estimate is 1–2 h of attention, dominated by waiting: `Value.lean` is
the root of `GoCore` (3 direct importers; 60 of the 66 modules under `GoLean/` depend on it
transitively — all but `Platform`, `FloatBits`, `EquationsAttr`, `StrictJson`, `StrictJsonParse`,
`DeclarationUnicode`; measured over the import graph), so the first build after the constructor
lands is a rebuild of the whole proof stack — the cold-class build (`docs/operational-lessons.md`: cold full builds need 64G+; run as
`capped -m 64G -- lake build`), an hour-class wait on this box. If the probe build (step 0) shows
either `cases` site NOT closing, the lane stops and reports before touching the tactic text — that
would falsify §2.1's «mechanical» and re-close the gate.

**Gate cost:** one cold-class `lake build` of every target, then `scripts/ci --diff` warm
(850–1034 s recorded, `docs/2026-10-12_gate-cull-plan.md`), under the build lock. No `--slow`,
no certificates, no evidence directory (D3, §5).

**Slice plan — one session if the build behaves, two commits either way:**
0. Probe: add the constructor and the three arms, `capped -m 64G -- lake build GoLean`; read the
   two `cases` sites' outcome. Stop and report if a tactic needs text.
1. Commit A (core + decoder + atomics twins + docstrings + the eval test wording): build green,
   the five atomics rows and `builtins/print/uints` still PASS (`scripts/ci`, the recorded-baseline
   diff: the six rows are expected to stay FAIL here — the guard still refuses them).
2. Commit B (retire the guard, port the born rows, re-pin the baseline with a fresh `--diff`,
   the records): `scripts/ci --diff` green; speedbump reds named (`check-bugs` will be the one to
   watch: `Expect: FAIL` and the baseline must flip together).
3. If O2 is ruled: commit C (both seams, `docs/cli.md`, the readout rows, the three eval tests).

**The pre-merge audit's focus:** (i) the two atomics twins admit `.uintptr` in lockstep (five
PASS rows are the witness); (ii) W1's arm reads `p.intBits`, with `Platform.lean:30`'s docstring
unchanged and go/types' `Sizeof` cited (`deps/go/src/go/types/sizes.go:151-179`, `:229`: `Int`,
`Uint`, `Uintptr` have no `basicSizes` entry and all fall to `WordSize` — gc never separates the
two widths); (iii) the guard, the static twin, the calibration fixture and the hooks go in ONE
commit; (iv) under O1 both observation seams still refuse by name (the `:3123` test and a
go-observation control on a `uintptr`-returning subject — a born red row is NOT wanted; the
existing seam tests suffice); (v) `check-bugs` rule 5 and the baseline flip in one commit;
(vi) the R1/J-8 amendments say exactly what moved (D4); (vii) the changelog row carries §2.6.

## 5. Decisions for the [USER] — each [AGENT]-recommended, PENDING

**D1 — the identity model: I1 a distinct `IntKind.uintptr` (recommended) vs I2 a `defined`-style
wrapper.** I1 is what the language says: `uintptr` is a basic integer kind (go/types
`types.Uintptr`, spec#Numeric_types), the declaration layer already has `Basic.uintptr`, the wire
spells it as an `int` name, and every identity site in §1.2(b) is fixed by `Ty.eqb` with no edit.
I2 (the decoder minting a synthetic `TypeDef` «uintptr» over `.int .uint64`) would invent a type
entry the wire does not carry (against the architecture rule that no semantic choice hides in the
decoder), mis-spell the panic text and the `dynamic` name unless special-cased, and break the
atomics twins (they key on `.int k`). **Recommend I1.** Within I1, the width arm: **W1
`| .uintptr => some p.intBits`** (recommended: the documented reading of `intBits`, go/types'
single `WordSize`, zero proof edits) vs W2 `some (8 * p.wordBytes)` (the old branch; spec-
faithful parametrization — «large enough to store the uninterpreted bits of a pointer» — but a
definition change to `Platform.PowTwoAligns` and a platform where `uintptr` and `int` can
diverge, which no gc target has). At the pin both are 64.

**D2 — what the observation spells: O1 keep both seams refusing `uintptr` (recommended for
THIS lane) vs O2 un-refuse (the old branch).** O1 keeps `golean-observation-v1`'s kind set at
ten and makes the repair a pure identity fix; the six wrong answers are the ones ruled on, and
they return `bool`/`int`. O2 is the right end state — the refusal's stated reason («the machine
could never emit it») is gone, and gc's `reflect.Kind()` says `uintptr` — but it is an additive
observation-format change the consumer sees (`docs/cli.md` §4), so it is named here rather than
folded in. **Recommend O1 now; O2 as commit C of the same lane if ruled, else its own small lane.**

**D3 — validation: the corpus rows and a fresh `scripts/ci --diff` alone (recommended)** vs
re-creating the old branch's apparatus (a 246-file evidence tree, `--slow` certificates, the
«full and slow» job, an independent-review directory). The gate cull ([USER]-ruled 2026-10-12,
D1–D9) retired that apparatus; the artifact doctrine says rebuild, never hoard. The fix
criterion stays BUG-124's: the six rows PASS with gc's values, `width-only` and the five atomics
rows still PASS, zero PASS→non-PASS flips. **Recommend the rows + `--diff`; no evidence directory.**

**D4 — amend the latitude record R1 and w7 J-8 (recommended: yes, in place for R1; a dated
supersession line for J-8).** What R1 says now (`docs/2026-08-11_latitude-inventory.md:2228-2235`,
the «Also entangled» clause): «`uintptr` (frontend maps to uint64; observations of it refused;
since 2026-10-12 its runtime type IDENTITY — boxing into an interface, assertion / type-switch
targets — is refused by name at the frontend too, `tools/nativefrontend/uintptrid.go`, BUG-124 /
ledger FR-38, pending the parked `typed-uintptr-identity` repair ([USER] 2026-10-12 D6: refuse
now, repair soon); the width pin here is untouched)». What it would say: «`uintptr` — a DISTINCT
integer kind since 2026-10-12 (`IntKind.uintptr`, BUG-124 fixed; [USER] 2026-10-12 D6: refuse now,
repair soon), whose width reads this pin (`IntKind.bitsAt`: `p.intBits`, as go/types sizes
`Int`/`Uint`/`Uintptr` by the one `WordSize`); the identity was never latitude — spec#Numeric_types
makes it a distinct type — only the width is; observations of it [O1: stay refused at both seams
by name / O2: carry the kind]». What J-8 says (`docs/2026-08-21_w7-desugar-inventory.md:2740-2742`):
«**`uintptr` is a gc-pin of latitude R1** — record it there rather than "fix" it». It was right
about the WIDTH and wrong about the IDENTITY (the collapse was never a pin of anything Go permits);
the dated inventory keeps its text and gains one line: «Superseded 2026-10-12 for identity (BUG-124,
`docs/2026-10-12_uintptr-repair-design.md`): the width remains R1's pin; the kind is distinct.»
The dated atomics design note (`docs/2026-09-03_atomics-w1-design.md:16`) is a record and is not
rewritten. The audit-B R13 condition («a third-lane review of the latitude override specifically»,
`docs/2026-09-07_landing-audit-B.md:605-613`) is met by the standing pre-merge adversarial audit
with §4's focus (ii) and (vi) named in the ask.

**D5 — the born rows (recommended: port four from `5f185fb3` + the `assert-panic` row, §3).**
The method-set shapes are the one identity site today's six probes do not exercise.

## 6. The gate

Under D1 = I1 + W1 and D2 = O1: no pinned statement text moves, no wire or observation schema
moves, the proof work is two `cases` sites closed by their existing combinators — **the gate is
open; the implementation is a plain lane** (slices 0–2 of §4), subject to the probe build
confirming §2.1 and to the [USER]'s rulings on D1–D5. Under W2 or O2 the gate is closed on the
axis named (§2.1, §2.4) and the lane returns here. This lane stops at this note.
