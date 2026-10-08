# R3 — the capacity of `[]byte(s)` / `[]rune(s)`: design note (b6; a named design gate — HARD STOP)

[AGENT] design worker, lane `design/b6-conv-cap-1007` (off `main` @ `0642b3e3`), 2026-10-07. Authority: [USER] Mike
2026-10-07, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «1-4 approved as proposed», item 3: the
gc-verified project's (b6) cap widening as a DESIGN NOTE FIRST, settling whether the append-spill choice site can be
reused; under the standing rule of the same day, «the semantic widenings should only be allowed if they match real Go»
(`docs/2026-08-31_qrow-rulings.md`: a widening admits only what the spec permits AND the pinned gc realizes,
differentially witnessed; never a wider machine; no pick that lets one execution observe inconsistent answers).
NO implementation here; every decision below is [AGENT], PENDING [USER]. Evidence:
`docs/evidence/2026-10-07_conv-cap-design/` (140-row measured envelope, probes, gc `-m` lines, wire dumps).

## 1. What Go says, and what gc does at the pin (go1.26.5)

Spec §Conversions to and from a string type (both arms, verbatim): «The capacity of the resulting slice is
implementation-specific and may be larger than the slice length.» Floor: cap ≥ len. gc realizes FOUR regimes, decided
by the typechecker, escape analysis and inlining — none of them visible as a semantic property of the program:

| Operand / regime | bytes `[]byte(s)` | runes `[]rune(s)` | where (gc) |
|---|---|---|---|
| literal (or folded constant) operand, any regime | **n** | **n** | `walk/convert.go:296` (`[n]byte`, stack or `new`); `typecheck/expr.go:380` `stringtoruneslit` (a `[]rune{…}` literal) |
| non-literal, result never mutated, non-escaping | **n** (zero-copy: the slice ALIASES the string — unobservable through writes; element-address identity is a separate, unmodelled axis — BUG-121) | — | `escape/escape.go:365` `OSTR2BYTESTMP`, gated on `base.Debug.ZeroCopy = 1` (the default, `base/flag.go:190`); no rune twin |
| non-literal, mutated, non-escaping, n ≤ 32 | **32** (`tmpBuf`) | **32** (`[32]rune` buffer; for n ≤ 32 whether mutated or not) | `walk/convert.go:330–335, 354–359`; `runtime/string.go` `stringtoslicebyte`/`stringtoslicerune` |
| non-literal, escaping, or non-escaping with n > 32 | **R(n)** | **R(4n)/4** | `rawbyteslice`/`rawruneslice` → `roundupsize(size, noscan)` (`runtime/msize.go`), the size-class table `internal/runtime/gc/sizeclasses.go` (68 classes ≤ 32768 B) then 8 KiB page rounding |

`R` = gc's `roundupsize` for a noscan allocation. Measured (evidence `envelope.tsv`, 140 rows, 0 mismatches, every
member ≥ len): bytes non-literal n=5 → {5, 8, 32}; n=33 → {33, 48}; n=100 → {100, 112}; n=32761 → {32761, 40960};
runes non-literal n=5 → {6, 32}; n=33 → {36}; n=100 → {104}; literals → {n} for both. The ENVELOPE, per kind, operand
class and length:

- `bytes, literal, n` = `{n}`; `runes, literal, n` = `{n}`.
- `bytes, non-literal, n` = `{n} ∪ {R(n)} ∪ {32 | n ≤ 32}` — 1 to 3 members.
- `runes, non-literal, n` = `{R(4n)/4} ∪ {32 | n ≤ 32}` — 1 or 2 members; **len is NOT a member** unless 4n is a
  size class (for n ≤ 32: n ∈ {0, 2, 4, 6, 8, 12, 16, 20, 24, 28, 32} (and every n > 32 with 4n a size class)).

Corrections to the inventory's R3 record (`docs/2026-08-11_latitude-inventory.md` ~2260–2285) and the arms' comments
(`Machine.lean` ~421–435, ~688–714): (i) «cap = len when the backing does not escape» is true only on the never-mutated
zero-copy regime — a mutated non-escaping `[]byte(s)` gives 32 or R(n); (ii) «`cap([]rune("héllo")) = 32`» is the
VARIABLE-operand value; the literal gives 5 (`probe_literal.go`: `rl` = 5, `rv` = 32); (iii) the green row
`strings/byte-conversion-cap` (`s := "hello"; []byte(s)`, read only) pins the zero-copy member, not a «non-escaping
point». The machine's singleton cap = len is a gc member for every byte conversion (zero-copy) and OUTSIDE gc for
almost every non-literal rune conversion — today's rune arm is an observed-∉-modeled wrong answer on `cap`, and on
the aliasing it implies (`append` on a cap-32 slice is in place; on a cap-5 one it spills).

Escape/mutation status is an OPTIMIZER decision, not a program property — for ESCAPE (inlining moves it); a WRITE
(appends count as writes) is a program property: a non-literal `[]byte(s)` that is written to never gets cap n under
gc when n is not a size class, and the per-(kind, literal, n) union admits n there anyway — a known per-program
over-admission, like R2's (train r74, the audit's item 2): `probe_inline.go` has ONE source line
(`return []byte(s)` in an inlinable helper) realizing 5, 32 (default build) and 8 (`-gcflags=-l`); gc's own `-m`
output names the regimes. So the envelope is the UNION over the regimes — latitude on the tape, exactly as the inventory
frames it. The literal/non-literal split IS a program property: the native frontend emits a literal operand as the
wire node `{"expr":"string","bytes":…}` (`Expr.stringLit`) and folds constants and constant concatenation into it
(`probe-outputs.txt`: `lit`, `cst`, `cat`, `nest` literal; `vr`, `rv` `ident`) — the same classification gc's
typechecker makes, so the machine can see it WITHOUT a wire change.

## 2. Where the pick must be drawn — the finding that reframes the reuse question

The conversions are STRICT EXPRESSION heads (`StrictOp.bytesFromString`/`runesFromString`, `strictPlan`), applied by
the pure `applyStrictOp` (`Machine.lean:358`, no stream) at `stepFn`'s `.retV v (.strictK op done [] …)` arm
(`StepFn.lean:730`) and the relation's `Step.strictApply` (`Machine.lean:6361`, label `⟨tr, [], []⟩`). The length is
known only there. NO existing consult position fits (the stream-holding arms are frame entry, the wide-statement apply,
map iteration, select, sync, the `unseq` pick, the abort line). Therefore ANY widening — whichever site tag it carries
— adds a consult at a previously consult-free arm, and the three pinned equations stating that arm pops nothing
(`BridgeSet.lean` rows 335–337: `retV_strictK_apply`, `_panic`, `_error`; the logic team uses `retV_strictK_apply`
13× across seven `golean-iris` modules — `Logic/SliceRules.lean` 5, `Rules.lean` 2, `Logic/StrictRules.lean` 2, one
each in `AggregateRules`, `MapRules`, `StructRules`, `SourceKernel`) change statement. Reusing `appendSpill` buys NO additivity: the breaking
element is the position, not the constructor — and the `ChoiceSite` constructor itself is additive downstream
(`~/projects/golean-logic`: no `cases`/`match` on `ChoiceSite`; it names only `Choices.consumeAtE_appendSpill` and
`appendSpillWidth`, keyed on the append bound). Moving the conversions to the wide-statement mold instead
(`Stmt`/`StmtOp` like `randIntn`) would change the wire (v3 → v4), delete two `Expr` heads and re-lower every fixture —
strictly more breaking. The literal case, by contrast, is a bound-1 consult (one member) and pops nothing.

## 3. The options

**(A) Reuse `ChoiceSite.appendSpill`.** Its pick is an OFFSET into the contiguous interval `[newLen, appendSpillUpper]`
(`applyStmtOp.plan`, `appendSpillWidth`; `canonicalSlot0`: «width ≥ 2 always — `one_lt_appendSpillWidth`»; the trace
census `spillFacts` checks a bijection onto the interval AT AN `appendSlice` APPLY). Reusing its SEMANTICS would admit
`[n, upper]` — cap 6, 7 for a 5-byte conversion, which gc never realizes: forbidden by the standing rule. Reusing only
the TAG with the conversion's own member list makes a `PickRecord ⟨.appendSpill, b, p⟩` ambiguous between two sources
of latitude (the logic team's §5 asks to «couple choices by meaning» — site/bound/value must identify the draw), breaks
`spillFacts`' invariants and the per-site census accounting (`scripts/choice-trace-summarize`), and falsifies the tag's
documented width-≥-2 property. No cost saved (§2). **Rejected.**

**(B) A new `ChoiceSite.convCap` (RECOMMENDED).** Additive constructor; the member list as the bound; the pick drawn
at the strict-apply arm through a stream-holding funnel (the `enterFramePick` idiom):

- `Ops.lean`: `gcRoundupSize : Nat → Nat` — gc's `roundupsize` (noscan) over the pinned tables (a PLATFORM datum,
  version-tracked by the membership rows, like R2's formula center); `convCapMembers (kind) (literal : Bool) (n) :
  List Nat` in SLOT ORDER: literal → `[n]`; bytes → `[n] ++ [R n | R n ≠ n] ++ [32 | n ≤ 32 ∧ 32 ∉ {n, R n}]`;
  runes → `[R(4n)/4] ++ [32 | n ≤ 32 ∧ R(4n)/4 ≠ 32]`. Lemmas: non-empty; every member ≥ n (the spec floor);
  bytes' head is n (default-tape preservation); the table facts by `decide` over the finite tables (`#eval` first —
  the memory note — never `native_decide`).
- `Syntax.lean`: `StrictOp.bytesFromString (literal : Bool)`, `StrictOp.runesFromString (literal : Bool)`;
  `strictPlan` sets the bit from the operand being `Expr.stringLit`. `Expr`, the wire (`golean-native-v3`) and the
  decoder UNCHANGED; no pinned statement enumerates `StrictOp` or names these heads; the logic repo never does.
- `Machine.lean`: `applyStrictOpPick (s) (leafOf) (op) (vs) (ch) : Except Stop ((GoValue × Store × AccessTrace) ×
  Choices × List PickRecord)` — conversion heads with a string operand: `consumeAtE .convCap members.length ch`, then
  the fresh backing of `members[pick]` cells (the padded `buildAppendBackingValue` shape, zeroed tail — gc's `memclr`
  and the zeroed buffers agree; zero-copy's aliasing is unobservable through writes; element-address identity is a separate, unmodelled axis — BUG-121 (train r74, the audit's item 1: gc takes zero-copy only when nothing
  writes); every other head: `(applyStrictOp …, ch, [])`. `applyStrictOp`'s two conversion arms become the `.internal`
  refusal «dispatches through applyStrictOpPick» (the `applyStmtOpCore`/`appendSlice` precedent) — one definition of
  the conversion, not two. `strictConsult? op vs : Option (ChoiceSite × Nat)`; `seqConsumption`'s `.strict` arm
  (today `none`) uses it; `Step.strictApply` restated over the funnel with `ch ch' ps` (the entry-rule idiom), label
  `⟨tr, ps, []⟩`; `evalStrictNullary` untouched (no nullary conversion).
- Coherence (`MachineSound`, `PrefixFacts`, `MultiStreams`, `EnumDedup*`): `stepFn_sound`/`step_complete` on the
  strict-apply arm; `stepFn_picks_none/_some` and `stepFn_consumption_some` hold with the new arm (statements unchanged,
  rows 60–62); a `consumesConvCap` flag through the oblivious checkers; the certified dedup engine REFUSES the site
  (fail closed, the intn D8 precedent — the bound is a value-dependent member count), the default enumerator carries
  the rows; `ChoiceTrace.lean` `convFacts` (width = member count, members ≥ n, bytes slot 0 = n); the census summary's
  non-scheduling family gains the tag.
- `canonicalSlot0 .convCap`: «the FIRST member of `convCapMembers`: bytes slot 0 = n, gc's zero-copy member and the
  pre-widening singleton, so the empty/default tape reproduces every byte-conversion observation on `main`; runes
  slot 0 = the size-class member R(4n)/4 (gc's deterministic point for n > 32, its escaping point below); the later
  slots in list order (the size-class member, then the 32-element conversion buffer); a one-member list is a bound-1
  consult and pops nothing — every literal conversion, and every length whose members coincide».

**(C) One generic capacity site for append and conversions (renaming `appendSpill`).** Breaks the logic team's
`Choices.consumeAtE_appendSpill`/`appendSpillWidth` uses for no fidelity gain; the two latitudes have different member
structures (an interval vs a ≤3-member list). **Rejected.** Posed, not taken, out of scope: R2's append interval is
itself wider than gc's realized set under the standing rule; `gcRoundupSize` would let a later lane re-derive it.

## 4. Decisions (all [AGENT], PENDING [USER] — the gate)

- **D1** Option B: `ChoiceSite.convCap`, bound = `(convCapMembers kind literal n).length`, slot i = the i-th member.
  A DATA pick over a value, not a scheduling pick; drawn once per conversion value (the cap lives in the header), so no
  execution can observe inconsistent answers; two conversions of one string may draw differently, as gc's regimes may.
- **D2** The envelope is EXACTLY §1's measured member sets — nothing in between (the standing rule). `gcRoundupSize`
  enters the semantic core as pinned gc data; a toolchain that moves the table or disables zero-copy (`-d=zerocopy=0`
  deletes the `n` member on 27 of the measured non-literal byte rows) turns the membership rows red — a deliberate
  re-pin, never a float.
- **D3** The literal bit lives in the `StrictOp` head, derived by `strictPlan` from `Expr.stringLit`; a non-literal
  operand of ANY other shape takes the union. (A literal under a named-type conversion is folded by the frontend like
  `cst`; the implementation lane adds a control row.)
- **D4** Default tape: bytes slot 0 = n — `strings/byte-conversion-cap` and every row on `main` keep their observations;
  no row flips (the four other corpus files with `cap(` beside a `[]byte(` observe reslices, `make`, arrays). Runes slot
  0 = R(4n)/4 — NO corpus row observes a converted rune slice's cap (the inventory's deliberate non-add), so no baseline
  row moves; `cap([]rune(s))` under the default tape changes from n to gc's deterministic point: break-incorrect-behaviour,
  recorded in the inventory, no `BUGS.md` Cases line (no PASS→non-PASS flip). The whole-corpus choice trace is NOT
  byte-identical to `main`: the 31 non-literal `[]byte(` and 11 `[]rune(` sites in `Corpus/` (26 files; 4 in
  `raftsubject/`) gain a consult wherever their member count is ≥ 2, so positional adversarial streams shift — the
  G-U-style certificate: the default stream's observations identical, the shifted streams' observations named.
- **D5** Membership rows born PASS: bytes var/{nomut, mut, esc} at n ∈ {0, 5, 33, 100}, concat/esc at 5, the literal
  controls (bytes and runes), runes var/{nomut, esc} at n ∈ {5, 33, 100} (6/32, 36, 104), the inlined-helper shape
  (one line, caps 5 and 32 in ONE run), and the ALIASING witness (`append` on a converted slice, then a write, observed
  through the original — in place at 32, a spill at n). Each member of §1 gets a gc witness: the rule's «differentially
  witnessed». R3's inventory row → (a) ENVELOPED with the corrections of §1; `appendSpillUpper`'s docstring cites
  `gcRoundupSize`.
- **D6** BridgeSet: rows 335–337 RE-PINNED with the hypothesis `op.convKind? = none` (the three strict-apply equations
  hold verbatim for every non-conversion head — the logic team's 13 uses gain one `rfl`/`simp [StrictOp.convKind?]`
  argument; a mechanical migration, one changelog line); rows ADDED: the conversion apply EQUATION at a popping bound and
  its no-pop instance, the derived step rule «every member i is realized by the singleton tape `[i]` with picks
  `PickRecord.ofPick .convCap b i`» (the intn D7 shape), the pick-lifted plan the coverage proofs consume; all three plus
  `convCapMembers`' lemmas in the core audit's required list. Rows 331–334 (expression entry/shift) BYTE-IDENTICAL.
- **D7** Dedup engine refuses the site; default enumerator carries it (intn D8).
- **D8** Timing — a [USER] call: the window's offer `20d3946d` is FROZEN (`logic-offer/2026-10-03`) and the logic team
  is porting to it; D6's re-pinned rows make b6 a SECOND-batch item under ruling 1 («one window, one re-pin»). Posed:
  build now behind the offer, ship with the next batched offer (default), or hold until the port completes.

## 5. Cost and acceptance

Cost: ~2 sessions — one build (the intn landing was 20 files/+744 lines on the wide-statement mold; this adds a NEW
consult position and the table lemmas), one for proofs/records; Opus build, Fable if the strict-apply coherence re-proof
resists. Logic-side impact: 1 additive `ChoiceSite` constructor; 2 `StrictOp` constructors gain a `Bool` (unpinned,
unused downstream); 3 equations gain a hypothesis (13 downstream uses); no wire, `Expr`, `Stmt`, `Frame` or
decoder-signature change. Acceptance: `ci --diff` green, no existing row moved, the D5 rows born PASS; `ci --slow` red
only on the 5a pair; the choice trace vs `main` identical on the default stream and the shifted adversarial streams
listed with their deltas; core audit green; elaboration inside G-C3's 1.5× rule (`decide` over the tables `#eval`-checked first).

## 6. Ratification (2026-10-07)

[USER] Mike, 2026-10-07, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «yeah agree, build now».
D1–D8 RATIFIED as recommended: option (B), a new `ChoiceSite.convCap` (D1); the envelope EXACTLY §1's measured member
sets, `gcRoundupSize` as pinned gc data (D2); the literal bit on the `StrictOp` head from `Expr.stringLit` (D3); the
default tape bytes slot 0 = n, runes slot 0 = R(4n)/4 (D4); the membership rows of D5 born red-first; BridgeSet rows
335–337 re-pinned with the one hypothesis `op.convKind? = none`, the new rows in the intn D7 shape (D6); the dedup
engine refuses the site (D7); D8 = BUILD NOW behind the frozen offer `20d3946d`, shipped to the logic side with the
next re-pin batch. Standing rule restated at the ratification ([USER] 2026-10-07): a widening admits only what the
spec permits AND gc go1.26.5 realizes. The build is lane `lane/conv-cap-1007` (this note lands with it); any deviation
the code forces from D1–D8 is a named design gate — STOP and report, never self-adjudicate.

## 7. The build's design-gate finding and its ruling (2026-10-07)

The build (lane `lane/conv-cap-1007`) found D4's «no row flips» CONTRADICTED by the full differential at its tip
`0fdcbd29`: 20 pre-existing rows PASS→FAIL — none an observation change (the default-tape observation of every
pre-existing row is identical; `docs/evidence/2026-10-07_conv-cap/choice-trace-compare.txt`), all consequences of the
new consult position on rows D4's SOURCE count missed: the source-through stdlib code they execute —
`strings.TrimSpace`'s `for lo, c := range []byte(s)` (strings.go:1093, gc's zero-copy range TEMP, capacity
unobservable) and `bytes.NewBufferString` — draws a bound-3 `convCap` on every call. 13 strict `stdlib-source/*`
rows failed the strict lane's depth guard (streams exhausted), 3 membership rows refuted `width=2` at the new bound,
1 exceeded its `work` budget; `imported-goose/channel/google-search` is the standing 5a pair (fresh certification:
unchanged set). STOPPED at the gate as the brief requires; the evidence README poses options (i) row metadata only,
(ii) a bound-1 consult where the capacity is unobservable (the range-temp shape — a frontend/decoder mark D3 excluded,
or a machine-side recognition of the range desugar), (iii) both.

**RULED** [USER] Mike 2026-10-07, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Agree» — to the
coordinator's recommendation: option (i), semantics exactly as ratified, row metadata only (depth for the 13 strict
rows, `width=3` ×3, `work` ×1, then a re-pin with a written reason), CONDITIONAL on measured gate cost: if the full
`ci --slow` wall time grows by more than ~10% vs `main`'s latest close (r71: 1301 s; r72's time if available), STOP
and report instead — option (ii) then becomes a new design. Applied: `option-i-row-metadata.tsv` (every value the
smallest that passes: depth = the default-stream wide count, on the first try for all 13; width 2 → 3; work 400000
over 354088 measured steps); the timing measurement is `timing.tsv` in the same evidence directory.
