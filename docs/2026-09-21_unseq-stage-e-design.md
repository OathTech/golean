# Stage E — family migration of the evaluation-order model v2.1: the design record, per family (2026-09-21)

[AGENT] Lane `core/unseq-stage-e-0921` (worktree `.claude/worktrees/unseq-stage-e`), branch off main
`74d084ad` (rebased onto the train's records-only `14006270`). Design of record:
`docs/2026-09-16_evaluation-order-model-v2.md` (v2.1) §7 row E — «Family migration: by operand and
statement family: BUG-101/104, assignment targets, guards, receivers, allocations; legacy
`unseqProbe`/`probeK`/`unseqPanic` removed ONLY after all callers, tests and consumers moved;
whole-sweep boundary, no fixture-name dispatch; EXIT: per-family full gate + `--diff`, named set
changes, pins/ledgers updated». Rulings in force ([USER], `docs/2026-08-31_qrow-rulings.md`): width of
P = ALL mutable reads, STAGED (2026-09-19 «Agree, merge», relayed); N1 = SPLIT; N3 = REFUSE by name;
E2/E12 (b) → (a) on the pilot's rows (2026-09-20 «land it», relayed — extended here to every migrated
row, each named); the confluent caption covers expression-order picks (2026-09-21 «yes, I agree — go
ahead», relayed). Stage C's design (`docs/2026-09-19_unseq-stage-c-design.md`: the pilot grammar §1,
the wire §4, the decoder spec §5, the lowering §6) and Stage D's route α
(`docs/2026-09-20_unseq-stage-d-design.md`) are extended, not restated: this note records what EACH
FAMILY adds — the grammar widening, the decoder arm, the reference witnesses, the census before/after,
the rows born/flipped/moved with their sets, the latitude reclassifications posed for ratification, the
[AGENT] choices with their alternatives. Everything below is [AGENT] unless marked. The handoff is
`docs/2026-09-21_unseq-stage-e-handoff.md`; evidence `docs/evidence/2026-09-21_unseq-stage-e/`.

## 0. The families and their order

| family | what enters the grammar | closes | core change |
|---|---|---|---|
| **E1** package-level variables (LANDED, §E1) | reads `g` / `pkg.V` as READ occurrences (`deref(globaladdr)`); operand-free targets (`g = e`, `g op= e`, `g++`) | **BUG-113** (two rows FAIL → PASS) | none (decoder D8: the `deref` head) |
| E2 pointers, fields, maps | `*p`, `p.f`/`s.f`, `m[k]` reads; map-element target plans (`m[k] = e`, `m[k] op= e`) — one frozen plan shared by load and store | BUG-104's `map-compound-index-key-vs-call` | `unseqReadTarget`'s `.mapElem` arm (+ its `locSup` lemma); `unseqAtom` string constants |
| E3 receives, method calls | `<-ch` as an EVENT occurrence (E1-ordered); concrete-receiver method calls as invocations (receiver sub-evaluation = occurrences) | BUG-104's `compound-call-target-vs-recv`, `map-compound-index-key-vs-{recv,method}` | a statement-bodied occurrence kind (the receive) + its `Step` rules and coherence arms |
| E4 conversions, allocations | numeric/string/byte/rune conversions as ops; `&T{…}`, slice literals, `make` as allocation occurrences (payload reads are the occurrences; no E1 edges) | BUG-102's five designed reds | the same statement-bodied kind (allocation statements) |
| E5 multi-target forms, the residue | tuple/multi-value assignment, comma-ok forms, blank targets; the census residue migrated or stated | E3/E4 latitude entries (inter-target order) | — |
| E6 retire the legacy triple | when the census shows ZERO legacy `unseq-probe` emissions | — | delete `Stmt.unseqProbe`/`Cont.probeK`/`ChoiceSite.unseqPanic` with their arms |

The order is the brief's recommendation — the families that close open WRONG ANSWERS first (E1 closes
BUG-113, a spec-forbidden member the legacy hoister realizes; E2/E3 close BUG-104's observed-∉-modeled
rows; E4 retires BUG-102's designed reds); each family is ONE gated runtime commit with records between.
The whole-sweep boundary rule is unchanged (v2.1 §3.7; Stage C design §1): one sweep is EITHER one
`unseq` graph OR the legacy path, decided by `unseqClassify` alone — never by fixture name, never a
mixture (the mixture guard and decoder D14 stay).

## E1. Package-level variables as occurrences (landed 2026-09-21)

**The grammar widening** (`tools/nativefrontend/unseq.go`). A PACKAGE-LEVEL VARIABLE — unqualified `g`,
or source-package qualified `pkg.V` (W1.1's name resolution) — of an admitted type (int kinds, bool,
string, slices of them, `any`) is a mutable location. Its READ is a READ occurrence and counts toward
`nonEvents` (`unseqExpr`'s Ident and Selector arms). As an ASSIGNMENT / COMPOUND / IncDec TARGET
(`unseqVarTarget`, the former `unseqLocalTarget`; `unseqQualifiedTarget`) its identity has no operands —
a plan that checks nothing — so the store rides `then` exactly like an address-taken local's, and a
compound form's load is the same READ occurrence (`unseqReadWriteTarget`: `nonEvents++`). `g = f()`
alone stays legacy by the trigger (no non-event occurrence: every edge forced). A global of a type
outside the grammar refuses by name («package-level variable / target of a type outside the grammar
(T)»). WHETHER THE CELL IS SEEDED is the lowering's check, not the classifier's: the census runs before
`emitProgram` builds the globals table, and the census must not drift from the emitter; an unseeded or
FR-24-poisoned global refuses by name inside `emitIdent` (the same per-declaration quarantine as the
legacy path — `init/stdlib-initializer-dependent` refuses identically on both).

**The lowering** (`unseq_lower.go`). `value`'s Ident arm: a package variable's `emitIdent` wire is
`deref(globaladdr gid)` — the head of an `eval` READ occurrence (`read<n>`); the Selector arm does the
same through `emitQualifiedSelector`. Targets: `emitAssignTargetPhase1` already spells a global target as
`addr(globaladdr)` — `then: assign addr(globaladdr) = $u` — for both spellings; `readWrite`'s variable
arm serves `g op= e` / `g++` (the read occurrence + the op; the store in `then`). Canonical order is
unchanged (events first per frame, then the residual): the all-zero tape realizes calls first, the
global read late — gc's call-first realization on every E1 row.

**The decoder** (`GoLean/NativeToIR.lean`, D8): the `deref` head is admitted when its `ptr` is an atom
(a slot or admitted local — the E2 family's `*p`) or a `globaladdr`; any other pointer position is a
hidden read, refused by name (mutant `mut-deref-hidden`, the 20th). The `deref` keys are the standing
`["expr","ptr","type"]`; D9 types the head against its cell. No machine change: the head evaluates under
the frame like every `eval` head (`unseqRunEval`/`unseqValue`).

**The reference leads the lowering** (`docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py`,
regenerated `outcomes.txt`, RESULT PASS): E1a `v := mut() + g` (mut: g = 2) → {1, 2}; E1c `g += f()`
(f: g = 10, returns 1) → {2, 11} (the store lands in phase 2 through g's operand-free identity);
E1b = BUG-113's c01 with `left` a package-level variable — the SAME graph as R2b, the singleton
{`logical false 0`}, the legacy `logical true 0` asserted FORBIDDEN. Hand-built wires
`Tests/unseq-wire/{e1,e1c}.json` (build.py: the gid is an envelope fact read off the frontend's own
emission, like a lifted closure's name) and the frontend's OWN lowerings `native-{e1,e1c}.json` give
those sets EXACTLY over the wire (`Tests/UnseqWire.lean`: 65 ok, 20 mutants refused by name;
`scripts/check-unseq-wire` PASS; `scripts/check-wire-boundary` PASS, 11 + 11 controls — the global-read
positive control and the hidden-read refusal added).

**The census** (`docs/evidence/2026-09-21_unseq-stage-e/census-e1.txt`): main `74d084ad`'s frontend vs
the E1 frontend over 1356 corpus packages + the raft twin — 107 943 sweeps; admitted 136 → 146 (+10, in
4 packages; 0 lost); the twin 10 203 sweeps, 0 admitted before and after (pin byte-identical). The ten:
`evalorder/legacy-logical-vs-call` ×3 (the BUG-113 rows and their control), `spec-examples-decl/
select-forms` ×5 (`sLog += … + itoa(…)` compound globals; two `return sLog + … + itoa(fCalls)`),
`panic-recover/repanic-collapse` `indexTwoFaults` (`sink = idx(s, 5)`, a global target beside a call
whose argument slice is address-taken), `init/stdlib-initializer-dependent`'s `main`
(`println(unrelated(), maxYear)`). Of the BEFORE census's 169 «package-level variable» refusals only
these ten enter: the rest meet another construct outside the grammar next (the census prints the
FIRST), and the still-legacy package-level reasons are all TYPE refusals (`*int`, `[3]int`, `chan int`,
struct types — E2/E4's).

**Rows** (measured by `scripts/diff-one` on all 13 affected rows, `diff-one-e1.txt`; gc's draws
`gc-draws-e1.txt`, 20/20 per row under GOMAXPROCS 1 and 8, default and `-gcflags=all='-N -l'`):

| row | before → after | set (output · result) | gc |
|---|---|---|---|
| `evalorder/legacy-logical-vs-call/or-vs-call` (BUG-113) | FAIL/differential → PASS strict, wide=0 | {`logical false 0`} — the R2b graph, every edge forced | = |
| `evalorder/legacy-logical-vs-call/and-vs-call` (BUG-113) | FAIL/differential → PASS strict, wide=0 | {`logical false 0`} | = |
| `evalorder/legacy-logical-vs-call/call-first-control` | PASS strict (unchanged), wide=1 | the read of `left` vs `change()` (which does not write `left`) — one observation | = |
| `evalorder/unseq-globals/read-vs-call` | born PASS/membership | {1, 2} (E1a) | 2 |
| `evalorder/unseq-globals/compound-vs-call` | born PASS/membership | {2, 11} (E1c) | 11 |
| `evalorder/unseq-globals/read-vs-unrelated-call` | born PASS strict, wide=1 | `wit 1` · 2 (both orders agree) | = |
| `evalorder/unseq-globals/plain-target-call` | born PASS strict, wide=0 | `wit 1` · 2 (legacy by the trigger — the control) | = |
| `spec-examples-decl/select-forms/{ready,default,block-forever}` | PASS strict (unchanged), wide=4 / 2 / 0 | the global reads beside `itoa` — no sibling call writes `sLog`/`fCalls` | = |
| `panic-recover/repanic-collapse/index-two-faults` | PASS/membership (unchanged), enumerated=2 | the `repanicCollapse` set; the new `unseqNext` pick (the address-taken `s`'s header vs `idx`) changes no observation | = |
| `init/stdlib-initializer-dependent` | FAIL/frontend-export (unchanged, pre-existing) | the H-11 poison of `maxDatetime`'s initializer refuses the whole export on both frontends | — |

NO lane move, NO widened pin, NO PASS → non-PASS. Baseline 3705 = 3459 / 246 → 3709 = 3465 / 244
(+4 born, +2 flips); BUG-113 `Status: fixed` (`check-bugs.sh` ok). **The full gate** (`scripts/capped
scripts/ci --slow` at the E1 tree under the box-wide lock, 02:10–02:28Z): EXIT=1 in 1083 s, K=80; 3709 rows
3464 PASS / 245 FAIL in the run = the pin with the one 5a-class row red; RESULT FAIL on exactly the two
5a-class items (`certificate provenance` STALE for `GoLean/NativeToIR.lean`; the drift line
`imported-goose/channel/google-search` PASS→FAIL/membership); every other step ok — the evidence README's
gate paragraph and `ci-slow-e1.tail.txt`. The 56 label-shape facts
(`Tests/GoCoreEval.lean`) are untouched (no machine change). `scripts/check-mem-callsites` untouched.

**Latitude** (`docs/2026-08-11_latitude-inventory.md`): E2's and E12's VALUE axis is (a) ENVELOPED on
TWO more rows — `evalorder/unseq-globals/{read-vs-call,compound-vs-call}` (a package-level read beside a
call that writes it: both values are members, gc's call-first value among them) — posed for
ratification at the merge ask with the pilot's precedent; the entries stay (b) PINNED for the rest of
their families. BUG-113's fix is NOT a latitude reclassification: the `||`-before-a-later-call order
is spec-FORCED (spec#Order_of_evaluation), the graph realizes it, the legacy member was forbidden.

**[AGENT] choices (alternatives named).** (i) The classifier stays SYNTACTIC on globals (seeded-cell and
poison checks in the lowering) — the alternative, consulting `globalVars` in the classifier, would make
the census (run before `emitProgram`) disagree with the emitter. (ii) A global target's store rides
`then`, not a `target`+`store` pair — the alternative would mint a target occurrence with no operands
(a plan that checks nothing and freezes nothing), one more pick position per loop iteration for no
semantic content (the Stage C private-compound precedent, design §7). (iii) The decoder's `deref` arm
admits an atom pointer NOW (E2's `*p` spelling) beside `globaladdr` — one arm, one mutant; the
alternative (a `globaladdr`-only arm, widened at E2) would restate the arm and its refusal text one
family later. (iv) BUG-113 is fixed by MIGRATION, not by the interim E1-at-completion anchoring in the
legacy hoister the entry's fix plan also named: a second implementation of the ordering the graph
already realizes, for sweeps the later families migrate anyway. (v) No corpus row for the qualified
`pkg.V` spelling: it needs a multi-package program; the classifier/lowering arms are exercised by the
unit test's shape only through the unqualified path and by the census (0 qualified sweeps admitted in
the corpus or the twin) — recorded as a gap, not claimed covered.
