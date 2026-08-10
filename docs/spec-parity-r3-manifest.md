# R3 manifest — GoSpec instances over the imported goose corpus

Standing record (spec-parity arc, charter D3): per-program disposition
of R3 (kernel-checked `GoSpecC` + first-order readout twin) over the
imported sequential-oracle class. Started at slice 3
(`docs/2026-08-10_wp-walk-driver.md`); rewritten at the S3 audit fix
round (2026-08-10) — the first version asserted "37 proved upstream"
and marked three upstream-ABORTED oracles "proved upstream"; this
version records the measured truth. Updated whenever a row moves.
NOTHING here is designated unless the arc-end curation (user-owned)
says so.

**What is gate-checked, precisely** (S3 audit correction — the first
header blurred two properties): every theorem listed here is covered
by the in-build Audit AXIOM SWEEP (exhaustive over all `GoLean*`
modules — `propext, Classical.choice, Quot.sound`, no `native_decide`,
no `sorry`), and the slice-3 laws + their discharge witnesses are
referenced in `proofs/Audit.lean`'s witness registry (deleting a
witness breaks the build). The statements' Surface/interpreter
VOCABULARY (the deletion test) is TRUE but checked by NO standing
gate for undesignated theorems — the statement-TCB closure walk runs
on the designated list only. It was hand-verified at the S3 audit by
a replica of the Audit closure walk (all 12 R3 theorems: zero
Iris/relation constants, closure sizes matching the designated
`goldenSpecC`/`goldenReturnsTwoC` controls) and becomes mechanically
gated if/when a row is designated. Recorded limitation, not a gate.

**The upstream denominator, measured** (deps/perennial @ 43d4efa,
`new/proof/.../semantics_proof/`; commands:
`grep -h 'Qed\.' *.v | wc -l` = 29,
`grep -rn 'test_fun_ok semantics\.' *.v | wc -l` = 36,
`grep -h 'Abort\.' *.v | wc -l` = 7, `grep -n Admitted *.v` =
structs.v:28): **36 `test_fun_ok` lemma STATEMENTS, of which 28 are
proved (`Qed`), 7 `Abort`, 1 `Admitted`.** (The suite's 29th `Qed`,
`wp_shouldPanic`, is not a `test_fun_ok` oracle. The "37 proved"
figure earlier arc docs carried counted lemma statements — including
the Aborts and the Admitted — and is corrected at its origin,
`docs/2026-08-07_goose-comparative-scoping.md` B.1, and at every
tracked restatement, same round.)

Dispositions:
- **proved** — both D1 forms kernel-checked (`…SpecC` at full
  `InitialSplit` strength via the conservation transfer, `…ReadoutC` on
  the pool carrier), stated over the staleness-guarded pinned lowering.
- **side-goals-remaining** — a walk exists but stops at a recorded
  obligation.
- **out-of-class** — the program needs a law/machinery that does not
  exist yet (the gap named).
- **not-attempted** — no walk written this slice (the blocker/cost
  named).
- **no-pinned-lowering** — R1-green but its lowering term was never
  pinned into `proofs/` (an import-tooling step, not a proof gap).

## Feature class 1: sequential boolean oracles (the `test_fun_ok` class)

The class the slice-3 exemplar fixed: `test<Name>() bool` verbatim
bodies under the generated `golean<TestName>` wrapper
(`Specs/GooseParityKit.lean`), TotalPins seed, verdict `1`. The
"upstream @ 43d4efa" column is nil.v's per-lemma proof status,
measured (`grep -n 'Qed\.\|Abort\.' nil.v`).

| program (imported-goose) | upstream @ 43d4efa | our disposition | where / why |
|---|---|---|---|
| semantics/nil `testCompareNilToNil` | **Qed** (nil.v:31) | **proved** (THE EXEMPLAR — a genuine parity row) | `Specs/GooseParityNilWP.lean` — `compareNilToNilSpecC` + `compareNilToNilReadoutC` (designation CANDIDATES) |
| semantics/nil `testCompareSliceToNil` | **Abort** (nil.v:20; their TODO: "need a lemma showing allocations are non-nil") | **proved** — an oracle upstream attempted and abandoned; we discharge it | same file, `compareSliceToNil*` |
| semantics/nil `testComparePointerToNil` | **Abort** (nil.v:27; TODO: "points-tos are non-null") | **proved** — ditto | same file, `comparePointerToNil*` |
| semantics/nil `testComparePointerWrappedToNil` | **Abort** (nil.v:38; TODO: "array points-to is non null") | **proved** — ditto | same file, `comparePointerWrappedToNil*` |
| semantics/nil `testComparePointerWrappedDefaultToNil` | **Qed** (nil.v:46) | **proved** (a genuine parity row) | same file, `comparePointerWrappedDefaultToNil*` |
| semantics/nil `testInterfaceNilWithType` | **Qed** (nil.v:50) | **out-of-class** — an oracle THEY prove and we currently cannot | verdict uses short-circuit `&&` (`Expr.and`): NO WP law exists for the short-circuit forms (they have their own machine rules, not `strictPlan`). The `Expr.and`/`Expr.or` law family is recorded future law work. |
| semantics/block `testExplicitBlockStmt` | no `test_fun_ok` statement (block.go has no lemma in semantics_proof/) | **proved** (same-class coverage, not a parity row) | `Specs/GooseParityBlockWP.lean`, `explicitBlock*` |
| semantics/defer (2 oracles) | no `test_fun_ok` statements | **not-attempted** | R2-pinned; bodies use `deferCall` + `funcVal` closures — the defer drain laws exist (`Laws/Unwind`, cap1 family) but the walk composition is a different frame discipline than the kit wrapper; sized as its own movement. |
| semantics — the R1-green remainder (comparisons, precedence, loops, switch, vars, operations, int-conversions, conversions, multiple-return, new, allocator, builtin, first-class-function, function-ordering, slices, maps, interfaces, structs' 8 green rows, …) | 26 of their 36 `test_fun_ok` statements (incl. 21 of the 28 Qeds) have R1-PASS rows here (delta-review recount — the first rewrite said "30 … incl. 25 Qeds", wrongly counting the 4 frontend-blocked rows below as R1-green) | **no-pinned-lowering** | R1-green rows exist; their lowering terms were never pinned into `proofs/` (the R2 buildout pinned 6 units). Pinning is mechanical (the import pipeline's term generator + ci 3a2 guard — label corrected at the S5 audit) and is the scaling lever for the next R3 movement. |
| semantics/structs `testStructUpdates`; semantics/type-equality `testPrimitiveTypesEqual`, `testDefinedStrTypesEqual`, `testListTypesEqual` | **Qed** ×4 (structs.v:11; type_equality.v:11,15,19) | **out-of-class at R1** — 4 upstream-proved oracles we cannot even RUN through the differential | all four rows are `FAIL frontend-export` in the tracked baseline (the recorded call-in-short-circuit-operand quarantine — the buildout log's class): `type-equality` is one of the all-fail-5 units (0/3 green), `structs` is mixed (8/9). NOT a pinning item — a frontend capability gap, strictly earlier than the `&&` R3 law gap. |

## Feature class 2: authored checksum wrappers (unittest/storage lanes)

NOT the exemplar's class: the subject is an authored int-checksum
wrapper (no bool inner oracle), so the kit's wrapper walk does not
apply; each needs a per-unit driver walk. Upstream has no `test_fun_ok`
analogue for these (translation-golden only), so they are coverage
rows, not parity rows.

| program | disposition | why |
|---|---|---|
| unittest/const | not-attempted | R2-pinned; large pure-arithmetic walk (checksum 2139) — the int applies auto-walk (`go_walk_side` computes pure int ops), but the wrapper shape is custom; sized as mechanical-but-long. |
| unittest/rune | not-attempted | R2-pinned; small (converts + add) but custom wrapper shape. |
| storage/mapliteral | not-attempted | R2-pinned; needs `makeMap` (law exists) + `mapAssign` apply walks — the map-entry store discharge is the new content. |

## Feature class 3: the curated channel exemplars (slice 4)

The charter's flagship comparisons (item 4): the select-tricky trio,
muxer, dsp. Subjects are the units' `golean*` harness wrappers (the
upstream bodies sit verbatim above the marker; the wrappers are
GoLean-authored harness code), over the staleness-guarded pinned
lowerings (`Specs/ImportedGoose{SelectTricky,Muxer,Actris}.lean`, ci
step 3a2 since this slice — the label "1c5" this line first carried
was stale for the whole arc: the step was renumbered at the branch
base 2927085f; corrected across the arc docs at the S5 audit).

**Statement strength, decided in the slice design note
(`docs/2026-08-10_gospecc-decomposition.md` §6, option (a))**: the
SEEDED ∀-schedule family per row — kernel certificate
(`allStreamsOkPool`, via the slice's non-consuming-select refinement),
∀-schedule verdict readout, no-deadlock + no-race first-order
corollaries, `TerminatesNormallyC` — five kernel-checked theorems per
row in `Specs/GooseParityChannels.lean`, interpreter vocabulary
throughout. NOT the D1 pair: the frame-quantified `GoSpecC` triple is
out of reach for ALL SIX rows this slice (it needs the §3–§5
decomposition pipe PLUS a channel WP law family that does not exist,
sequentially or concurrently) — that is each row's recorded gap, owed
with the decomposition arc, not a silent skip. The verdicts, in table
row order (trio, muxer async/client, dsp:
1/1/1/"async"/"Hello, World!"/42), are the observables the R1
differential rows pin against `go run`.

Deltas, BOTH directions, no ordering claimed (upstream-model wording
corrected at the S4 audit round — the first form said "a model no
test executes", compressing away a distinction
`docs/2026-08-06_concurrency-research-goose-perennial.md` already
records): THEIRS are heap-general, compositional Iris triples about
the upstream FUNCTIONS (protocol/ghost-carrying, e.g.
`wp_DSPExample`'s dependent-separation-protocol session),
partial-correctness `NotStuck` — no termination, and no
deadlock-freedom (GooseLang blocking is loop-based, so `NotStuck`
holds of a parked-forever schedule). Their channel semantics is the
goose TRANSLATION of `goose/model/channel`, a hand-written Go package
that IS well tested in Go — 24 tests incl. direct side-by-side
comparisons against real Go channels, run in upstream CI, and the six
rows' own programs have upstream Go tests (`examples_test.go`,
`muxer_test.go`) — but the Rocq/GooseLang model itself and the
translation step are executed by no test. OURS are seed-concrete (no
frame quantifier), driver-level (the wrapper program, not a
compositional function spec), and quantify EVERY modeled schedule of
the differentially tested `execProg` with totality + exact verdict +
deadlock- and race-refusal-freedom.

| corpus row (imported-goose/channel/) | upstream @ 43d4efa | our disposition | where / gap |
|---|---|---|---|
| select-tricky-examples `nb-not-ready` | **Qed** (`wp_select_nb_not_ready`, channel_select_tricky_examples.v:71, Qed :114) | **∀-schedule family proved** (5 kernel theorems) | `ChannelSelectTricky.nbNotReady*`; gap: frame-quantified GoSpecC (decomposition + channel WP laws) |
| select-tricky-examples `nb-guaranteed-ready` | **Qed** (:117, Qed :137) | **∀-schedule family proved** | `nbGuaranteedReady*`; same gap (this one spawns nothing — the sequential-lane triple is ALSO blocked, on sequential channel WP laws; design note §6(c) declined this slice with the reason) |
| select-tricky-examples `nb-full-buffer-not-ready` | **Qed** (:219, Qed :258) | **∀-schedule family proved** | `nbFullBuffer*`; same gaps as `nb-guaranteed-ready` |
| muxer `async` | **no upstream lemma** for `Async` (searched `channel*.v`; `wp_HelloWorldAsync` channel.v:149 is the sibling `HelloWorldAsync`, a different function) | **∀-schedule family proved** (coverage row, not a parity row) | `ChannelMuxer.async*` |
| muxer `client` | **Qed** (`wp_Client`, channel_dsp.v:152, Qed :172) | **∀-schedule family proved** | `ChannelMuxer.client*`; the leaked parked server at main's exit is inside the modeled envelope (D6/L5) |
| actris-example (dsp) | **Qed** (`wp_DSPExample`, channel_dsp.v:35, Qed :57) | **∀-schedule family proved** | `ChannelActris.dsp*` |

**Population honesty — what the curated set does NOT cover.** The
upstream channel-examples proof tree at 43d4efa states **73**
Lemma/Theorem items (CORRECTED at the S5 records audit, at this
origin and every restatement: this paragraph first said **60**,
counted by a FILENAME glob — `channel*.v` +
`channel/{workq,etcd_session}.v` — that silently dropped
`elimination_stack.v` (8 items) and `lock.v` (5), an 18% undercount
in the self-favorable direction; both are channel-example proofs in
the same directory, listed in the matrix §5's verified set. The
corrected count is directory-derived and the command emits the
figure: in `new/proof/.../examples/`, `grep -hE '^(Lemma|Theorem)'
$(grep -l 'testdata\.examples\.channel' *.v channel/*.v) | wc -l` =
73; per-file: 12 channel.v, 9 google, 5 fibonacci, 3 search-replace,
3 higher-order, 9 dsp, 10 select-tricky, 4 workq, 5 etcd_session, 8
elimination_stack, 5 lock — helper lemmas included, all Qed-closed:
zero `Abort.`/`Admitted.` in these files). This slice's curated set
is the charter-fixed SIX rows above; of the remainder: fibonacci and
higher-order units are the recorded P2 import-parking (enumeration
cost, buildout ledger); muxer's `client-old`/`make-greeting` rows are
the same P2 entry (their upstream lemmas are Qed — `wp_MapClient`,
channel_dsp.v:271, Qed :313; `wp_makeGreeting`, :358, Qed :385 —
parity rows we cannot certify until the P2 cost call is made); google-search is imported and R1-green
(membership lane, tier=slow) but its three-worker fan-in — a
4-thread, width-4 schedule tree (enum-stats: ~40.0M steps, 59601
leaves) — is beyond this
checker idiom's cost envelope — not attempted, recorded ("5-worker",
the descriptor this line first carried, corrected at the S5 audit —
the program forks THREE workers, matching its 3! = 6 certified
arrival orders);
workq/etcd_session/search-replace and the channel.v basics are
imported (search-replace, google) or unimported upstream units — as
are elimination_stack and lock, both unimported — rows
for a later movement, not silently claimed.

Certificate fuels (measured minimum → shipped): nb-not-ready 100→200,
nb-guaranteed-ready 100→200, nb-full-buffer 100→200, dsp 200→400,
async 200→400, client 400→800. Full module kernel-checks in ~20 s.

## Counts (slice 3 close; corrected at the S3 audit fix round)

- **R3 proved: 6** programs × 2 kernel-checked theorems each
  (`GoSpecC` + pool readout twin). Against Perennial's measured set
  (28 proved / 36 stated `test_fun_ok`), the honest split of our six,
  BOTH directions:
  - **2 are upstream-Qed parity rows** (`testCompareNilToNil`,
    `testComparePointerWrappedDefaultToNil`) — the
    statement-by-statement comparison the arc charters;
  - **3 discharge oracles upstream ATTEMPTED AND ABORTED** (their own
    TODO comments name the missing non-nil-allocation/points-to
    lemmas) — rows where our result goes past theirs (context added
    at the arc-end audit: all three aborts are ONE missing
    SL-library lemma class — points-to non-nullness their predicates
    do not carry — which our concrete-heap model computes away; an
    assertion-language-design delta, not a semantic-reach one; the
    matrix §7.1 note carries the full form);
  - **1 is same-class coverage** with no upstream statement
    (semantics/block);
  - and the deltas AGAINST us are **five** upstream-Qed oracles, not
    one (delta-review recount): `testInterfaceNilWithType` (R1-green,
    R2-pinned, blocked only at R3 — the `&&` law gap) plus the FOUR
    frontend-blocked rows above (`testStructUpdates`,
    `testPrimitiveTypesEqual`, `testDefinedStrTypesEqual`,
    `testListTypesEqual` — `FAIL frontend-export` at R1, the
    short-circuit-operand quarantine), which they prove and we cannot
    yet run.
- Attempted and stopped: 0 (nothing shipped with open side-goals).
- Out-of-class: 1 (recorded gap: short-circuit law family).
- Not-attempted, reasons recorded: 5 (2 defer + const + rune +
  mapliteral).
- No-pinned-lowering population, recounted (S3 audit; the first
  version's "~72 of 78" used a stale pre-sync-tail denominator):
  the corpus has **82** imported-goose units
  (`find Corpus/coverage/exec/imported-goose -mindepth 2 -maxdepth 2
  -type d | wc -l`), 6 pinned → **76 unpinned**, of which **71** have
  ≥ 1 R1-green row and **64** are fully green (per-unit grouping of
  `baselines/native-full.tsv`'s 176 imported-goose rows: 70 all-pass,
  7 mixed, 5 all-fail). The all-fail 5 (recorded fail-closed
  frontend-export classes) were never "R1-green".

## Arc-close addendum (slice 5, 2026-08-10)

The slice-3 counts above are the dated record; the deltas since:
slice 4 added the three channel pin modules
(select-tricky-examples, muxer, actris-example — the
`check-imported-pins` PINS registry is the authority), so at arc
close **9 units are pinned → 73 unpinned** (the P-S3-2 lever's
denominator). Feature class 3 landed as recorded in its section (6
rows × 5 kernel theorems). The per-STATEMENT comparison artifact is
`docs/goose-perennial-comparison.md` §7; the arc-closure record and
the consolidated parked-items agenda are in
`docs/2026-08-09_spec-parity-arc-charter.md`.
