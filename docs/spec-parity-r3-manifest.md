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
| semantics (other R1-green units: comparisons, precedence, loops, switch, vars, operations, int-conversions, conversions, multiple-return, new, allocator, builtin, first-class-function, function-ordering, structs, slices, maps, interfaces, …) | 30 of their 36 `test_fun_ok` statements (incl. 25 of the 28 Qeds) lie in these trees | **no-pinned-lowering** | R1-green rows exist; their lowering terms were never pinned into `proofs/` (the R2 buildout pinned 6 units). Pinning is mechanical (the import pipeline's term generator + ci 1c5 guard) and is the scaling lever for the next R3 movement. |

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
    lemmas) — rows where our result goes past theirs;
  - **1 is same-class coverage** with no upstream statement
    (semantics/block);
  - and the one nil oracle we CANNOT do (`testInterfaceNilWithType`,
    the `&&` gap) is one THEY prove — the delta against us, recorded.
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
