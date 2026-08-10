# R3 manifest — GoSpec instances over the imported goose corpus

Standing record (spec-parity arc, charter D3): per-program disposition
of R3 (kernel-checked `GoSpecC` + first-order readout twin) over the
imported sequential-oracle class. Started at slice 3
(`docs/2026-08-10_wp-walk-driver.md`); updated whenever a row moves.
Every instance here is gate-checked (in-build Audit axiom sweep —
`propext, Classical.choice, Quot.sound` — and stated in
Surface/interpreter vocabulary); NOTHING here is designated unless the
arc-end curation (user-owned) says so.

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
(`Specs/GooseParityKit.lean`), TotalPins seed, verdict `1`.

| program (imported-goose) | their `test_fun_ok`? | disposition | where / why |
|---|---|---|---|
| semantics/nil `testCompareNilToNil` | **proved upstream** | **proved** (THE EXEMPLAR) | `Specs/GooseParityNilWP.lean` — `compareNilToNilSpecC` + `compareNilToNilReadoutC` (designation CANDIDATES) |
| semantics/nil `testCompareSliceToNil` | proved upstream | **proved** | same file, `compareSliceToNil*` |
| semantics/nil `testComparePointerToNil` | proved upstream | **proved** | same file, `comparePointerToNil*` |
| semantics/nil `testComparePointerWrappedToNil` | proved upstream | **proved** | same file, `comparePointerWrappedToNil*` |
| semantics/nil `testComparePointerWrappedDefaultToNil` | proved upstream | **proved** | same file, `comparePointerWrappedDefaultToNil*` |
| semantics/nil `testInterfaceNilWithType` | proved upstream | **out-of-class** | verdict uses short-circuit `&&` (`Expr.and`): NO WP law exists for the short-circuit forms (they have their own machine rules, not `strictPlan`). The `Expr.and`/`Expr.or` law family is recorded future law work. |
| semantics/block `testExplicitBlockStmt` | no (not in their 37) | **proved** (same-class coverage, not a parity row) | `Specs/GooseParityBlockWP.lean`, `explicitBlock*` |
| semantics/defer (2 oracles) | not in their 37 | **not-attempted** | R2-pinned; bodies use `deferCall` + `funcVal` closures — the defer drain laws exist (`Laws/Unwind`, cap1 family) but the walk composition is a different frame discipline than the kit wrapper; sized as its own movement. |
| semantics (other R1-green units: comparisons, precedence, loops, switch, vars, operations, int-conversions, conversions, multiple-return, new, allocator, builtin, first-class-function, function-ordering, structs, slices, maps, interfaces, …) | 30 of their 37 lie here | **no-pinned-lowering** | R1-green rows exist; their lowering terms were never pinned into `proofs/` (the R2 buildout pinned 6 units of 78). Pinning is mechanical (the import pipeline's term generator + ci 1c5 guard) and is the scaling lever for the next R3 movement. |

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

## Counts (slice 3 close)

- **R3 proved: 6** programs × 2 kernel-checked theorems each
  (`GoSpecC` + pool readout twin) — 5 of the 6 are rows of
  Perennial's proved-37 (`nil.v`), the statement-by-statement parity
  the arc charters.
- Attempted and stopped: 0 (nothing shipped with open side-goals).
- Out-of-class: 1 (recorded gap: short-circuit law family).
- Not-attempted, reasons recorded: 5 (2 defer + const + rune +
  mapliteral).
- No-pinned-lowering population: the remaining ~72 R1-green imported
  units (the import-tooling lever, not a proof gap).
