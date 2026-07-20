# Known fidelity bugs — the SINGLE canonical index

A **fidelity bug** is a case where GoLean gives a *wrong* answer relative to real
Go: a wrong value, or a wrongly-*stuck* run on a construct we claim to support.
(A construct we don't model yet is not a bug — it must fail closed at the
frontend boundary as `frontend-export`, and is tracked as coverage, not here.)

This file is machine-cross-checked against the recorded differential **baseline**
(`baselines/native-full.tsv`) by `scripts/check-bugs.sh` (part of `scripts/ci`),
so a bug can neither rot in prose nor silently outlive its evidence:

1. every `- Cases:` id of an open `Pinned-by: differential` bug **exists in the
   baseline and is currently `FAIL`** — if a listed case now `PASS`es, the bug is
   fixed-but-not-closed (or the case no longer pins it), and the check fails;
2. every `Status: open` + `Pinned-by: differential` bug lists ≥1 case;
3. (warning) the check reports how many baseline **fidelity failures**
   (`stage=lean-observation` or `stage=differential` — wrong/stuck answers, not
   frontend-coverage gaps) are **not** yet explained by any bug entry — the
   omission surface to ratchet toward zero.

Bugs that cannot yet be mechanically pinned use `Pinned-by: none (<reason>)` and
are exempt from (1)/(2) — but still listed, so they cannot disappear.

**Entry format (keep parseable):** a `## BUG-NNN — <title>` heading, then
`- Status: open|fixed`, `- Pinned-by: differential|none (<reason>)`, and (for
differential-pinned) `- Cases: <id>, <id>, …` (baseline case ids), then prose.

---

## BUG-001 — struct-field / array-element WRITE lowers an address base as a value

- Status: open
- Pinned-by: differential
- Cases: structs/copy-value, structs/pointer-field, arrays/arrays
- Discovered: 2026-07-19 (directional audit, finding F1)

Writing through a struct field or array index — `b.n = 7`, `a[1] = …`,
`p.n = …` — fails closed at `lean-observation` with "expected address value, got
GoLean.GoValue.struct/array". Root cause is in the **frontend lowering**, not
GoCore: `tools/nativefrontend/emit.go` `fieldBase` (~736) and `emitAddressOf`'s
`SelectorExpr` case (~814) lower the base via a value-read (`.var`) where the
*address* path needs an address base (`.ref`/`.fieldAddr`). GoCore's
`valueAsLoc` correctly rejects the struct/array value and fails closed — so this
is a visible stuck, not a silent wrong answer, but the interpreter cannot perform
one of the most common Go mutations. On the north-star path (raft mutates struct
fields pervasively). GoCore already has the right primitives (`fieldAddr`,
`indexAddr`); the fix is in `emit.go`. Also: `docs/native-frontend-goal.md`
overclaims "field/index access" as working (true for reads, false for writes) —
correct it when the lowering is fixed. Tracked in `TODO.md` (F1).
