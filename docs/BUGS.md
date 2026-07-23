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

## BUG-002 — expression-step atomicity is wrong for concurrent Go (latent)

- Status: open
- Pinned-by: none (latent — `Rel` has no goroutine rules yet, so no
  concurrent claim is derivable today and no differential case can pin it;
  it becomes a live unsoundness the day concurrency lands without the fix)
- Discovered: 2026-07-22 (arc E loop-law review of the Goose divergence;
  classified a BUG, not a caveat, at user direction — concurrency is
  committed, so "coarser than Go" is wrong-by-default, not a scope note)

`ExprR` is a big-step premise relation inside statement steps, so a
compound expression reading several cells (`x == y`, `x == y+z`) is ONE
atomic `Rel` step. Real Go interleaves goroutines between the reads. If
goroutine rules are added over the current granularity, the model UNDER-
approximates real behaviors (misses torn reads), and Iris invariant
opening "around one atomic step" licenses reasoning across a multi-read
window — together enough to prove theorems false of real Go for racy
programs (e.g. invariant-mediated plain reads racing a two-step writer:
the model never shows the mixed pair a real schedule can produce). The
DRF escape ("coarse ≡ fine for race-free programs") is NOT self-enforcing:
the logic would verify such racy programs without complaint, so carrying
this granularity into a concurrent `Rel` violates fail-closed (a hidden
wrong answer, not a visible red).

**Consequence: the concurrency arc (F4) is BLOCKED on resolving this.**
Sequentially it is NOT a bug — GoCore `Expr` has no call constructor (the
frontend must lower calls out of expressions), so no sequential program
distinguishes the granularities; every current theorem is unaffected.

Fix paths (F4 decides; record the choice there):
1. **Refactor expression evaluation into the configuration language**
   (small-step expression machine): word-level granularity, `wp_bind` and
   `wp_atomic` become available (retiring two recorded workarounds), and
   the calls-in-expressions trigger in `Rel.lean` points the same way.
   The likely eventual fix; substantial correspondence rework.
2. **v1 confinement concurrency**: goroutine-confined heaps, ownership
   transferred only via channel externs (CSP-style) — no shared-memory
   invariants in v1, making expression granularity moot; matches the
   etcd-raft north star's actual architecture (single-threaded core,
   message passing). Defers (1) to a lock-free-code widening.
3. Law-discipline restriction (invariants openable only around
   single-access steps): fragile, easy to violate silently — likely
   reject.

See `docs/2026-07-22_arc-e-while-invariant.md` §2′ (the sequential
justification) and TODO.md F4 (the charter). This entry exists so the
constraint cannot rot in prose while goroutine machinery is built.

**Scope sharpening (2026-07-22, same day):** the full fix is bigger than
expressions. Even a small-step expression machine leaves `Step.assign`
bundling its reads and its write in one step — true word-level atomicity
requires decomposing statement steps into a HeapLang-style memory-op
machine, a major reshape of the trusted relation. This strengthens the
case for fix path 2 (confinement v1) and for making the F4 *decision*
early even while the *fix* is deferred: the rework cost of path 1 scales
with fragment size, so every Arc-E widening rung built before F4 decides
deepens the potential hole. Recommendation recorded: write the F4 note
before or alongside the next major fragment widening (structs/arrays),
not after.

**Direction pinned (2026-07-22, user):** fix path 2 (confinement-only
v1) is REJECTED as the target — it excludes most actually interesting
concurrent Go (mutex-protected shared state, sync/atomic, lock-free
patterns); "CSL-proofs-only is a trivial kind of concurrency." The target
is full shared-memory, fine-grained concurrency with the complete Iris
apparatus. Path 1 (the memory-op machine) is THE fix, and its scope is
larger than first recorded: the INTERPRETER is in scope too — it is the
executable side of the Choices split, and instantiating real schedules
requires preemption points at memory-op granularity (big-step `evalExpr`
cannot be preempted mid-expression; an earlier claim that the interpreter
survives unchanged was wrong). Alignment note: Go's sync/atomic is SC, so
an SC interleaving model at memory-op granularity honestly covers
atomics-based code; plain-access races remain out of verification scope
(UB-ish in Go — same position as Goose). Sequencing consequence: the
reshape is unavoidable and its cost scales with fragment size, so it
should be the next MAJOR arc after the current rung — BEFORE the
structs/arrays widening, which would otherwise be built twice.
