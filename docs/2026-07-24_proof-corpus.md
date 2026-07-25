# The proof corpus: making the calculus answerable to real Go (2026-07-24)

Decision of record (user direction). Companion to
`docs/2026-07-24_sequential-coverage-scoping.md` (the coverage ladder) and
to the non-vacuity gate in `CLAUDE.md`.

## 1. The gap this closes

The differential corpus pins **behavior**: 744 cases, 228 passing, growing
fast because cases are cheap. The proof layer pins **claims**: today that
is essentially ONE program (the golden `incViaCall` walk, in four
statement shapes) plus the `while (x==0){x=x+1}` witness. So the calculus
is known to work on two toys, and every new feature widens the behavioral
surface without testing whether we can still *prove* anything over it.

That asymmetry is the north-star risk in miniature. `etcd-io/raft` will
not be reached by a calculus whose laws each have a witness but which has
never been asked to compose them over an idiomatic function.

## 2. What a proof corpus is

A tracked set of **(differential case id → proven surface theorem)**
pairs. The programs come from the DIFFERENTIAL CORPUS — already canonical
Go, already oracle-validated — so a proof-corpus entry proves something
about a program we independently know the behavior of. That pairing is
the point: the differential says *what the program does*, the proof says
*what we can establish about it*, and both are about the same file.

The theorem should be a **surface judgment** — `GoFuncSpec` where the
shape allows (the engineer-readable form: "`f(args)` needs no heap and
returns 2"), else `GoSpec`/`GoTriple`/`GoInvariant`.

## 3. Selection criteria (this is NOT a mirror of the coverage corpus)

Proofs cost orders of magnitude more than corpus cases; a proof corpus
that chased coverage would stall the project. Entries are chosen to
stress the calculus, not to tile the language:

1. **Composition over breadth** — prefer one function that combines a
   loop, a call, and a conditional over three that each isolate one.
   Per-law witnesses already cover isolation; nothing else covers
   composition.
2. **Idiom over minimality** — write the program the way Go is actually
   written (early returns, `err` checks once errors exist, accumulator
   loops). A calculus that only proves un-idiomatic code is not useful
   for real Go, which is the whole claim being tested.
3. **North-star shapes** — as features allow, prefer miniatures of raft:
   a state-machine step function, a bounds-checked log append, a quorum
   count over a slice.
4. **One entry per feature AREA, not per feature** — the unit is
   "closures", "switch", "defer", not each sub-form.

## 4. Gating

Each entry is referenced from `proofs/Audit.lean` exactly as the existing
non-vacuity witnesses are (`example := @…`), so **deleting or breaking a
proof-corpus theorem fails the build**. The manifest below is the tracked
record; `scripts/ci` needs no new step because the Audit gate already
runs in-build.

## 5. Manifest

Format: `case id — theorem — what it stresses`. Seeded with what exists,
so the record starts honest rather than aspirational.

| differential case | theorem | stresses |
|---|---|---|
| `pointers/inc-via-call` | `GoLean.Surface.goldenFuncSpec` | call/frame protocol, pointer mutation through a callee, the D2-proper result read |
| `pointers/inc-via-call` | `GoLean.Surface.goldenInvariant` | per-step invariance over a whole call (what a triple structurally cannot say) |
| `control-flow/while-eq-single-iteration` | `GoLean.Iris.wp_while_eq_once` | the Löb loop rule with a real machine-walked condition |

**Owed, in ladder order** (each becomes an entry when its rung lands; a
rung is not "finished" until its entry exists, though slices need not
block on it):

- W1 tuples — a multi-result function proved at `GoFuncSpec`; stresses
  whether the frame-exit law generalizes past one result.
- W2 switch — `control-flow/switch-basic`'s `classify`; stresses the
  if-chain walk and whether case dispatch composes with early return.
- W5 closures — `functions/closure-share`; stresses reasoning about a
  captured cell aliased between two callees (the first genuinely
  separation-logic-shaped obligation in the corpus).
- W3 defer — `defer/multiple-lifo`; stresses frame-exit ordering.
- W4 structs/arrays — a bounds-checked accumulator over an array.

## 6. What this will find (predictions, recorded so they can be wrong)

Stated in advance so the exercise is falsifiable rather than
self-congratulatory:

1. The first non-golden entry will need laws that do not exist yet
   (`wp_call_value_enter` for closures; a multi-result frame exit). That
   is the intended signal, not a setback.
2. Walk plumbing will be the bottleneck before any law is *wrong* — the
   `iapply … fupd_intro; inext; …` chains are already the bulk of every
   proof, and they grow linearly with program size. If proving a
   twenty-line function needs a thousand-line walk, the calculus needs a
   tactic or a bind-form combinator, and we will have learned that from a
   real program rather than from theory.
3. `GoFuncSpec`'s v1 shape (unary int result) will bind first — the
   `(T, error)` widening is likely the first forced generalization.
