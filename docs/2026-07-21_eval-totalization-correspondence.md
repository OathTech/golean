# Arc B (punch-list item 6): Eval totalization → interpreter/relation correspondence

Date: 2026-07-21. Branch `eval-totalization`. This is the L4 wall: joining the
differentially-validated interpreter (`Eval`) to the Iris-proven relation
(`Rel`) so proofs over the relation are claims about the artifact the corpus
validates against real Go.

## Part 1 — Totalization (DONE, this commit)

The big-step cluster (`execStmt` + 8 siblings) is now **total**; GoCore has
zero `partial def`s (including `GoString.compareAt`, totalized on
`left.size - index`). Approach — behavior **bit-identical** by construction:

- `execDecl`/`execDecls` hoisted out of the `mutual` block (they never recurse).
- The two `if fuel == 0 then stuck` guards restructured as structural
  `match fuel with | 0 | fuel' + 1` — same semantics, decrement now visible to
  the termination checker. Fuel is consumed at exactly the two back-edges it
  always was: function-body entry and the `while` back-edge.
- Lexicographic measure `(fuel, statement size, tiebreak)`:
  statement size covers structural descent (`seqn`/`block` elements, `if`
  branches, loop/`mapRange` bodies); the tiebreak orders the same-fuel call
  chain (`execFunctionCall (3) → …WithLocs (2) → …WithValues (1)`, each
  `< sizeOf stmt ≥ 1` of the `.call` that invoked it) and `mapRange`'s
  shrinking snapshot (`1 + remaining.size`, with the body call at tiebreak 0).
- `execMapRangeLoop`: `eraseIdx! → eraseIdx` with the in-bounds proof from the
  (now-named) `remaining[idx]?` match — identical in-bounds behavior.

Payoff: the cluster now has equational lemmas and a functional induction
principle (`execStmt.induct` etc.) — the prerequisite for everything below.
Validation: full `scripts/ci --diff` (zero baseline drift required, since the
change is semantics-preserving).

## Part 2 — Correspondence design (the bridge, decided before proving)

### State bridge: the relation is locals-agnostic

The interpreter resolves names via `ExecState.locals` and mutates it
(`declareLocal`, push/pop scopes). The relation (CEK) resolves via
`Config.env` and **never reads or writes `state.locals`** — its rules touch
only heap/nextAddr (and read types/functions). Consequently, along any
relation derivation the state's `locals` field is frozen at its initial value,
while the interpreter's evolves. The correspondence therefore relates states
**up to the `locals` field**:

- `ExecState.withLocals σ L := { σ with locals := L }`.
- Substrate transport lemmas (all straightforward, since no substrate op the
  relation mentions reads `locals`): `loadLoc (σ.withLocals L) = loadLoc σ`,
  `storeLoc` commutes with `withLocals`, `alloc` commutes, `defaultValue`,
  `normalizeValueForTy`, `valueEq` invariant, `functions` field preserved.
- Statement soundness shape (normal outcome):
  `execStmt fuel σ ch stmt = .ok (.normal σ', ch') → Steps (.exec stmt σ.locals k) (σ.withLocals L) (.next k) (σ'.withLocals L)`
  (∀ L, ∀ k — the generality both the frame case and the top-level statement
  need; the headline instantiates `L := σ.locals`, `k := .stop`).
- Env bridge invariant: at each simulated point, the relation's `env` equals
  the interpreter's **current** `σᵢ.locals` (declare/push/pop on the
  interpreter side correspond to env extension / continuation-carried envs on
  the relation side).

### Value/heap fragment: correspondence needs shape conditions

The interpreter is *richer* than the relation (e.g. `add` also concatenates
strings; the relation has no string-add rule), so the unconditioned
"interpreter ok ⇒ relation reaches" statement is **false** — a `var` can load
a string from the heap and feed it to `add`. The honest per-arc scope
(mirroring the punch list's "scalar+pointer fragment"):

- `FragVal v` — v is `.int`/`.bool`/`.addr`/`.nil`.
- `HeapFrag σ` — every heap cell holds a `FragVal` (preserved by fragment
  stores/allocs; pointer/int/bool `defaultValue`s are `FragVal`s).
- `ExprFrag e` / `StmtFrag s` — the syntactic fragment (var, intLit, boolLit,
  add/sub/mul/div, eqCmp, ref, deref; assign, initialization, seqn, block, if,
  while, return/break/continue, call).

Under these, interpreter success forces the int paths (e.g. `add` on
`FragVal`s that succeeds is on ints), and each relation rule's premises are
recoverable from the interpreter run plus transport.

### Discovered divergences (found by attempting the statement — the point of L4)

**D1 — nested `.seqn` scoping: the relation cannot run frontend output.**
The frontend routinely emits Go `x := 5` as `.seqn #[.initialization x,
.assign x 5]` (see `NativeToIR.decodeAssign`, also `decodeVar`,
comma-ok/blank-target desugarings), spliced as an *element* of the enclosing
block's statement list. The interpreter's `.seqn` is scope-transparent, so the
binding persists for the rest of the block — matching Go, where a statement
list splices and only *blocks* scope. The relation wraps every executed
`.seqn` in its own `Cont.seq` and **discards that seq's env at `seqDone`** —
so the binding dies at the end of the desugaring seqn and any later use is
*stuck*. Consequence: interp→rel correspondence over frontend-emitted
programs is false today; it holds only for hand-modeled shapes (all current
proof subjects, e.g. `sliceProg`, where initializations are direct elements
of the governing seq). **Proposed fix (own slice — semantic Rel edit, full
audit class):** a *splice* rule
`Step (.exec (.seqn ss) env (.seq rest env k)) s (.next (.seq (ss.toList ++ rest) env k)) s`
(same-env pattern, exactly like `Step.initialization`'s), with the existing
wrap rule guarded off the seq-matching case to stay deterministic; downstream
`wp_seqn` and witnesses re-proved. Until then, the correspondence theorem
carries a well-formedness side condition ("initializations extend only their
own governing seq").

**D2 — named-result shadowing at `return`.** `frameReturn` reads results via
the `returning`-carried env — the env *at the return point*, innermost scopes
included — while the interpreter reads them after block scopes have been
popped (frame scope). If an inner block shadowed a named result, the relation
reads the shadow (wrong vs Go); the interpreter is right. Unreachable from
frontend output (it synthesizes `$res0`-style result names and explicit
assignments, and user code cannot shadow `$`-names), but a real relation-vs-Go
gap to fix when `frame`/`returning` are next touched — cleanest fix: stash the
result *locations* in `Cont.frame` at call time (also erases the fall-through
results gap noted in `Rel.lean`).

**D3 — missing panic-propagation rules in `ExprR`.** The relation propagates
operand panics only through `add/sub/mul/div` (`binPanicLeft/Right`); `eqCmp`
and `deref` operands have no propagation rule, so e.g. `(1/0) == x` panics in
the interpreter with no relational derivation. Fix alongside D1 in the
Rel-completion slice. Until then the panic-side bridge covers the arithmetic
core only (note `deref` of a nil pointer IS covered — `valueAsLoc .nil`
panics with exactly `derefNil`'s message).

### Proof plan (per-construct lemmas, then the fragment capstone)

Landed 2026-07-21 (commits 821b07d, 9b38254, + statement-layer foundation):

1. **Transport lemmas** (DONE): `withLocals` + field simps; `loadLoc`/`alloc`
   unconditional; `normalizeValueForTy`/`defaultValue`/`valueEq`
   state-*independent* at `TyFrag` types (their equations neither read
   `state.types` nor recurse — much cheaper than the general
   `mutual_induct` transports, which remain the documented widening path);
   `storeLoc` at base locations conditioned on the cell's declared type
   being `TyFrag` (supplied by `HeapFrag`).
2. **Expression bridge** (DONE): `evalExpr_frag_ok` — fragment evaluation
   preserves state, yields `FragVal`s, and maps to `ExprR` with
   `env := σ.locals` over any transported state. Axiom-clean.
3. **Assignee bridge** (DONE): `evalAssigneeLoc_frag_ok` (var + addr).
4. **Heap preservation** (DONE): `lookup_set_cases` (no `BEq`-lawfulness
   reasoning needed), `heapFrag_set/alloc`, `storeLoc_frag` (success forces
   base locations, preserves `HeapFrag`, leaves locals untouched).
5. **First statement-level lemma** (DONE): `execStmt_assign_ok` — an
   interpreter assignment IS `Step.assign`. Axiom-clean.

### Statement-layer design (the remaining lift — shapes fixed, next session)

Two mutual theorems by `(fuel, sizeOf stmt)` recursion mirroring the
interpreter's own measure, over two predicates: `StmtFragNS` (non-spine
statements: assign, if/while with NS bodies, block, NS-only nested seqns,
return/break/continue — **no** `.initialization`, which dodges D1 exactly)
and spine lists (NS ∪ `.initialization` with `TyFrag`):

- **T1 (statement, NS)** `execStmt fuel σ ch stmt = .ok (out, ch')` →
  `HeapFrag out.state` ∧ outcome-indexed conclusion:
  normal → `σf.locals = σ.locals` ∧ `∀ L k, Steps (.exec stmt σ.locals k)
  (σ.withLocals L) (.next k) (σf.withLocals L)`; broke/continued → same
  with `.breaking k`/`.continuing k`; returned → `∃ Eret, … (.returning
  Eret k) …` (Eret uncharacterized until the call/frame layer, which needs
  the no-result-shadowing WF condition from D2).
- **T2 (spine list)** from `.next (.seq ss σ.locals k)` to `.next k`, with
  the weaker locals claim `σf.locals.popScope = σ.locals.popScope` (what
  `block` consumes) plus init-free ⇒ locals equality (what NS seqn
  consumes). `Step.initialization` aligns because the interpreter's
  `declareLocal` is literally `alloc` + env-`declare`
  (`declareLocal_eq_alloc`), and the list-level env is re-synced to
  `σᵢ.locals` at every element.
- **Call/frame layer** (after T1/T2): `BindParamsR`/`DeclsR`/`ResultsR`
  bridges + the D2 no-shadowing condition; then the capstone fragment
  version of `interpreterSoundStatement`.

Panic-side: arithmetic core only until D3 is fixed.
