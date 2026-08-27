# The data-branch crossing kit (W3 mechanism unit, 2026-08-27)

> **SUPERSESSION BANNER (triage landing, 2026-08-27; added by the
> pre-merge audit, semantics-dimension M4).** §"Non-vacuity" below
> demonstrates the kit's ≥2-consumer requirement with three CallSpec
> members — `unstable.maybeLastIndex`, `unstable.maybeTerm`
> (`LogReadSpecs`), and `MemoryStorage.firstIndex`
> (`StorageWalkSpecs`). **Those three modules were DELETED in the
> 2026-08-27 triage** with the rest of the CallSpec calculus; they
> are recoverable at `archive/callspec-era`. Read that section as
> the historical demonstration, not as a live census.
>
> **The live non-vacuity witnesses** are the judgment-free
> mini-witnesses in `proofs/GoLeanProofs/Sym/CrossingWitness.lean` —
> `crossing_witness_lenNeg` (the class-1 normalize collapse via
> `normalize_int_eq`/`int_ofNat_cast`, plus the length read through
> `applyStrict_length_slice`, whose engine is `validateSlice_ok`),
> `crossing_witness_ifSplit` (`stepFn_ifK_true` as a span prefix),
> and `crossing_witness_read` (`loadLoc_base` →
> `applyStrict_indexGet_slice`). All three are span derivations over
> ABSTRACT states at symbolic lengths, pinned in
> `proofs/Audit/Landing.lean`. The kit itself is unchanged and
> judgment-free; only its consumers moved.
>
> Two kit members carry in-tree SCAFFOLD labels because the deletion
> left them at zero consumers: `applyStrict_deref` (resume: G-REPR/
> G-CALLS) and the `normalize_uint64_eq`/`normalize_uint64_ofNat`/
> `normalize_int_ofNat` group (resume: first live consumer). The
> kit's forward consumers remain the correspondence and ∃-side
> discharge work of the G-units.

One writer: the W3 crossing-kit worker (`w1-prover` lane, U3.1-F's
successor). Deliverable: `proofs/GoLeanProofs/Sym/Crossing.lean` +
this note. Consumers: the U3.1-F remainder (this unit's second half),
then every data-branching member of clusters B/C/D/E.

## The problem (park record §U3.1-F, re-verified before design)

The F proof pattern closes whole call spans by ONE `kernel_rfl` at a
symbolic footprint family. Kernel reduction decides a machine step
only when its scrutinees bottom out on constructors. Two universal
stuck classes block every remaining F member — both REPRODUCED this
session before design (park-record re-verification):

1. **Store-time `IntKind.normalize` on a symbolic scalar**
   (`artifacts/w3/kit-stuck2.out`): `IntKind.normalize .int
   (Int.ofNat (k+1))` is a stuck `%`/`if`-term at free `k`; any later
   branch on that scalar (maybeLastIndex's `l != 0`) is kernel-stuck.
2. **`validateSlice`'s symbolic Nat-Nat `len > cap`**
   (`artifacts/w3/kit-stuck1.out`): stuck at free `len`/`cap` (the
   reducer diverges through the refusal message's `Nat.repr`); the
   len-0 control reduces to `.ok ()` — exactly the landed empty
   member's escape. Blocks every symbolic-length slice length/index
   read.

A third class surfaces as soon as class 2 is crossed: **symbolic-heap
reads** — an index read at a symbolic index into a symbolic backing
array yields a non-constructor value, and every subsequent scrutinee
of it is stuck.

## LINEAGE

Classic symbolic execution's PATH CONDITION (King 1976): at a branch
whose condition is not decidable from the symbolic state, fork the
execution, assume the condition (resp. its negation) on each path,
and continue; a path's result holds for every concrete state
satisfying its path condition. Symbolic memory reads under
constraints are the companion classic (array theory in symbolic
executors). WHERE THIS CONSTRUCTION DIVERGES: our execution engine is
KERNEL REDUCTION of the reflected interpreter (computational
reflection), not a metatheoretic executor — so the fork is realized
as a WINDOW SPLIT: the span equation is cut at the last config
boundary before the stuck step, the path condition enters as a
theorem HYPOTHESIS consumed either by a conditioned step lemma (the
StepKit idiom, extended here) or by a rewrite of the window's exit
term, and the arms recombine by ordinary case analysis at the spec
statement. Windows stay `kernel_rfl`; only the crossing step is
lemma-mediated. The barrier/open-tail discipline (W1) is unchanged —
splits are orthogonal to the frame barrier.

## Quantifier audit

The kit advances **∀-state at spec boundaries**: a member's footprint
family with a data branch is covered by case analysis over the PATH
CONDITION — the case split IS the discharging rule, and each arm's
window chain covers a whole state family per step (symbolic
execution, the charter's sanctioned engine). This is NOT enumeration:
the split is over the reflected program's own branch structure
(if/else arms, error arms), never over a subject run; the number of
cases is the program text's branch count, a reflected-program shape
constant. Recombination: a join spec ∀-quantified over the family
parameter proves by `match`/`rcases` on that parameter (e.g. slice
length `0` vs `k+1` — a constructor-complete split), citing the arm
members.

## The kit's contents (all in `Sym/Crossing.lean`)

Value-level path-condition lemmas feeding the EXISTING conditioned
step lemmas (`StepKit.stepFn_strict_apply`, `stepFn_store_step`,
`stepFn_var`, `stepFn_return_frame` — the ≥2-consumer promotion this
kit builds on rather than re-invents):

1. **Branch crossings** (class A — config-boundary `Bool` matches):
   `stepFn_ifK_true` / `stepFn_ifK_false` — the `.retV (.bool b)
   (.ifK …)` step under `b = true`/`b = false`. (The `whileK`/`andK`/
   `orK` siblings are consume-on-demand — no U3.1-F member branches
   there; recorded, not built.)
2. **Comparison bridges**: the machine's comparison booleans are
   `decide`-shaped (`valueLess` etc.) or `BEq`-shaped (`valueEq`);
   core `decide_eq_true`/`decide_eq_false` plus `Int.beq` bridge
   lemmas convert reader-vocabulary range facts into the exact stuck
   `Bool`, which is then REWRITTEN in the window's exit config (the
   rewrite-then-continue convention) or fed to the class-A lemmas.
3. **Normalize collapses** (class 1): `IntKind.normalize .int v = v`
   under `-2^63 ≤ v < 2^63`; `.uint64` under `0 ≤ v < 2^64`; `ofNat`
   corollaries. Consumed as rewrites on window exits: the stored
   stuck payload collapses to its constructor form and the next
   window's `kernel_rfl` proceeds (often making the following branch
   self-reducing — the maybeLastIndex shape).
4. **`validateSlice` collapse** (class 2): `validateSlice ⟨some b, o,
   n, c⟩ = .ok ()` under `n ≤ c`; plus the per-op result lemmas
   `applyStrict_length_slice` (the `len` builtin under it) and
   `applyStrict_indexGet_slice` (the slice index read under validity
   + range + backing-read facts) — each discharging
   `stepFn_strict_apply`'s hypothesis at its op.
5. **Symbolic-heap read support** (class 3): the index/deref crossing
   hypotheses are reader-vocabulary heap facts (`Heap.lookup … =
   some …`, `values[j]? = some v`) carried by the footprint family —
   the same `stepFn_strict_apply` route through `applyStrictOp`
   computations under those facts.

**The window-split convention** (the composition discipline, enforced
by use in this unit's members): a member's span = `kernel_rfl`
windows chained by `stepFnIter_chain`, crossings as `stepFnIter_one`
of a conditioned step, hypothesis rewrites applied to window exits
between links. Step counts, window boundaries, and stuck normal
forms stay PRIVATE proof-body scaffolding (the W1 convention);
exports are count-free `CallSpecR`s whose extra hypotheses are
reader-vocabulary range/heap facts the invariant supplies.

## Non-vacuity (≥2 genuinely different consumers, demonstrated in
this unit)

1. `unstable.maybeLastIndex` nonempty arm: class-1 collapse + the
   class-2 length crossing (branch self-reduces after collapse), and
   the empty/nonempty JOIN spec demonstrates recombination.
2. `unstable.maybeTerm`: a genuinely symbolic two-scalar comparison
   (`i < u.offset` at free `i`, `offset`) — the class-A/bridge route,
   plus the class-3 in-range entry read.
3. `MemoryStorage.firstIndex`: the `ents[0]` symbolic-length index
   read — `applyStrict_indexGet_slice` at a literal index, symbolic
   length (a different stuck shape from 1: the comparison
   `0 < len` reduces, the VALIDATION does not).

## Scope and retirement

The kit is untrusted proof-layer machinery (no GoCore, no Audit, no
scripts). It carries no subject-run constants. Retirement condition:
if a future mirror/abstract-domain evaluator subsumes data-branch
crossing (Sym/Domain's territory), the kit's members retire to it;
until then every W3 cluster is a consumer. Extensions
(whileK crossing, map-read crossings, further IntKind collapses) are
consume-on-demand, each proved on admission.
