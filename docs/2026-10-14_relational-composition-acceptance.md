# RD5 composition acceptance — 2026-10-14

[USER] 2026-10-14: take RD5 requests A–D ahead of C1, independently of any
unfinished C1 work. Return checked adapters, acceptance and an independently
audited immutable pin. No merge, push or peer-worktree writes. The lane was
clean at `ed9058ef04b73ac7287dd94a9bca8e4532a5eb04`; no C1 work had started
or been dispatched, so no C1 changes are included or waiting to resume.
Audited baseline: `67f7d1c5ba6a96055a41802b978386d019e03c67`.

## Frozen inputs and scope

Logic implementation `b6c31fb74f8817fd3ae6d90790204e0eabbc6d80`, reviewed
handoff `66920605c244badf346352e241089951fd57d13d`. The stage is
`docs/2026-10-14_relational-composition-stage.md`; the result review is
`docs/2026-10-14_rd5-result-review.md` at the handoff commit (it is not present
at the implementation commit). The coordination request is
`relational-demo-brief/docs/2026-10-14_rd5-phase-relay.md`.

All 75 files of `experiments/2026-10-14_relational-codex/` were frozen from
the implementation with `git archive` before building. Requests, targets and
client proofs are unchanged. SHA-256:

- `RelationalCodeX/CompositionRequests.lean`: `2fbf57fb4749c85820edf68e552d823f740856ac3a68e43ec30c031b542161cf`.
- `RelationalCodeX/CompositionTargets.lean`: `c59cc14630a74be8debfb7e82e1181bb7d2285695a8f4b16d52d307904aba622`.
- `RelationalCodeX/AddObligations.lean`: `0b1b79aa29ccfb3e5cb8d42165600c43df84c42a01b8d89e291324f1fad20f0f`.

Lean 4.32.2 and the original dependency pins are unchanged:
Iris `e7a0a43814c4f1154ca0c8049883ca56c2288b86`, Batteries
`023ce7d62a0531e22a5331e20b587817a80d49ff`, Qq
`38d591e778f100aec9762bb582f9c7f55f50e9dc`. Every clone/cache is independent. Only the scratch GoLean pin and appended harness
library targets change; the peer worktree is a read-only input.

## Public interface and mapping

All exports are in `GoLean.GoCore.Relational`, through `GoLean.Relational`.
No permanent production export imports Iris or a downstream module.

| Request | Public support | Exact adapter |
| --- | --- | --- |
| A `DeliveryPhases` | `OrderedWrites`, `CallBoundary.delivery_phases` | `RD5Acceptance.delivery` |
| B `VariableExpressionPhases` | `ReadOnlyExpr`, `variable_expression_phases` | `RD5Acceptance.variableExpression` |
| C `WhilePhases` | `WhileControl`, `while_control` | `RD5Acceptance.whilePhases` |
| D `Uint64IncrementPhases` | `ReadOnlyExpr.variable`, `.deref`, `.int_literal`, `.add_int`, `pointer_rhs_phases` | `RD5Acceptance.increment` |

[AGENT] 2026-10-14: compose expression paths through `ReadOnlyExpr` and expose
one assignment effect, reusing the existing `StorePath`/`StoreEffect` vocabulary.
D remains a derived compatibility proof. The pointer assignment law covers
`*p = rhs` for arbitrary read-only RHS and pointee, rather than every possible
address-former chain. Those chains are decomposed by the machine and defer
checks to store time; this batch does not export that machinery or pretend
all pointer expressions have the same assignment walk. No A–D statement is
narrowed by this boundary.

Delivery reads all callee results before any destination write, then uses
`OrderedWrites` to expose each store update and all intervening paths. Locations
may repeat, be interior, or overlap result cells. Read facts are not required
after writes. `ResultSlots` is the frozen request's premise and remains derivable
from `LocalEntry.resultSlots`; no additional caller validity premise is added.
Both normal exits and zero/nonzero results are covered, without a safety or
admission condition on the final caller continuation.

`ReadOnlyExpr` includes continuation-uniform intermediate preservation and
source admission. Dereference retains continuation-dependent access traces;
typed addition uses `IntKind.normalize`, including modular uint64 overflow.
Binding reads retain the existing root-only `loadRoot` domain; pointee reads
and writes retain arbitrary locations. Original RD4 assignment phase statements
are preserved, now derived through the shared assignment composition. RD3's
weaker endpoint-only operand contracts remain unchanged.

The while view has a real admitted entry transition, not a reflexive path.
Selection, repeat, continue, break and return concern control only. Invariants,
Iris later/mask obligations, body safety, cleanup and observer silence remain
downstream. No labelled-control, termination or full Add contract is claimed.

## Exact GoLean-only compatibility source

Save as `CompositionAdapters.lean` beside the frozen request module:

```lean
import RelationalCodeX.CompositionRequests

namespace RD5Acceptance
open GoLean GoLean.GoCore GoLean.GoCore.Relational RelationalCodeX

theorem writes {ctx ls vs c d} (h : OrderedWrites ctx ls vs c d) : WritePath ctx ls vs c d := by
  induction h with
  | nil path => exact .nil path
  | cons path effect _ ih => exact .cons path effect ih

theorem delivery : DeliveryPhases := by
  intro ctx b mode locs vs count values valid bound
  obtain ⟨before, pre, rest⟩ := b.delivery_phases mode ctx locs vs count values valid bound
  exact ⟨before, pre, writes rest⟩

theorem variableExpression : VariableExpressionPhases := by
  intro ctx env k dst target rhs value fact bound path
  exact variable_expression_phases ctx env k dst target rhs value fact bound path

theorem whilePhases : WhilePhases := by
  intro ctx guard body env k
  let view := while_control ctx guard body env k
  exact ⟨view.test, view.next, view.admission,
    (fun s => ⟨_, (view.enter s).1, rfl⟩), view.select, view.repeatPath,
    view.continuePath, view.breakPath, view.returnPath⟩

/-- D is assembled from reusable expression and assignment laws. -/
theorem increment : Uint64IncrementPhases := by
  intro ctx env k id slot target a bound
  let fact := fun s => loadRoot ctx s slot = .ok (.addr target) ∧
    loadLoc ctx s target = .ok (.int a.toNat .uint64)
  have pointer : ReadOnlyExpr ctx fact env (.var id) (.addr target) :=
    (ReadOnlyExpr.variable ctx env id slot (.addr target) bound).weaken (fun _ h => h.1)
  have pointee := pointer.deref (.int .uint64) (fun s h => h.2)
  have one : ReadOnlyExpr ctx fact env (.intLit 1 .uint64) (.int 1 .uint64) :=
    (ReadOnlyExpr.int_literal ctx env 1 .uint64).weaken (fun _ _ => trivial)
  have sum := ReadOnlyExpr.add_int .uint64 pointee one
  have modular : IntKind.uint64.normalize (a.toNat + 1) = (a + 1).toNat := by
    simp [IntKind.normalize, IntKind.bits?, IntKind.bitsAt, IntKind.signed,
      BitVec.toNat_add, Int.natCast_add]
  rw [modular] at sum
  exact pointer_rhs_phases ctx env k id slot target _ _ fact bound (fun _ h => h.1) sum

#print axioms delivery
#print axioms variableExpression
#print axioms whilePhases
#print axioms increment
end RD5Acceptance
```

## Guarded acceptance wrapper

Save as `CompositionAcceptance.lean` in the full frozen package. This closes
Alias and rechecks Pair/Set/Keep. B/C/D remove only the semantic-law arguments
from the intermediate Add acceptances and invariant rule; all other binders
and premises remain. There is deliberately no `AddTarget` proof.

```lean
import RelationalCodeX
import CompositionAdapters

namespace RD5Acceptance
open GoLean GoLean.GoCore GoLean.GoCore.Relational RelationalCodeX
open GoLean.Logic GoLean.IrisCustomer Iris

theorem aliasTarget : AliasTarget := alias_body_at_acceptance delivery
theorem pairTarget : PairTarget := pair_body_at
theorem setTarget : SetTarget := set_body_at
theorem keepTarget : KeepTarget := keep_body_at

noncomputable section
variable {ctx : ProgramCtx} {GF : BundledGFunctors} [GoGS GF]
variable {md : Safe.Index} {E : CoPset} {Φ : Safe.Outcome → IProp GF}

-- These specialize the existing intermediate statements, retaining all other
-- binders and logical premises. None is a proof of AddTarget.
abbrev addCounterInit := @add_counter_init_acceptance ctx GF _ md E Φ variableExpression
abbrev addLoopEntry := @add_loop_entry_acceptance ctx GF _ md E Φ whilePhases
abbrev addIncrement := @add_increment_acceptance ctx GF _ md E Φ increment
abbrev whileInvariant := @wp_while_invariant ctx GF _ md E Φ whilePhases

#print axioms aliasTarget
#print axioms pairTarget
#print axioms setTarget
#print axioms keepTarget
#print axioms addCounterInit
#print axioms addLoopEntry
#print axioms addIncrement
#print axioms whileInvariant
#eval RelationalCodeX.audit
end
end RD5Acceptance
```

## Reproduction

Use a clean implementation checkout (or its docs-only successor). Export the
frozen package from the logic repository; never build in the peer tree:

```sh
set -euo pipefail
mkdir -p .tmp/rd5 .tmp/rd5-semantic/RelationalCodeX
git -C /home/mike/projects/golean-logic/.claude/worktrees/relational-demo \
  archive b6c31fb74f8817fd3ae6d90790204e0eabbc6d80 \
  experiments/2026-10-14_relational-codex/ |
  tar -x -C .tmp/rd5 --strip-components=2
cp .tmp/rd5/RelationalCodeX/CompositionRequests.lean .tmp/rd5-semantic/RelationalCodeX/
cp lean-toolchain .tmp/rd5-semantic/
```

Save the adapter block in both scratch packages. Semantic-only `lakefile.toml`:

```toml
name = "RD5Semantic"
version = "0.1.0"
defaultTargets = ["CompositionAdapters"]
[[require]]
name = "GoLean"
path = "../.."
[[lean_lib]]
name = "RelationalCodeX"
globs = ["RelationalCodeX.CompositionRequests"]
[[lean_lib]]
name = "CompositionAdapters"
```

Run `LEAN_NUM_THREADS=2 capped lake build` in `.tmp/rd5-semantic`.
For guarded acceptance, set only the scratch `pins.json` GoLean entry to the
immutable implementation pin in the checked result below, then bootstrap:

```sh
python3 .tmp/rd5/setup.py --golean-source "$PWD" \
  --seeds /home/mike/projects/golean-logic/.claude/worktrees/develop/packages/golean-iris/.lake/packages \
  --copy-cache
```

The frozen setup script refuses mismatched/dirty cache sources and creates
independent clones. Keep the other dependency pins unchanged. Save the guarded
wrapper above, append these targets to the scratch `lakefile.toml`:

```toml
[[lean_lib]]
name = "CompositionAdapters"
[[lean_lib]]
name = "CompositionAcceptance"
```

Then, in `.tmp/rd5`:

```sh
LEAN_NUM_THREADS=2 capped lake build RelationalCodeX CompositionAdapters CompositionAcceptance
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose \
  GoLean RelationalCodeX GoLeanIris GoLeanIrisExamples CompositionAdapters CompositionAcceptance
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose Iris Batteries Qq
```

Check replay names and multiplicities against all GoLean source modules
(including root `GoLean.lean`), all 68 frozen local source modules (including
the aggregate), and the two harness modules. Check third-party names against
the built `.olean` files in the private caches. This is the built dependency
closure, not every unbuilt library source or the toolchain itself.

Upstream validation, from the implementation checkout:

```sh
LEAN_NUM_THREADS=2 capped scripts/ci --diff
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean
```

The standing core audit and headline prints are part of CI. Compare the replay
set to the source set; discard scratch/cache/log/corpus artifacts after checking.

## Validation at source freeze

All four exact adapters pass the GoLean-only check (53 jobs), standard trio
only. Changed upstream modules and contract/core-audit modules build warning-free
(72 jobs). The full unchanged downstream package rebuilds at its baseline
(325 jobs, 5,752 local declarations with standard axioms), still with the A–D
law parameters. That baseline build is not unconditional Alias acceptance.
The pre-existing Memory.lean unused-variable warning remains visible.

Direct kernel replay passes the exact source set of 86 GoLean modules and
the exact built dependency set of 206 modules (174 Iris, 18 Batteries, 14 Qq),
with no omissions or duplicates. This branch's CI predates the newer main-branch
replay wrapper; these are explicit separate checker runs.

Full `scripts/ci --diff` passes (579 seconds): 3,989 differential cases
(3,749 PASS, 240 tracked FAIL) and 405 negative cases, no baseline regression;
396 interpreter checks pass. It certified the frozen working-tree source that
is committed below, not yet a clean commit metadata record. One speedbump was
RED: `check-mem-callsites` needed the new `OrderedWrites.storeLoc` mention
inventoried. This is a Prop-level effect premise, not an executable raw access.
The inventory now records that reason; its targeted rerun passes all 86 rows.
No other speedbump was red. No semantic source changed after the CI run.

Candidate-pinned guarded acceptance and final independent candidate confirmation
are in progress. The immutable pin and final evidence will be recorded below;
no Add completion claim follows from this batch.
