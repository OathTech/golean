# U1 restricted sequentialization experiment

This package imports the public `GoLean.Relational` facade. `U1.Symbolic`
instantiates the general theorem on actual source expressions over arbitrary
stores and values: `sum = x + y`, `copy = x`, `less = sum < copy`. Its source
premises are typed value cells at the two input roots. It proves the actual
entry checks, fresh binder allocation, expression laws over all intermediate
heaps, all-schedule safety and canonical realization. No Iris is imported.

`U1.Controls` checks aliased write/read order, observable print order with no
heap effect, and different fresh addresses at unequal allocator bounds.
`U1.Audit` checks every declaration in this import closure, including generated
declarations, and prints the headline axiom dependencies. Its axiom result and
its implementation scan are distinct: the inherited implementation scan
reports **FAIL: 16 unwaived findings**. See the root U1 stage and I1 dispositions.

From this directory, after building the root facade:

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env lean U1/Audit.lean
LEAN_NUM_THREADS=2 capped lake env lean --run AliasControl.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose U1
LEAN_NUM_THREADS=2 capped lake env leanchecker --fresh --verbose U1.Audit
```

The normal replay checks each experiment module against its imports; the fresh
replay additionally replays the audit's entire import closure. Root CI performs
its own exact GoLean-module replay. No compiler replacement or native decision
procedure substitutes for these kernel checks.

The separate `../2026-10-15-unseq-rd8` adapter discharges the frozen RD8
SimulationLaw and original guarded target by interpreting the shared U1
traversal. The general result here remains primary. `AliasControl.lean` runs a
fresh unordered invocation/write versus aliased read through the real pool
explorer and verified behavior-set certificate checker, retaining {-2, 7}.
This negative control's enumeration is not the general proof. No arbitrary
observation/interference stability or live downstream integration is claimed.
