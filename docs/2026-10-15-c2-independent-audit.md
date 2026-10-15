# Independent C2 implementation review

Reviewed 2026-10-15 against the C2 charter, the actual sequential driver and
the local execution, entry, setup, readback and successful-program dependencies.
The review brief supplied goals and source locations; investigation was unrestricted.
No production or peer worktree edits. Reviewed immutable implementation:
`fcebf85ccabd4caae101ac656b3ae149caf02f70`. The reviewer compared all seven
committed source/configuration blobs with the independently compiled hashes:
zero mismatches. This review covers the initial upstream implementation;
the subsequently relayed RD6 consumer batch has a separate implementation
and review.

## Verdict

No concrete semantic or proof defect found in this implementation. The new
coverage and realization theorems are closed and unrestricted over program,
arguments, budget and selected tape. The semantic carriers contain neither a
driver invocation nor an existential tape making a driver fail. Existing
operation contracts are used at setup and readback boundaries.

The phase constructors enforce lookup, arity, type prefix, empty-store seeding,
the actual seeded-state check, initializer shape/execution, parameter binding,
result allocation/pinning, main execution and readback in the driver's order.
The impossible seeded-validity failure is represented at its real position and
discharged using the existing seeding theorem; no extra admission hypothesis is
introduced. Both local segments receive the full supplied fuel independently.
Initialization guards, including print refusal with zero remaining fuel, come
from C1's local relation. Malformed initializer errors remain unwrapped;
execution errors receive exactly the actual diagnostic wrapping.

Histories retain successful labels, endpoint states, local outcomes and finishing
selection records. Correspondence threads initialization's residual choices into
the body and realizes any prescribed final suffix. The suffix and error
endpoints are semantic witnesses, not falsely presented as driver return fields.
The success projection has the actual empty output field. Refusal and fatal
transfer premises quantify over all relational alternatives and budgets;
selected success is not confused with either exclusion. `normal_iff` is
behavior-set compatibility, not a stronger identity of supplied histories.

## Remaining acceptance obligations and limits

1. The exact downstream `closed_program_init_outcomes` constraint has not been
   relayed or checked here. This blocks a claim of completed C2 consumer
   acceptance, not the checked upstream correspondence checkpoint. The eventual
   consumer use must retain its original premises, observers and histories.
2. Readback coverage includes the failure branch after a normal body. The generic
   facade composition test checks this branch, and the concrete failing-readback
   control is explicitly an arbitrary-state component example. It does not
   establish reachability of a readback error from whole-program activation.
   The interface documentation states this limitation accurately; no concrete
   whole-program readback-failure example was independently established.
3. This review does not independently rerun full differential CI or downstream
   Iris/RD5 acceptance. Those require separately attributed author evidence.
   No concurrency, infinite-run or complete observed-adequacy result follows.

## Independent checks

- Recompiled the two new production modules, facade and facade client into
  reviewer-local oleans, with the remaining built dependencies linked read-only.
- Exact toolchain `leanchecker` replay passed for those four rebuilt modules.
- All printed headline axioms were among `propext`, `Classical.choice`,
  `Quot.sound`. A separate exhaustive sweep checked all **281 declarations**
  belonging to those four modules: standard axioms only.
- Independently compiled the retained experimental exact-obligation client.
- Independently compiled and replayed additional controls: global seeding failure
  precedes malformed initialization; result-allocation failure precedes body
  failure even with zero fuel; a successful printing body still returns empty
  `Readout.output`; generic semantic success inversion retains setup, normal
  body and fallible readback premises.
- No new `sorry`, project axiom, unsafe/extern/implemented-by escape, native
  decision or kernel-check bypass appears in the reviewed production sources.
- The first reviewer-only build attempt failed because Lean resolves a namespace
  from one search root; linking dependencies into the isolated root corrected
  that setup error. Initial scratch controls needed layout/recursion settings;
  the final controls compiled and replayed. These were review setup failures,
  not production failures.

Reproduce the maintained public checks after building this source state:

```sh
LEAN_NUM_THREADS=2 capped lake build GoLean.Relational Tests.RelationalProgramOutcomes
LEAN_NUM_THREADS=2 capped lake env lean Tests/RelationalProgramOutcomes.lean
LEAN_NUM_THREADS=2 capped lake env lean experiments/2026-10-15-program-outcomes/ProgramOutcomeConstraint.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker \
  GoLean.GoCore.RelationalProgramOutcome \
  GoLean.GoCore.RelationalProgramOutcomeSound \
  GoLean.Relational Tests.RelationalProgramOutcomes
```

For the independent rebuild, `.tmp/c2-implementation-review/olean` held separate
outputs for the four modules and read-only symlinks for dependencies. Inside
`capped lake env bash`, prepend that root to `LEAN_PATH`, then use `lean -o`
for those four source files in the order shown above and run `leanchecker`
with the same path. The extra controls and exhaustive axiom script are in the
same disposable review scratch; remove it after retaining this conclusion.

## Additional independent controls

Save the following in disposable `.tmp/C2Controls.lean`, then run
`LEAN_NUM_THREADS=2 capped lake env lean -o .tmp/C2Controls.olean .tmp/C2Controls.lean`
and replay `C2Controls` with `.tmp` prepended to `LEAN_PATH`:

```lean
import GoLean.Relational
set_option maxRecDepth 10000
open GoLean GoCore Relational ProgramExecution Machine
namespace C2Independent
def f : Func := { id := ⟨"main"⟩, args := #[], results := #[], body := .seqn #[] }
def badGlobals : Program := { funcs := #[f, { f with id := pkgInitFuncId, results := #[⟨0, .bool⟩] }], globals := #[⟨"g", .unsupported "review global"⟩] }
example (fuel : Nat) (ch : Choices) : runProgramM fuel badGlobals "main" #[] ch =
    .error (.unsupported "default value for review global") := rfl

def badResult : Program := { funcs := #[{ f with results := #[⟨0, .unsupported "review result"⟩], body := .unsupported "review body" }] }
example (fuel : Nat) (ch : Choices) : runProgramM fuel badResult "main" #[] ch =
    .error (.unsupported "default value for review result") := rfl

-- Successful output-bearing body labels do not change the actual Readout projection.
def printBody : Program := { funcs := #[{ f with body := .print false #[.boolLit true] }] }
example (ch : Choices) : runProgramM 10 printBody "main" #[] ch =
    .ok { values := #[], output := GoString.empty } := rfl

-- Generic consumer inversion retains the normal-body/readback boundary,
-- rather than replacing readback by a logical safety assumption.
theorem successful_body {program name args fuel history values}
    (h : Execution program name args fuel history (.ok values)) :
    ∃ init ready seg, history = ⟨init, some seg⟩ ∧
      Setup program name args fuel init (.ok ready) ∧
      seg.Runs .main ⟨program⟩ fuel ∧ seg.outcome = .boundary .normal ∧
      Readback ⟨program⟩ seg.finish.store ready.activation.results (.ok values) := by
  cases h with
  | normal hs _ run normal read => exact ⟨_, _, _, rfl, hs, run, normal, read⟩
#print axioms successful_body
end C2Independent
```

## Disposition

No concrete implementation defect was found or waived. Final downstream
consumer acceptance remains pending the exact relayed constraint. The concrete
readback control remains component-only; neither reachability nor impossibility
of a whole-program readback failure is asserted. These limits remain visible in
[the stage record](2026-10-15_relational-program-outcomes.md).
