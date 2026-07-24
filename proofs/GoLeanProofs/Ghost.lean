import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.HeapBridge

/-!
# The GoCore ghost state
`GoCoreGS` (gen_heap + the pinned program), the state interpretation
(heap ∗ ⌜functions = prog ∧ HeapWf⌝), and the `IrisGS` instance.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

section
/-- The GoCore ghost state: invariant+credit cameras plus gen_heap over the
base-address heap, and the **fixed program** `prog` the state interpretation
pins `σ.functions` to (functions are Step-invariant; pinning them is what
lets `wp_call` take a pure `findFunctionIn? prog … = some func` premise
instead of an unsatisfiable `∀σ` one — `docs/2026-07-20_call-law-design.md`).
WP laws *assume* it, exactly as HeapLang's laws assume `[HeapLangGS]`;
constructing it is adequacy's job. -/
class GoCoreGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends
    InvGS_gen hlc GF where
  heap : genHeapGS Nat HeapCell GF GoHeapF
  prog : Array Func
  /-- The fixed method table, pinned like `prog` (R3: the machine's
  frame-entry step consults `σ.methods` for dynamic dispatch, so call laws
  need it pinned — it is `Step`-invariant for the same reason functions
  are: no rule writes it). -/
  methods : Array MethodInfo
attribute [reducible, instance] GoCoreGS.heap

variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- State interpretation: gen_heap over the projected heap, plus the two pure
step-invariants — `σ.functions` pinned to the fixed program and heap
well-formedness (`docs/2026-07-20_call-law-design.md`). -/
instance : StateInterp ExecState Unit GF where
  stateInterp σ _ _ _ :=
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ.heap)
      ∗ ⌜σ.functions = GoCoreGS.prog GF ∧ σ.methods = GoCoreGS.methods GF
          ∧ HeapWf σ⌝)

instance : IrisGS_gen hlc Config GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

end

end GoLean.Iris
