import GoLean.GoCore.Correspondence
import GoLeanProofs.Specs.Slice

/-!
# The slice correspondence witness (non-vacuity discharge for item 6)

Instantiates the interpreter⇄relation correspondence on THE slice program —
the same `sliceProg`/`incFunc`/`mainFunc` terms `slice_adequate` speaks
about. This is the closed witness that the fragment conditions
(`StInv`/`FuncFrag`/`SpineFrag`) are satisfiable *by the real proof subject*,
per the non-vacuity gate: it exhibits a concrete interpreter run
(kernel-computed, `r = 2` in the final heap) and its `Steps` derivation in
the relation — the run the differential validates is an execution of the
semantics the Iris proofs govern.

Iris-free on purpose: everything here is about the core-side correspondence;
it lives in the proofs package only because the slice program terms do.
-/

namespace GoLean.Iris.SliceCorrespondence

open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.GoCore.Correspondence

abbrev mainId : FuncId := ⟨"main"⟩
abbrev incId : FuncId := ⟨"inc"⟩

/-- The slice's closed initial state: just the two functions. -/
abbrev σ₀ : ExecState :=
  { functions := #[mainFunc mainId incId .int, incFunc incId .int (.int .int) 1] }

/-- `inc` is a fragment function (void, bare non-spine body). -/
theorem incFunc_frag : FuncFrag (incFunc incId .int (.int .int) 1) where
  argsTy := by
    intro p hp
    simp at hp
    subst hp
    exact .pointer _
  resultsTy := by intro r hr; simp at hr
  body := by
    right
    refine ⟨?_, rfl⟩
    exact .assign (.addr (.var "p")) (.add (.deref _ (.var "p")) (.intLit 1 .int))

/-- `main` is a fragment function (`.seqn` spine body ending in `return`;
no block shadows the result name — there are no blocks). -/
theorem mainFunc_frag : FuncFrag (mainFunc mainId incId .int) where
  argsTy := by intro p hp; simp at hp
  resultsTy := by
    intro r hr
    simp at hr
    subst hr
    exact .int _
  body := by
    left
    refine ⟨_, rfl, ?_, fun _ => ?_⟩
    · intro s hs
      simp at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact .init (.int _) (by simp)
      · exact .ns (.call (by intro a ha; simp at ha)
          (by intro e he; simp at he; subst he; exact .ref _))
      · exact .ns (.assign (.var _) (.var _))
      · exact .ns .returnStmt
    · exact .cons _ (.cons _ (.cons _ (.cons _ .single)))

/-- The initial state satisfies the program invariant. -/
theorem σ₀_inv : StInv σ₀ where
  heap := by intro loc cell h; simp [Heap.lookup] at h
  methods := rfl
  funcs := by
    intro f hf
    simp at hf
    rcases hf with rfl | rfl
    · exact mainFunc_frag
    · exact incFunc_frag

/-- The slice program's elements are spine fragments (no avoided names). -/
theorem sliceProg_spine :
    ∀ s ∈ (#[Stmt.initialization ⟨"r", .int .int⟩,
        Stmt.call #[.var "r"] mainId #[]] : Array Stmt).toList,
      SpineFrag [] s := by
  intro s hs
  simp at hs
  rcases hs with rfl | rfl
  · exact .init (.int _) (by simp)
  · exact .ns (.call
      (by intro a ha; simp at ha; subst ha; exact .var _)
      (by intro e he; simp at he))

/-- **The witness.** Every fragment hypothesis of the correspondence is
discharged for THE slice program (`StInv σ₀`, both `FuncFrag`s, the spine
shape): any normal interpreter run of `sliceProg` from `σ₀` IS a `Steps`
derivation of the relation, landing at the interpreter's final state up to
the bookkeeping `locals` field.

The run itself enters as a hypothesis by design: the totalized interpreter is
compiled by well-founded recursion, which does not reduce definitionally, so
the kernel cannot execute it inside a proof — and running it is the
*executable* world's job anyway. That world discharges it: the eval tests and
the differential corpus case `pointers/inc-via-call` (real Go oracle) execute
exactly this program shape and observe `r = 2`. -/
theorem slice_interp_run_in_relation (fuel : Nat) (σf : ExecState)
    (ch' : Choices)
    (hrun : execStmt fuel σ₀ [] (sliceProg mainId .int)
      = .ok (.normal σf, ch')) :
    Steps (.exec (sliceProg mainId .int) [] .stop) σ₀
      (.next .stop) (σf.withLocals []) :=
  interpreterSound_spineSeq fuel σ₀ σf _ [] ch' sliceProg_spine σ₀_inv hrun

end GoLean.Iris.SliceCorrespondence
