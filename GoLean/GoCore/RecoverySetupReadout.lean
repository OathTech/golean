import GoLean.GoCore.RecoverySetupWf

/-! Pointwise and complete actual readout of canonical entry storage. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem initialState_argument (p : Program) (f : Func) (args results : List GoValue)
    (hlen : args.length = f.args.size) (i : Nat) (hi : i < args.length) :
    loadLoc (initialState p f args results) (.base ⟨i⟩) = .ok args[i] := by
  have hleft : i < (parameterCells f.args.toList args).length := by
    simpa [parameterCells, hlen] using hi
  have hcell : (parameterCells f.args.toList args ++
      parameterCells f.results.toList results)[i]? =
      some (.value f.args[i].typ args[i]) := by
    rw [List.getElem?_append_left hleft]
    simp [parameterCells, List.getElem?_zipWith, List.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem (xs := f.args) (i := i) (by omega)]
  simp [loadLoc, Heap.lookup, initialState, hcell]

theorem initialState_result (p : Program) (f : Func) (args results : List GoValue)
    (ha : args.length = f.args.size) (hr : results.length = f.results.size)
    (i : Nat) (hi : i < results.length) :
    loadLoc (initialState p f args results) (.base ⟨f.args.size + i⟩) =
      .ok results[i] := by
  have hsize : (parameterCells f.args.toList args).length = f.args.size := by
    simp [parameterCells, ha]
  have hcell : (parameterCells f.args.toList args ++
      parameterCells f.results.toList results)[f.args.size + i]? =
      some (.value f.results[i].typ results[i]) := by
    rw [List.getElem?_append_right (by omega), hsize]
    simp [parameterCells, List.getElem?_zipWith, List.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem (xs := f.results) (i := i) (by omega)]
  simp [loadLoc, Heap.lookup, initialState, hcell]

theorem loadMany_of_lookup (vs : List GoValue) (s : ExecState) (root : Nat → Loc)
    (h : ∀ i (hi : i < vs.length), loadLoc s (root i) = .ok vs[i]) :
    loadMany s ((List.range vs.length).map root) = .ok vs := by
  induction vs generalizing root with
  | nil => rfl
  | cons v vs ih =>
    have hh := h 0 (by simp)
    have hr := ih (fun i => root (i + 1)) (by
      intro i hi
      exact h (i + 1) (by simpa using Nat.succ_lt_succ hi))
    simp [List.range_succ_eq_map, List.map_map, Function.comp_def,
      loadMany, hh, hr, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem initialState_readout (p : Program) (f : Func) (args results : List GoValue)
    (ha : args.length = f.args.size) (hr : results.length = f.results.size) :
    loadMany (initialState p f args results) (BooleanRuntime.initialResults f) =
      .ok results := by
  simpa [BooleanRuntime.initialResults, hr] using
    loadMany_of_lookup results (initialState p f args results)
      (fun i => .base ⟨f.args.size + i⟩)
      (initialState_result p f args results ha hr)

end GoLean.GoCore.RecoveryRuntime
