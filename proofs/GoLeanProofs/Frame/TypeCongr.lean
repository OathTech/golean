import GoLeanProofs.Frame.Sim

/-!
# The executable frame theorem, module 3: static-table congruence

Every machine helper that reads ONLY the static tables
(types/functions/methods/methodSets) computes identically in the
canonical and framed states — `FrameSim` keeps those tables EQUAL, so
these are plain congruence lemmas, no renaming involved. They are the
reason type resolution, method dispatch metadata, interface
satisfaction, and message rendering agree across the two runs.

Stated with the four table-equality hypotheses directly (not against
`FrameSim`) so they compose freely; each is simp-orientable
`f σF x = f σ x`.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {σ σF : ExecState}

section Types

variable (htypes : σF.types = σ.types)
include htypes

theorem resolveDefinedAliasesFuel_congr :
    ∀ (fuel : Nat) (ty : Ty),
      resolveDefinedAliasesFuel fuel σF ty = resolveDefinedAliasesFuel fuel σ ty := by
  intro fuel
  induction fuel with
  | zero => intro ty; cases ty <;> rfl
  | succ n ih =>
      intro ty
      cases ty <;> simp [resolveDefinedAliasesFuel, ih, htypes]

theorem resolveDefinedAliases_congr (ty : Ty) :
    resolveDefinedAliases σF ty = resolveDefinedAliases σ ty :=
  resolveDefinedAliasesFuel_congr htypes _ _

theorem canonicalTyFuel_congr :
    ∀ (fuel : Nat) (ty : Ty),
      canonicalTyFuel fuel σF ty = canonicalTyFuel fuel σ ty := by
  intro fuel
  induction fuel with
  | zero => intro ty; cases ty <;> rfl
  | succ n ih =>
      intro ty
      cases ty <;> simp [canonicalTyFuel, ih, htypes]

theorem canonicalTy_congr (ty : Ty) :
    canonicalTy σF ty = canonicalTy σ ty :=
  canonicalTyFuel_congr htypes _ _

theorem canonicalDynamicTy_congr (ty : Ty) :
    canonicalDynamicTy σF ty = canonicalDynamicTy σ ty := by
  simp [canonicalDynamicTy, canonicalTy_congr htypes]

theorem tyUncomparableFuel_congr :
    ∀ (fuel : Nat) (ty : Ty),
      tyUncomparableFuel fuel σF ty = tyUncomparableFuel fuel σ ty := by
  intro fuel
  induction fuel with
  | zero => intro ty; cases ty <;> rfl
  | succ n ih =>
      intro ty
      cases ty <;> simp [tyUncomparableFuel, ih, htypes]

theorem tyUncomparable_congr (ty : Ty) :
    tyUncomparable σF ty = tyUncomparable σ ty :=
  tyUncomparableFuel_congr htypes _ _

theorem goTypeNameForMessageFuel_congr :
    ∀ (fuel : Nat) (ty : Ty),
      goTypeNameForMessageFuel fuel σF ty = goTypeNameForMessageFuel fuel σ ty := by
  intro fuel
  induction fuel with
  | zero => intro ty; rfl
  | succ n ih =>
      intro ty
      simp only [goTypeNameForMessageFuel, resolveDefinedAliases_congr htypes]
      cases hres : resolveDefinedAliases σ ty with
      | chan dir e => cases dir <;> simp [ih]
      | funcType params results =>
          have hmap : List.map (goTypeNameForMessageFuel n σF) params
              = List.map (goTypeNameForMessageFuel n σ) params :=
            List.map_congr_left (fun t _ => ih t)
          cases results with
          | nil => simp [hmap]
          | cons r rs =>
              have hmap' : List.map (goTypeNameForMessageFuel n σF) (r :: rs)
                  = List.map (goTypeNameForMessageFuel n σ) (r :: rs) :=
                List.map_congr_left (fun t _ => ih t)
              cases rs <;> simp [ih, hmap, hmap']
      | _ => simp [ih]

theorem goTypeNameForMessage_congr (ty : Ty) :
    goTypeNameForMessage σF ty = goTypeNameForMessage σ ty :=
  goTypeNameForMessageFuel_congr htypes _ _

theorem dynamicTypeName?_congr (ty : Ty) :
    dynamicTypeName? σF ty = dynamicTypeName? σ ty := by
  simp only [dynamicTypeName?, resolveDefinedAliases_congr htypes]

theorem interfaceDeclaredMethods?_congr (id : TypeId) :
    interfaceDeclaredMethods? σF id = interfaceDeclaredMethods? σ id := by
  simp [interfaceDeclaredMethods?, htypes]

theorem methodCarrierKey?_congr (ty : Ty) :
    methodCarrierKey? σF ty = methodCarrierKey? σ ty := by
  simp only [methodCarrierKey?, resolveDefinedAliases_congr htypes]

end Types

section Tables

theorem methodInfoByFuncId?_congr (hmethods : σF.methods = σ.methods)
    (id : FuncId) :
    methodInfoByFuncId? σF id = methodInfoByFuncId? σ id := by
  simp [methodInfoByFuncId?, hmethods]

theorem methodRecvInterfaceName?_congr (htypes : σF.types = σ.types)
    (m : MethodInfo) :
    methodRecvInterfaceName? σF m = methodRecvInterfaceName? σ m := by
  simp only [methodRecvInterfaceName?, resolveDefinedAliases_congr htypes]

theorem methodRecvDynamicTy?_congr (htypes : σF.types = σ.types)
    (m : MethodInfo) :
    methodRecvDynamicTy? σF m = methodRecvDynamicTy? σ m := by
  simp only [methodRecvDynamicTy?, canonicalTy_congr htypes]

theorem concreteMethodForDynamic?_congr (htypes : σF.types = σ.types)
    (hmethods : σF.methods = σ.methods) (dynTy : Ty) (name : String) :
    concreteMethodForDynamic? σF dynTy name
      = concreteMethodForDynamic? σ dynTy name := by
  simp only [concreteMethodForDynamic?, hmethods,
    methodRecvDynamicTy?_congr htypes]

theorem hasConcreteMethod_congr (htypes : σF.types = σ.types)
    (hmethods : σF.methods = σ.methods) (dynTy : Ty) (name : String) :
    hasConcreteMethod σF dynTy name = hasConcreteMethod σ dynTy name := by
  simp only [hasConcreteMethod, concreteMethodForDynamic?_congr htypes hmethods]

theorem concreteMethodSignature?_congr (htypes : σF.types = σ.types)
    (hfuncs : σF.functions = σ.functions) (m : MethodInfo) :
    concreteMethodSignature? σF m = concreteMethodSignature? σ m := by
  simp only [concreteMethodSignature?, hfuncs]
  cases findFunctionIn? σ.functions m.funcId with
  | none => rfl
  | some f => simp [canonicalTy_congr htypes]

theorem satisfiesMethodSig_congr (htypes : σF.types = σ.types)
    (hmethods : σF.methods = σ.methods)
    (hfuncs : σF.functions = σ.functions) (dynTy : Ty) (req : MethodSig) :
    satisfiesMethodSig σF dynTy req = satisfiesMethodSig σ dynTy req := by
  simp only [satisfiesMethodSig, concreteMethodForDynamic?_congr htypes hmethods]
  cases concreteMethodForDynamic? σ dynTy req.name with
  | none => rfl
  | some hit =>
      simp only [concreteMethodSignature?_congr htypes hfuncs]
      cases concreteMethodSignature? σ hit.1 with
      | none => rfl
      | some sig =>
          have hc : canonicalTy σF = canonicalTy σ :=
            funext fun t => canonicalTy_congr htypes t
          simp [hc]

theorem methodSetCoverage?_congr (hmsets : σF.methodSets = σ.methodSets)
    (key : String) :
    methodSetCoverage? σF key = methodSetCoverage? σ key := by
  simp [methodSetCoverage?, hmsets]

theorem dynamicMethodSetRecorded_congr (htypes : σF.types = σ.types)
    (hmsets : σF.methodSets = σ.methodSets) (dynTy : Ty) :
    dynamicMethodSetRecorded σF dynTy = dynamicMethodSetRecorded σ dynTy := by
  simp only [dynamicMethodSetRecorded, methodCarrierKey?_congr htypes,
    methodSetCoverage?_congr hmsets]

theorem dynamicMethodSetExportedOnly_congr (htypes : σF.types = σ.types)
    (hmsets : σF.methodSets = σ.methodSets) (dynTy : Ty) :
    dynamicMethodSetExportedOnly σF dynTy
      = dynamicMethodSetExportedOnly σ dynTy := by
  simp only [dynamicMethodSetExportedOnly, methodCarrierKey?_congr htypes,
    methodSetCoverage?_congr hmsets]

theorem firstUnsatisfiedMethod?_congr (htypes : σF.types = σ.types)
    (hmethods : σF.methods = σ.methods)
    (hfuncs : σF.functions = σ.functions)
    (hmsets : σF.methodSets = σ.methodSets) (dynTy : Ty) (iname : TypeId) :
    firstUnsatisfiedMethod? σF dynTy iname
      = firstUnsatisfiedMethod? σ dynTy iname := by
  simp only [firstUnsatisfiedMethod?, interfaceDeclaredMethods?_congr htypes,
    satisfiesMethodSig_congr htypes hmethods hfuncs,
    dynamicMethodSetRecorded_congr htypes hmsets,
    dynamicMethodSetExportedOnly_congr htypes hmsets,
    goTypeNameForMessage_congr htypes]

theorem dynamicImplementsInterface_congr (htypes : σF.types = σ.types)
    (hmethods : σF.methods = σ.methods)
    (hfuncs : σF.functions = σ.functions)
    (hmsets : σF.methodSets = σ.methodSets) (dynTy : Ty) (iname : TypeId) :
    dynamicImplementsInterface σF dynTy iname
      = dynamicImplementsInterface σ dynTy iname := by
  simp only [dynamicImplementsInterface,
    firstUnsatisfiedMethod?_congr htypes hmethods hfuncs hmsets]

end Tables

end GoLean.Frame
