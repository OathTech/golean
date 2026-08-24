import GoLean.GoCore.StepFn
import GoLeanProofs.Frame.Values

/-!
# FastEval — static-table congruence for the ctx refactor
(campaign Arc 2, unit P2R slice 3)

Function-level congruence lemmas for every pure helper the fast
evaluator calls at a state image: each helper reads ONLY the static
tables (`types`, and for dispatch `functions`/`methods`/`methodSets`),
never the heap — so it computes identically at any two states agreeing
on those tables. Consumed by the `ctxF` flip in the FastEval modules:
the def-side call sites move from `γF σF` (whose COMPILED construction
materializes the O(cells) heap dump per call — the P2R strictness
discovery, log slice 2) to the O(1) `ctxF σF`, and the sims rewrite by
these lemmas back to the `γF` spelling, leaving the existing proof
scripts untouched.

Builds on the Frame library's congruence layer
(`Frame/TypeCongr.lean`, `Frame/Values.lean`: `defaultValue_congr`,
`resolveDefinedAliases_congr`, `canonicalTy_congr`,
`tyUncomparable_congr`, `goTypeNameForMessage_congr`, the method
family). Stated FUNCTION-LEVEL (`helper σ' = helper σ`) so a single
`rw`/`simp only` rewrites every occurrence, including under binders.
UNTRUSTED METHOD — never in any statement closure.
LINEAGE: context/state splitting in data refinement.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame

set_option maxHeartbeats 1000000

variable {σ' σ : ExecState}

section Types

variable (htypes : σ'.types = σ.types)
include htypes

theorem structTagCompatible_congr :
    structTagCompatible σ' = structTagCompatible σ := by
  funext actual expected
  simp only [structTagCompatible, htypes]

theorem normalizeValueForTyFuel_congr :
    ∀ fuel : Nat, normalizeValueForTyFuel fuel σ' = normalizeValueForTyFuel fuel σ := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ n ih =>
      funext ty v
      cases ty <;> cases v <;>
        simp only [normalizeValueForTyFuel, htypes, ih]

theorem normalizeValueForTy_congr :
    normalizeValueForTy σ' = normalizeValueForTy σ := by
  funext ty v
  rw [normalizeValueForTy, normalizeValueForTy, normalizeValueForTyFuel_congr htypes]

theorem valueEqFuel_congr :
    ∀ fuel : Nat, valueEqFuel fuel σ' = valueEqFuel fuel σ := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ n ih =>
      funext ty l r
      cases ty <;>
        first
          | rfl
          | simp only [valueEqFuel, htypes, ih,
              tyUncomparable_congr htypes, goTypeNameForMessage_congr htypes]
          | (cases l <;> cases r <;>
              first
                | rfl
                | simp only [valueEqFuel, htypes, ih,
                    tyUncomparable_congr htypes, goTypeNameForMessage_congr htypes])

theorem valueEq_congr : valueEq σ' = valueEq σ := by
  funext ty l r
  rw [valueEq, valueEq, valueEqFuel_congr htypes]

theorem valueHashability_congr :
    ∀ v, valueHashability σ' v = valueHashability σ v := by
  intro v
  induction v using valueHashability.induct
    (state := σ')
    (motive_2 := fun vs => valueHashabilityList σ' vs = valueHashabilityList σ vs)
    (motive_3 := fun fs => valueHashabilityFields σ' fs = valueHashabilityFields σ fs) with
  | _ =>
    simp_all [valueHashability, valueHashabilityList, valueHashabilityFields,
      ← tyUncomparable_congr htypes, goTypeNameForMessage_congr htypes]

theorem checkKeyHashable_congr :
    checkKeyHashable σ' = checkKeyHashable σ := by
  funext key isInsert nonEmpty
  rw [checkKeyHashable, checkKeyHashable, valueHashability_congr htypes]

theorem mapEntryIndex?_congr :
    ∀ (keyTy : Ty) (entries : Array (GoValue × GoValue)) (key : GoValue)
      (isInsert : Bool),
      mapEntryIndex? σ' keyTy entries key isInsert
        = mapEntryIndex? σ keyTy entries key isInsert := by
  intro keyTy entries key isInsert
  unfold mapEntryIndex?
  rw [checkKeyHashable_congr htypes, valueEq_congr htypes]

theorem convertValueToTyFuel_congr :
    ∀ fuel : Nat, convertValueToTyFuel fuel σ' = convertValueToTyFuel fuel σ := by
  intro fuel
  induction fuel with
  | zero =>
      funext ty v
      cases ty <;> cases v <;>
        first
          | rfl
          | simp only [convertValueToTyFuel, htypes]
          | (rename_i inner _; cases inner <;>
              first | rfl | simp only [convertValueToTyFuel, htypes])
  | succ n ih =>
      funext ty v
      cases ty <;> cases v <;>
        first
          | rfl
          | simp only [convertValueToTyFuel, htypes, ih]
          | (rename_i inner _; cases inner <;>
              first | rfl | simp only [convertValueToTyFuel, htypes, ih])

theorem convertValueToTy_congr :
    convertValueToTy σ' = convertValueToTy σ := by
  funext ty v
  rw [convertValueToTy, convertValueToTy, convertValueToTyFuel_congr htypes]

end Types

section Tables

variable (htypes : σ'.types = σ.types) (hmethods : σ'.methods = σ.methods)
  (hfuncs : σ'.functions = σ.functions) (hmsets : σ'.methodSets = σ.methodSets)
include htypes hmethods hfuncs hmsets

theorem typeAssertValue_congr :
    typeAssertValue σ' = typeAssertValue σ := by
  funext v targetTy
  unfold typeAssertValue
  simp only [defaultValue_congr htypes, resolveDefinedAliases_congr htypes,
    canonicalTy_congr htypes,
    dynamicImplementsInterface_congr htypes hmethods hfuncs hmsets]

end Tables

section Types2

variable (htypes : σ'.types = σ.types)
include htypes

theorem buildStructFields_congr :
    buildStructFields σ' = buildStructFields σ := by
  funext fields args
  induction fields generalizing args with
  | nil => cases args <;> rfl
  | cons f rest ih =>
      cases args with
      | nil => rfl
      | cons v vs =>
          simp only [buildStructFields, normalizeValueForTy_congr htypes, ih]

theorem buildStructValueFuel_congr :
    ∀ fuel : Nat, buildStructValueFuel fuel σ' = buildStructValueFuel fuel σ := by
  intro fuel
  induction fuel with
  | zero =>
      funext ty args
      cases ty <;> first | rfl | simp only [buildStructValueFuel, htypes]
  | succ n ih =>
      funext ty args
      cases ty <;>
        first
          | rfl
          | simp only [buildStructValueFuel, htypes, ih,
              buildStructFields_congr htypes]

theorem buildStructValue_congr :
    buildStructValue σ' = buildStructValue σ := by
  funext ty args
  rw [buildStructValue, buildStructValue, buildStructValueFuel_congr htypes]

theorem buildArrayValue_congr :
    buildArrayValue σ' = buildArrayValue σ := by
  funext length elem args
  unfold buildArrayValue
  rw [defaultValue_congr htypes, normalizeValueForTy_congr htypes]

theorem buildDefaultArrayValue_congr :
    buildDefaultArrayValue σ' = buildDefaultArrayValue σ := by
  funext length elem
  rw [buildDefaultArrayValue, buildDefaultArrayValue, buildArrayValue_congr htypes]

theorem buildAppendBackingValue_congr :
    buildAppendBackingValue σ' = buildAppendBackingValue σ := by
  funext elem oldValues elemValues newCap
  unfold buildAppendBackingValue
  rw [defaultValue_congr htypes, normalizeValueForTy_congr htypes]

theorem keyInKeyList_congr :
    keyInKeyList σ' = keyInKeyList σ := by
  funext keyTy key l
  induction l with
  | nil => rfl
  | cons p rest ih =>
      simp only [keyInKeyList, valueEq_congr htypes, ih]

theorem keyInKeys_congr :
    keyInKeys σ' = keyInKeys σ := by
  funext keyTy keys key
  rw [keyInKeys, keyInKeys, keyInKeyList_congr htypes]

theorem filterCandidateList_congr :
    filterCandidateList σ' = filterCandidateList σ := by
  funext keyTy produced l
  induction l with
  | nil => rfl
  | cons kv rest ih =>
      cases kv
      simp only [filterCandidateList, keyInKeys_congr htypes, ih]

theorem mandatoryInList_congr :
    mandatoryInList σ' = mandatoryInList σ := by
  funext keyTy start l
  induction l with
  | nil => rfl
  | cons kv rest ih =>
      cases kv
      simp only [mandatoryInList, keyInKeys_congr htypes, ih]

theorem mapIterMandatoryRemains_congr :
    mapIterMandatoryRemains σ' = mapIterMandatoryRemains σ := by
  funext keyTy candidates start
  rw [mapIterMandatoryRemains, mapIterMandatoryRemains, mandatoryInList_congr htypes]

end Types2

end GoLean.FastEval
