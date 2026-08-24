import GoLeanProofs.FastEval.Shared

/-!
# FastEval — the store/statement-op tower, mirrored (campaign Arc 2,
U4 wave, worker B)

Mirrors + ONE-DIRECTIONAL sims (`…F .ok ⟹ original .ok` at `γF`) for
`indexTargetLoc`, `resolveChain`, `storeTarget`, `applyRhsOp`,
`mapAssignValue`, `applyStmtOpCore`, `applyStmtOp`,
`contAfterStmtOp`. Arm selection is probe D's exercised-arm census
(`docs/campaign-arc2-probes/records/probeD-armcensus.out`): the
census-exercised statement ops are newValue, makeSlice, makeMap,
mapAssign, appendSlice, sortSlice, copySlice; `makeChan`, `mapDelete`,
`clearMap`, `clearSlice` are FAIL-CLOSED STUBS with vacuous sim cases
(the one-directional refinement, design note §2a).

UNTRUSTED METHOD — no name from this file may appear in any headline
statement's closure (the design note's §3.1 accelerator position).
Template + elaboration-wrinkle register: `docs/campaign-arc2-log.md`.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## Mirrors -/

/-- `resolveChain`, fast (structural on the step list, like the
original). -/
def resolveChainF (σF : ExecStateF) : GoValue → List TargetStep → List GoValue →
    Except GoError GoValue
  | cur, [], [] => return cur
  | cur, .index :: steps, i :: idxs => do
      resolveChainF σF (.addr (← indexTargetLocF σF cur i)) steps idxs
  | cur, .field tid f :: steps, idxs => do
      resolveChainF σF (.addr (.field (← valueAsLoc cur) tid f)) steps idxs
  | _, _, _ => stuck "malformed target chain"

/-- `mapAssignValue`, fast. -/
def mapAssignValueF (σF : ExecStateF) (keyTy valueTy : Ty)
    (baseV keyV valueV : GoValue) : Except GoError ExecStateF := do
  let map ← valueAsMap baseV
  let key ← normalizeValueForTy (ctxF σF) keyTy keyV
  let value ← normalizeValueForTy (ctxF σF) valueTy valueV
  match ← mapEntriesF σF map with
  | none => GoCore.panic "assignment to entry in nil map"
  | some (baseLoc, entries) =>
      let entries ←
        match ← mapEntryIndex? (ctxF σF) keyTy entries key (isInsert := true) with
        | some i => pure (entries.set! i (key, value))
        | none => pure (entries.push (key, value))
      storeLocF σF baseLoc (.mapData entries)

/-- `storeTarget`, fast. -/
def storeTargetF (σF : ExecStateF) (r : TargetRef) (v : GoValue) :
    Except GoError ExecStateF := do
  match r with
  | .chain anchor idxs steps =>
      storeLocF σF (← valueAsLoc (← resolveChainF σF anchor steps idxs)) v
  | .mapElem b k kt vt => mapAssignValueF σF kt vt b k v

/-- `applyRhsOp`, fast (`typeAssertValue` is pure — the lazy view
carries it). -/
def applyRhsOpF (σF : ExecStateF) : RhsOp → List GoValue → Except GoError (List GoValue)
  | .vals, vs => return vs
  | .mapLookup keyTy valueTy, [baseV, keyV] => do
      let map ← valueAsMap baseV
      let key ← normalizeValueForTy (ctxF σF) keyTy keyV
      let pair ← mapLookupValueF σF map key keyTy valueTy
      return [pair.1, .bool pair.2]
  | .typeAssert targetTy, [value] => do
      let result ← typeAssertValue (ctxF σF) value targetTy
      return [result.1, .bool result.2]
  | _, _ => stuck "malformed comma-ok source operands"

/-- `applyStmtOpCore`, fast — census-exercised arms only; the rest are
fail-closed stubs (vacuous sim cases). Fast loops are structural
`List.range'`/`toList` folds per the template's loop rule. -/
def applyStmtOpCoreF (σF : ExecStateF) (op : StmtOp) (_nt : Nat)
    (vs : List GoValue) : Except GoError ExecStateF := do
  match op with
  | .newValue typ =>
      match vs with
      | [tv, value] => do
          let loc ← valueAsLoc tv
          let (nloc, σ₁) := allocF σF value typ
          storeLocF σ₁ loc (.addr nloc)
      | _ => stuck "malformed newValue operands"
  | .makeSlice elem hasCap => do
      let (tv, lenV, capV?) ←
        match vs, hasCap with
        | [tv, lenV], false => pure (tv, lenV, none)
        | [tv, lenV, capV], true => pure (tv, lenV, some capV)
        | _, _ => stuck "malformed makeSlice operands"
      let lenValue ← valueAsInt lenV
      let capValue ←
        match capV? with
        | none => pure lenValue
        | some capV => valueAsInt capV
      let len ← natFromNonnegativeInt "runtime error: makeslice: len out of range" lenValue
      let cap ← natFromNonnegativeInt "runtime error: makeslice: cap out of range" capValue
      if cap < len then
        GoCore.panic "runtime error: makeslice: cap out of range"
      let backing ← buildDefaultArrayValue (ctxF σF) cap elem
      let (base, σ₁) := allocF σF backing (some (.array cap elem))
      let loc ← valueAsLoc tv
      storeLocF σ₁ loc (.slice { base := some base, offset := 0, len, cap })
  | .makeMap hasSpace => do
      let (tv, spaceV?) ←
        match vs, hasSpace with
        | [tv], false => pure (tv, none)
        | [tv, spaceV], true => pure (tv, some spaceV)
        | _, _ => stuck "malformed makeMap operands"
      match spaceV? with
      | none => pure ()
      | some spaceV => do
          let size ← valueAsInt spaceV
          let _ ← natFromNonnegativeInt "makemap: size out of range" size
      let (base, σ₁) := allocF σF (.mapData #[])
      let loc ← valueAsLoc tv
      storeLocF σ₁ loc (.map { base := some base })
  | .makeChan _ => stuck "fastEval-stub: applyStmtOpCore.makeChan"
  | .mapAssign keyTy valueTy =>
      match vs with
      | [baseV, keyV, valueV] => mapAssignValueF σF keyTy valueTy baseV keyV valueV
      | _ => stuck "malformed mapAssign operands"
  | .mapDelete _ => stuck "fastEval-stub: applyStmtOpCore.mapDelete"
  | .clearMap => stuck "fastEval-stub: applyStmtOpCore.clearMap"
  | .clearSlice _ => stuck "fastEval-stub: applyStmtOpCore.clearSlice"
  | .sortSlice _ =>
      match vs with
      | [baseV] => do
          let slice ← valueAsSlice baseV
          validateSlice slice
          let loaded ← forIn (List.range' 0 slice.len 1)
              (#[] : Array (Int × IntKind)) (fun i loaded => do
            match ← loadLocF σF (← sliceIndexLoc slice (Int.ofNat i)) with
            | .int v kind => pure (ForInStep.yield (loaded.push (v, kind)))
            | other => stuck s!"sortSlice expected int element, got {repr other}")
          let sorted := (sortLe (fun a b => a.1 ≤ b.1) loaded.toList).toArray
          let current ← forIn (List.range' 0 slice.len 1) σF (fun i current => do
            match sorted[i]? with
            | some (v, kind) => do
                let c ← storeLocF current (← sliceIndexLoc slice (Int.ofNat i))
                  (.int v kind)
                pure (ForInStep.yield c)
            | none => stuck "sortSlice element count mismatch")
          return current
      | _ => stuck "malformed sortSlice operands"
  | .copySlice =>
      match vs with
      | [tv, dstV, srcV] => do
          let dstSlice ← valueAsSlice dstV
          let srcSlice ← valueAsSlice srcV
          validateSlice dstSlice
          validateSlice srcSlice
          let count := Nat.min dstSlice.len srcSlice.len
          let values ← forIn (List.range' 0 count 1) (#[] : Array GoValue)
            (fun i values => do
              let v ← loadLocF σF (← sliceIndexLoc srcSlice (Int.ofNat i))
              pure (ForInStep.yield (values.push v)))
          let (current, _) ← forIn values.toList (σF, (0 : Nat))
            (fun value st => do
              let c ← storeLocF st.1 (← sliceIndexLoc dstSlice (Int.ofNat st.2)) value
              pure (ForInStep.yield (c, st.2 + 1)))
          let tloc ← valueAsLoc tv
          storeLocF current tloc (.int (Int.ofNat count))
      | _ => stuck "malformed copySlice operands"
  | .appendSlice _ =>
      throw (.internal "applyStmtOpCore: appendSlice dispatches through applyStmtOp")

/-- `applyStmtOp`, fast — the choices-threading wrapper; only the
append arm touches the stream (`Choices` ops are pure and shared). -/
def applyStmtOpF (σF : ExecStateF) (choices : Choices) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) : Except GoError (ExecStateF × Choices) := do
  match op with
  | .appendSlice elem =>
      match vs with
      | [tv, sliceV, elemsV] => do
          let slice ← valueAsSlice sliceV
          let elems ← valueAsSlice elemsV
          validateSlice slice
          validateSlice elems
          let elemValues ← sliceVisibleValuesF σF elems
          let newLen := slice.len + elemValues.size
          let tloc ← valueAsLoc tv
          if newLen <= slice.cap then
            let (current, _) ← forIn elemValues.toList (σF, (0 : Nat))
              (fun value st => do
                match slice.base with
                | some base => do
                    let c ← storeLocF st.1
                      (.index base (Int.ofNat (slice.offset + slice.len + st.2))) value
                    pure (ForInStep.yield (c, st.2 + 1))
                | none => stuck s!"cannot append {elemValues.size} element(s) into nil slice in place")
            return ((← storeLocF current tloc (.slice { slice with len := newLen })), choices)
          else
            let oldValues ← sliceVisibleValuesF σF slice
            let width := appendSpillWidth slice.cap newLen
            let (extra, choices) := Choices.consumeAt .appendSpill width choices
            let newCap := newLen +
              ((appendGrowthCap slice.cap newLen - newLen + extra) % width)
            let backing ← buildAppendBackingValue (ctxF σF) elem oldValues elemValues newCap
            let (base, current) := allocF σF backing (some (.array newCap elem))
            return ((← storeLocF current tloc
              (.slice { base := some base, offset := 0, len := newLen, cap := newCap })), choices)
      | _ => stuck "malformed appendSlice operands"
  | op => do return ((← applyStmtOpCoreF σF op nt vs), choices)

/-- `contAfterStmtOp`, fast: the exercised statement ops all take the
catch-all identity arm; the `mapDelete`/`clearMap` prune paths are
unexercised (their ops are stubbed above) and stub here too. -/
def contAfterStmtOpF (_σF : ExecStateF) (op : StmtOp) (_vs : List GoValue)
    (k : Cont) : Except GoError Cont :=
  match op with
  | .mapDelete _ => stuck "fastEval-stub: contAfterStmtOp.mapDelete"
  | .clearMap => stuck "fastEval-stub: contAfterStmtOp.clearMap"
  | _ => return k

/-! ## Sims -/


theorem resolveChainF_ok {σF : ExecStateF} :
    ∀ {steps : List TargetStep} {cur : GoValue} {idxs : List GoValue} {v : GoValue},
    resolveChainF σF cur steps idxs = .ok v →
    resolveChain (γF σF) cur steps idxs = .ok v := by
  intro steps
  induction steps with
  | nil =>
      intro cur idxs v h
      cases idxs with
      | nil => simpa [resolveChainF, resolveChain] using h
      | cons _ _ => simp [resolveChainF] at h
  | cons step steps ih =>
      intro cur idxs v h
      cases step with
      | index =>
          cases idxs with
          | nil => simp [resolveChainF] at h
          | cons i idxs =>
              unfold resolveChainF at h
              unfold resolveChain
              cases hidx : indexTargetLocF σF cur i with
              | error e => rw [hidx] at h; simp [Bind.bind, Except.bind] at h
              | ok l =>
                  rw [hidx] at h
                  rw [indexTargetLocF_ok hidx]
                  simp only [Bind.bind, Except.bind] at h ⊢
                  exact ih h
      | field tid f =>
          unfold resolveChainF at h
          unfold resolveChain
          cases hvl : valueAsLoc cur with
          | error e => rw [hvl] at h; simp [Bind.bind, Except.bind] at h
          | ok l =>
              rw [hvl] at h
              simp only [Bind.bind, Except.bind, hvl] at h ⊢
              exact ih h

theorem mapAssignValueF_ok {σF : ExecStateF} {keyTy valueTy : Ty}
    {baseV keyV valueV : GoValue} {σF' : ExecStateF}
    (h : mapAssignValueF σF keyTy valueTy baseV keyV valueV = .ok σF') :
    mapAssignValue (γF σF) keyTy valueTy baseV keyV valueV = .ok (γF σF') := by
  unfold mapAssignValueF at h
  simp only [normalizeValueForTy_ctx, mapEntryIndex?_ctx] at h
  unfold mapAssignValue
  cases hm : valueAsMap baseV with
  | error e => rw [hm] at h; simp [Bind.bind, Except.bind] at h
  | ok map =>
      rw [hm] at h
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hk : normalizeValueForTy (γF σF) keyTy keyV with
      | error e => rw [hk] at h; simp at h
      | ok key =>
          rw [hk] at h
          cases hval : normalizeValueForTy (γF σF) valueTy valueV with
          | error e => rw [hval] at h; simp at h
          | ok value =>
              rw [hval] at h
              cases hme : mapEntriesF σF map with
              | error e => rw [hme] at h; simp at h
              | ok ents =>
                  rw [hme] at h
                  rw [mapEntriesF_ok hme]
                  cases ents with
                  | none => simp at h
                  | some p =>
                      obtain ⟨baseLoc, entries⟩ := p
                      simp only [] at h ⊢
                      cases hidx : mapEntryIndex? (γF σF) keyTy entries key
                          (isInsert := true) with
                      | error e => rw [hidx] at h; simp [Bind.bind, Except.bind] at h
                      | ok io =>
                          rw [hidx] at h
                          cases io <;>
                            · simp only [Bind.bind, Except.bind, pure,
                                Except.pure] at h ⊢
                              exact storeLocF_ok h

theorem storeTargetF_ok {σF : ExecStateF} {r : TargetRef} {v : GoValue}
    {σF' : ExecStateF} (h : storeTargetF σF r v = .ok σF') :
    storeTarget (γF σF) r v = .ok (γF σF') := by
  unfold storeTargetF at h
  unfold storeTarget
  cases r with
  | chain anchor idxs steps =>
      simp only [] at h ⊢
      cases hrc : resolveChainF σF anchor steps idxs with
      | error e => rw [hrc] at h; simp [Bind.bind, Except.bind] at h
      | ok cur =>
          rw [hrc] at h
          rw [resolveChainF_ok hrc]
          simp only [Bind.bind, Except.bind] at h ⊢
          cases hvl : valueAsLoc cur with
          | error e => rw [hvl] at h; simp at h
          | ok loc =>
              rw [hvl] at h
              exact storeLocF_ok h
  | mapElem b k kt vt => exact mapAssignValueF_ok h

theorem applyRhsOpF_ok {σF : ExecStateF} {op : RhsOp} {vs r : List GoValue}
    (h : applyRhsOpF σF op vs = .ok r) :
    applyRhsOp (γF σF) op vs = .ok r := by
  unfold applyRhsOpF at h
  simp only [normalizeValueForTy_ctx, typeAssertValue_ctx] at h
  split at h
  · simp only [applyRhsOp]
    exact h
  · rename_i keyTy valueTy baseV keyV
    cases hm : valueAsMap baseV with
    | error e => rw [hm] at h; simp [Bind.bind, Except.bind] at h
    | ok map =>
        rw [hm] at h
        simp only [Bind.bind, Except.bind] at h
        cases hk : normalizeValueForTy (γF σF) keyTy keyV with
        | error e => rw [hk] at h; simp at h
        | ok key =>
            rw [hk] at h
            simp only [Bind.bind, Except.bind] at h
            cases hl : mapLookupValueF σF map key keyTy valueTy with
            | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
            | ok pair =>
                rw [hl] at h
                simp only [Bind.bind, Except.bind] at h
                simp only [applyRhsOp, hm, hk, mapLookupValueF_ok hl,
                  Bind.bind, Except.bind]
                exact h
  · rename_i targetTy value
    simp only [applyRhsOp]
    exact h
  · simp only [applyRhsOp]
    exact h

theorem contAfterStmtOpF_ok {σF : ExecStateF} {op : StmtOp} {vs : List GoValue}
    {k k' : Cont} (h : contAfterStmtOpF σF op vs k = .ok k') :
    contAfterStmtOp (γF σF) op vs k = .ok k' := by
  unfold contAfterStmtOpF at h
  cases op <;>
    simp_all [contAfterStmtOp, pure, Except.pure, stuck]

/-- The alloc pair, bridged (private plumbing for the arm proofs). -/
private theorem alloc_pair_eq {σF : ExecStateF} {v : GoValue} {ty : Option Ty}
    {nloc : Loc} {σ₁ : ExecStateF} (hpair : allocF σF v ty = (nloc, σ₁)) :
    ExecState.alloc (γF σF) v ty = (nloc, γF σ₁) := by
  have h1 := allocF_loc σF v ty
  have h2 := allocF_state σF v ty
  rw [hpair] at h1 h2
  exact Prod.ext h1.symm h2.symm

private theorem core_newValue_ok {σF : ExecStateF} {typ : Option Ty} {nt : Nat}
    {tv value : GoValue} {σF' : ExecStateF}
    (h : applyStmtOpCoreF σF (.newValue typ) nt [tv, value] = .ok σF') :
    applyStmtOpCore (γF σF) (.newValue typ) nt [tv, value] = .ok (γF σF') := by
  simp only [applyStmtOpCoreF] at h
  cases hloc : valueAsLoc tv with
  | error e => rw [hloc] at h; simp [Bind.bind, Except.bind] at h
  | ok loc =>
      rw [hloc] at h
      simp only [Bind.bind, Except.bind] at h
      simp only [applyStmtOpCore, hloc, Bind.bind, Except.bind]
      rw [← allocF_loc, ← allocF_state, storeLocF_ok h]
      all_goals rfl

private theorem core_mapAssign_ok {σF : ExecStateF} {keyTy valueTy : Ty}
    {nt : Nat} {baseV keyV valueV : GoValue} {σF' : ExecStateF}
    (h : applyStmtOpCoreF σF (.mapAssign keyTy valueTy) nt [baseV, keyV, valueV]
      = .ok σF') :
    applyStmtOpCore (γF σF) (.mapAssign keyTy valueTy) nt [baseV, keyV, valueV]
      = .ok (γF σF') := by
  simp only [applyStmtOpCoreF] at h
  simp only [applyStmtOpCore]
  exact mapAssignValueF_ok h

private theorem core_makeMap_false_ok {σF : ExecStateF} {nt : Nat}
    {tv : GoValue} {σF' : ExecStateF}
    (h : applyStmtOpCoreF σF (.makeMap false) nt [tv] = .ok σF') :
    applyStmtOpCore (γF σF) (.makeMap false) nt [tv] = .ok (γF σF') := by
  simp only [applyStmtOpCoreF, buildDefaultArrayValue_ctx, Bind.bind, Except.bind, pure, Except.pure] at h
  cases hloc : valueAsLoc tv with
  | error e => rw [hloc] at h; simp [Bind.bind, Except.bind] at h
  | ok loc =>
      rw [hloc] at h
      simp only [Bind.bind, Except.bind] at h
      simp only [applyStmtOpCore, hloc, Bind.bind, Except.bind, pure,
        Except.pure]
      rw [← allocF_loc, ← allocF_state, storeLocF_ok h]
      all_goals rfl

private theorem core_makeMap_true_ok {σF : ExecStateF} {nt : Nat}
    {tv spaceV : GoValue} {σF' : ExecStateF}
    (h : applyStmtOpCoreF σF (.makeMap true) nt [tv, spaceV] = .ok σF') :
    applyStmtOpCore (γF σF) (.makeMap true) nt [tv, spaceV] = .ok (γF σF') := by
  simp only [applyStmtOpCoreF, buildDefaultArrayValue_ctx, Bind.bind, Except.bind, pure, Except.pure] at h
  cases hsz : valueAsInt spaceV with
  | error e => rw [hsz] at h; simp [Bind.bind, Except.bind] at h
  | ok size =>
      rw [hsz] at h
      simp only [Bind.bind, Except.bind] at h
      cases hnn : natFromNonnegativeInt "makemap: size out of range" size with
      | error e => rw [hnn] at h; simp [Bind.bind, Except.bind] at h
      | ok n =>
          rw [hnn] at h
          simp only [Bind.bind, Except.bind] at h
          cases hloc : valueAsLoc tv with
          | error e => rw [hloc] at h; simp [Bind.bind, Except.bind] at h
          | ok loc =>
              rw [hloc] at h
              simp only [Bind.bind, Except.bind] at h
              simp only [applyStmtOpCore, hsz, hnn, hloc,
                Bind.bind, Except.bind, pure, Except.pure]
              rw [← allocF_loc, ← allocF_state, storeLocF_ok h]
              all_goals rfl

private theorem core_makeSlice_ok {σF : ExecStateF} {elem : Ty} {nt : Nat}
    {tv lenV : GoValue} {capV? : Option GoValue} {hasCap : Bool}
    {σF' : ExecStateF}
    (hshape : match capV?, hasCap with
      | none, false => True | some _, true => True | _, _ => False)
    (h : applyStmtOpCoreF σF (.makeSlice elem hasCap) nt
        (match capV? with | none => [tv, lenV] | some capV => [tv, lenV, capV])
      = .ok σF') :
    applyStmtOpCore (γF σF) (.makeSlice elem hasCap) nt
        (match capV? with | none => [tv, lenV] | some capV => [tv, lenV, capV])
      = .ok (γF σF') := by
  cases capV? with
  | none =>
      cases hasCap with
      | true => exact absurd hshape (by simp)
      | false =>
        simp only [applyStmtOpCoreF, buildDefaultArrayValue_ctx, Bind.bind, Except.bind, pure,
          Except.pure] at h
        cases hlv : valueAsInt lenV with
        | error e => rw [hlv] at h; simp [Bind.bind, Except.bind] at h
        | ok lenValue =>
            rw [hlv] at h
            simp only [Bind.bind, Except.bind] at h
            cases hlen : natFromNonnegativeInt
                "runtime error: makeslice: len out of range" lenValue with
            | error e => rw [hlen] at h; simp [Bind.bind, Except.bind] at h
            | ok len =>
                rw [hlen] at h
                simp only [Bind.bind, Except.bind] at h
                cases hcap : natFromNonnegativeInt
                    "runtime error: makeslice: cap out of range" lenValue with
                | error e => rw [hcap] at h; simp [Bind.bind, Except.bind] at h
                | ok cap =>
                    rw [hcap] at h
                    simp only [Bind.bind, Except.bind] at h
                    split at h
                    case isTrue => simp [GoCore.panic] at h
                    case isFalse hcl =>
                      cases hbd : buildDefaultArrayValue (γF σF) cap elem with
                      | error e => rw [hbd] at h; simp [Bind.bind, Except.bind] at h
                      | ok backing =>
                          rw [hbd] at h
                          simp only [Bind.bind, Except.bind] at h
                          cases hloc : valueAsLoc tv with
                          | error e => rw [hloc] at h; simp [Bind.bind, Except.bind] at h
                          | ok loc =>
                              rw [hloc] at h
                              simp only [Bind.bind, Except.bind] at h
                              simp only [applyStmtOpCore, hlv, hlen, hcap,
                                hbd, hloc, hcl,
                                Bind.bind, Except.bind, pure, Except.pure,
                                if_neg]
                              rw [← allocF_loc, ← allocF_state, storeLocF_ok h]
                              all_goals rfl
  | some capV =>
      cases hasCap with
      | false => exact absurd hshape (by simp)
      | true =>
        simp only [applyStmtOpCoreF, buildDefaultArrayValue_ctx, Bind.bind, Except.bind, pure,
          Except.pure] at h
        cases hlv : valueAsInt lenV with
        | error e => rw [hlv] at h; simp [Bind.bind, Except.bind] at h
        | ok lenValue =>
            rw [hlv] at h
            simp only [Bind.bind, Except.bind] at h
            cases hcv : valueAsInt capV with
            | error e => rw [hcv] at h; simp [Bind.bind, Except.bind] at h
            | ok capValue =>
                rw [hcv] at h
                simp only [Bind.bind, Except.bind] at h
                cases hlen : natFromNonnegativeInt
                    "runtime error: makeslice: len out of range" lenValue with
                | error e => rw [hlen] at h; simp [Bind.bind, Except.bind] at h
                | ok len =>
                    rw [hlen] at h
                    simp only [Bind.bind, Except.bind] at h
                    cases hcap : natFromNonnegativeInt
                        "runtime error: makeslice: cap out of range" capValue with
                    | error e => rw [hcap] at h; simp [Bind.bind, Except.bind] at h
                    | ok cap =>
                        rw [hcap] at h
                        simp only [Bind.bind, Except.bind] at h
                        split at h
                        case isTrue => simp [GoCore.panic] at h
                        case isFalse hcl =>
                          cases hbd : buildDefaultArrayValue (γF σF) cap elem with
                          | error e => rw [hbd] at h; simp [Bind.bind, Except.bind] at h
                          | ok backing =>
                              rw [hbd] at h
                              simp only [Bind.bind, Except.bind] at h
                              cases hloc : valueAsLoc tv with
                              | error e => rw [hloc] at h; simp [Bind.bind, Except.bind] at h
                              | ok loc =>
                                  rw [hloc] at h
                                  simp only [Bind.bind, Except.bind] at h
                                  simp only [applyStmtOpCore, hlv, hcv, hlen,
                                    hcap, hbd, hloc, hcl,
                                    Bind.bind, Except.bind, pure, Except.pure,
                                    if_neg]
                                  rw [← allocF_loc, ← allocF_state, storeLocF_ok h]
                                  all_goals rfl


/-- Head-only bind reducers: rewrite ok/error-headed binds WITHOUT
normalizing lambda-internal binds (the wrinkle-register fix — a
pre-normalized hypothesis can no longer be `rw`-matched by bind-spelled
loop equations). -/
private theorem bind_ok_eq {α β : Type} (a : α) (f : α → Except GoError β) :
    (Except.ok a : Except GoError α) >>= f = f a := rfl
private theorem bind_error_eq {α β : Type} (e : GoError)
    (f : α → Except GoError β) :
    (Except.error e : Except GoError α) >>= f = .error e := rfl

/-- The sortSlice arm, isolated (vs already shaped). -/
private theorem core_sortSlice_ok {σF : ExecStateF} {cmp : Ty} {nt : Nat}
    {baseV : GoValue} {σF' : ExecStateF}
    (h : applyStmtOpCoreF σF (.sortSlice cmp) nt [baseV] = .ok σF') :
    applyStmtOpCore (γF σF) (.sortSlice cmp) nt [baseV] = .ok (γF σF') := by
  simp only [applyStmtOpCoreF] at h
  cases hsl : valueAsSlice baseV with
  | error e => rw [hsl] at h; simp [bind_error_eq] at h
  | ok slice =>
      rw [hsl] at h
      simp only [bind_ok_eq] at h
      cases hvs : validateSlice slice with
      | error e => rw [hvs] at h; simp [bind_error_eq] at h
      | ok u =>
          rw [hvs] at h
          simp only [bind_ok_eq] at h
          cases hread : forIn (List.range' 0 slice.len 1)
              (#[] : Array (Int × IntKind)) (fun i loaded => do
            match ← loadLocF σF (← sliceIndexLoc slice (Int.ofNat i)) with
            | .int v kind => pure (ForInStep.yield (loaded.push (v, kind)))
            | other => stuck s!"sortSlice expected int element, got {repr other}") with
          | error e => rw [hread] at h; simp [bind_error_eq] at h
          | ok loaded =>
              rw [hread] at h
              simp only [bind_ok_eq] at h
              cases hwrite : forIn (List.range' 0 slice.len 1) σF
                  (fun i current => do
                match (sortLe (fun (a b : Int × IntKind) => a.1 ≤ b.1) loaded.toList).toArray[i]? with
                | some (v, kind) => do
                    let c ← storeLocF current
                      (← sliceIndexLoc slice (Int.ofNat i)) (.int v kind)
                    pure (ForInStep.yield c)
                | none => stuck "sortSlice element count mismatch") with
              | error e => rw [hwrite] at h; simp [bind_error_eq] at h
              | ok current =>
                  rw [hwrite] at h
                  simp only [pure, Except.pure, Except.ok.injEq] at h
                  obtain ⟨lres, hlres, hlrel⟩ :=
                    list_forIn_sim (R := (· = ·))
                      (body := fun i loaded => do
                        let x ← sliceIndexLoc slice (Int.ofNat i)
                        let y ← loadLoc (γF σF) x
                        match y with
                        | .int v kind => do
                            pure PUnit.unit
                            pure (ForInStep.yield (loaded.push (v, kind)))
                        | other => do
                            stuck (toString "sortSlice expected int element, got "
                              ++ toString (repr other))
                            pure (ForInStep.yield loaded))
                      (fun i b' b hR s' hstep => by
                        subst hR
                        cases hloc : sliceIndexLoc slice (Int.ofNat i) with
                        | error e => rw [hloc] at hstep; simp [Bind.bind, Except.bind] at hstep
                        | ok loc =>
                            rw [hloc] at hstep
                            simp only [Bind.bind, Except.bind] at hstep
                            cases hl : loadLocF σF loc with
                            | error e => rw [hl] at hstep; simp at hstep
                            | ok v =>
                                rw [hl] at hstep
                                cases v <;> simp [Bind.bind, Except.bind, stuck] at hstep <;>
                                  · rename_i iv kind
                                    refine ⟨ForInStep.yield (b'.push (iv, kind)), ?_, ?_⟩
                                    · simp only [Bind.bind, Except.bind]
                                      rw [loadLocF_ok hl]
                                      simp [Bind.bind, Except.bind, pure, Except.pure]
                                    · rw [← hstep]
                                      simp [stepRel])
                      (List.range' 0 slice.len 1) rfl hread
                  obtain ⟨sres, hsres, hsrel⟩ :=
                    list_forIn_sim
                      (R := fun (cF : ExecStateF) (c : ExecState) => c = γF cF)
                      (body := fun i current =>
                        match (sortLe (fun (a b : Int × IntKind) =>
                            decide (a.fst ≤ b.fst)) lres.toList).toArray[i]? with
                        | some (v, kind) => do
                            let x ← sliceIndexLoc slice (Int.ofNat i)
                            let c ← storeLoc current x (GoValue.int v kind)
                            pure PUnit.unit
                            pure (ForInStep.yield c)
                        | none => do
                            stuck "sortSlice element count mismatch"
                            pure (ForInStep.yield current))
                      (fun i b' b hR s' hstep => by
                        cases hidx : (sortLe (fun (a b : Int × IntKind) => decide (a.fst ≤ b.fst)) loaded.toList).toArray[i]? with
                        | none => rw [hidx] at hstep; simp [stuck] at hstep
                        | some p =>
                            rw [hidx] at hstep
                            obtain ⟨v, kind⟩ := p
                            simp only [Bind.bind, Except.bind] at hstep
                            cases hloc : sliceIndexLoc slice (Int.ofNat i) with
                            | error e => rw [hloc] at hstep; simp [Bind.bind, Except.bind] at hstep
                            | ok loc =>
                                rw [hloc] at hstep
                                simp only [Bind.bind, Except.bind] at hstep
                                cases hst : storeLocF b' loc (.int v kind) with
                                | error e => rw [hst] at hstep; simp at hstep
                                | ok c =>
                                    rw [hst] at hstep
                                    simp only [pure, Except.pure,
                                      Except.ok.injEq] at hstep
                                    refine ⟨ForInStep.yield (γF c), ?_, ?_⟩
                                    · rw [← hlrel, hidx]
                                      simp only [Bind.bind, Except.bind]
                                      rw [hR, storeLocF_ok hst]
                                      simp [Bind.bind, Except.bind, pure, Except.pure]
                                    · rw [← hstep]
                                      simp [stepRel])
                      (List.range' 0 slice.len 1) rfl hwrite
                  simp only [applyStmtOpCore, hsl, hvs,
                    Std.Legacy.Range.forIn_eq_forIn_range',
                    Std.Legacy.Range.size, Nat.sub_zero,
                    Nat.add_sub_cancel, Nat.div_one]
                  simp only [hvs, bind_ok_eq]
                  show (do
                    let r ← forIn (List.range' 0 slice.len 1)
                      (#[] : Array (Int × IntKind)) (fun i loaded => do
                        let x ← sliceIndexLoc slice (Int.ofNat i)
                        let y ← loadLoc (γF σF) x
                        match y with
                        | GoValue.int v kind => do
                            pure PUnit.unit
                            pure (ForInStep.yield (loaded.push (v, kind)))
                        | other => do
                            stuck (toString "sortSlice expected int element, got "
                              ++ toString (repr other))
                            pure (ForInStep.yield loaded))
                    let r2 ← forIn (List.range' 0 slice.len 1) (γF σF)
                      (fun i current =>
                        match (sortLe (fun (a b : Int × IntKind) =>
                            decide (a.fst ≤ b.fst)) r.toList).toArray[i]? with
                        | some (v, kind) => do
                            let x ← sliceIndexLoc slice (Int.ofNat i)
                            let c ← storeLoc current x (GoValue.int v kind)
                            pure PUnit.unit
                            pure (ForInStep.yield c)
                        | none => do
                            stuck "sortSlice element count mismatch"
                            pure (ForInStep.yield current))
                    pure r2) = Except.ok (γF σF')
                  simp only [hlres, bind_ok_eq]
                  simp only [hsres, bind_ok_eq]
                  simp only [bind_ok_eq, pure, Except.pure,
                    Except.ok.injEq] at h
                  simp only [pure, Except.pure, Except.ok.injEq]
                  rw [hsrel, h]

/-- The copySlice arm, isolated. -/
private theorem core_copySlice_ok {σF : ExecStateF} {nt : Nat}
    {tv dstV srcV : GoValue} {σF' : ExecStateF}
    (h : applyStmtOpCoreF σF .copySlice nt [tv, dstV, srcV] = .ok σF') :
    applyStmtOpCore (γF σF) .copySlice nt [tv, dstV, srcV] = .ok (γF σF') := by
  simp only [applyStmtOpCoreF] at h
  cases hds : valueAsSlice dstV with
  | error e => rw [hds] at h; simp [bind_error_eq] at h
  | ok dstSlice =>
      rw [hds] at h
      simp only [bind_ok_eq] at h
      cases hss : valueAsSlice srcV with
      | error e => rw [hss] at h; simp [bind_error_eq] at h
      | ok srcSlice =>
          rw [hss] at h
          simp only [bind_ok_eq] at h
          cases hvd : validateSlice dstSlice with
          | error e => rw [hvd] at h; simp [bind_error_eq] at h
          | ok u1 =>
              rw [hvd] at h
              simp only [bind_ok_eq] at h
              cases hvsr : validateSlice srcSlice with
              | error e => rw [hvsr] at h; simp [bind_error_eq] at h
              | ok u2 =>
                  rw [hvsr] at h
                  simp only [bind_ok_eq] at h
                  cases hread : forIn
                      (List.range' 0 (Nat.min dstSlice.len srcSlice.len) 1)
                      (#[] : Array GoValue) (fun i values => do
                    let v ← loadLocF σF (← sliceIndexLoc srcSlice (Int.ofNat i))
                    pure (ForInStep.yield (values.push v))) with
                  | error e => rw [hread] at h; simp [bind_error_eq] at h
                  | ok values =>
                      rw [hread] at h
                      simp only [bind_ok_eq] at h
                      cases hwrite : forIn values.toList (σF, (0 : Nat))
                          (fun value st => do
                        let c ← storeLocF st.1
                          (← sliceIndexLoc dstSlice (Int.ofNat st.2)) value
                        pure (ForInStep.yield (c, st.2 + 1))) with
                      | error e => rw [hwrite] at h; simp [bind_error_eq] at h
                      | ok st =>
                          rw [hwrite] at h
                          simp only [bind_ok_eq] at h
                          cases htl : valueAsLoc tv with
                          | error e => rw [htl] at h; simp [bind_error_eq] at h
                          | ok tloc =>
                              rw [htl] at h
                              simp only [bind_ok_eq] at h
                              obtain ⟨lres, hlres, hlrel⟩ :=
                                list_forIn_sim (R := (· = ·))
                                  (body := fun i values => do
                                    let x ← sliceIndexLoc srcSlice (Int.ofNat i)
                                    let y ← loadLoc (γF σF) x
                                    pure PUnit.unit
                                    pure (ForInStep.yield (values.push y)))
                                  (fun i b' b hR s' hstep => by
                                    subst hR
                                    cases hloc : sliceIndexLoc srcSlice (Int.ofNat i) with
                                    | error e => rw [hloc] at hstep; simp [Bind.bind, Except.bind] at hstep
                                    | ok loc =>
                                        rw [hloc] at hstep
                                        simp only [Bind.bind, Except.bind] at hstep
                                        cases hl : loadLocF σF loc with
                                        | error e => rw [hl] at hstep; simp at hstep
                                        | ok v =>
                                            rw [hl] at hstep
                                            simp only [pure, Except.pure,
                                              Except.ok.injEq] at hstep
                                            refine ⟨ForInStep.yield (b'.push v), ?_, ?_⟩
                                            · simp only [Bind.bind, Except.bind]
                                              rw [loadLocF_ok hl]
                                              simp [Bind.bind, Except.bind, pure, Except.pure]
                                            · rw [← hstep]
                                              simp [stepRel])
                                  (List.range' 0 (Nat.min dstSlice.len srcSlice.len) 1)
                                  rfl hread
                              obtain ⟨sres, hsres, hsrel⟩ :=
                                list_forIn_sim
                                  (R := fun (pF : ExecStateF × Nat)
                                      (p : MProd ExecState Nat) =>
                                    p.fst = γF pF.1 ∧ p.snd = pF.2)
                                  (body := fun value r => do
                                    let x ← sliceIndexLoc dstSlice (Int.ofNat r.snd)
                                    let c ← storeLoc r.fst x value
                                    pure PUnit.unit
                                    pure (ForInStep.yield ⟨c, r.snd + 1⟩))
                                  (fun value b' b hR s' hstep => by
                                    obtain ⟨hR1, hR2⟩ := hR
                                    cases hloc : sliceIndexLoc dstSlice (Int.ofNat b'.2) with
                                    | error e => rw [hloc] at hstep; simp [Bind.bind, Except.bind] at hstep
                                    | ok loc =>
                                        rw [hloc] at hstep
                                        simp only [Bind.bind, Except.bind] at hstep
                                        cases hst : storeLocF b'.1 loc value with
                                        | error e => rw [hst] at hstep; simp at hstep
                                        | ok c =>
                                            rw [hst] at hstep
                                            simp only [pure, Except.pure,
                                              Except.ok.injEq] at hstep
                                            refine ⟨ForInStep.yield ⟨γF c, b'.2 + 1⟩, ?_, ?_⟩
                                            · rw [hR2, hloc]
                                              simp only [Bind.bind, Except.bind]
                                              rw [hR1, storeLocF_ok hst]
                                              simp [Bind.bind, Except.bind, pure, Except.pure]
                                            · rw [← hstep]
                                              simp [stepRel])
                                  values.toList (init := (⟨γF σF, 0⟩ : MProd ExecState Nat)) ⟨rfl, rfl⟩ hwrite
                              simp only [applyStmtOpCore, hds, hss, hvd, hvsr,
                                htl,
                                Std.Legacy.Range.forIn_eq_forIn_range',
                                Std.Legacy.Range.size, Nat.sub_zero,
                                Nat.add_sub_cancel, Nat.div_one]
                              simp only [hvd, hvsr, bind_ok_eq]
                              simp only [hlres, bind_ok_eq]
                              rw [← hlrel, ← Array.forIn_toList]
                              simp only [hsres, bind_ok_eq]
                              simp only [pure, Except.pure, Except.ok.injEq]
                              obtain ⟨hs1, hs2⟩ := hsrel
                              rw [hs1]
                              rw [storeLocF_ok h]
                              rfl

theorem applyStmtOpCoreF_ok {σF : ExecStateF} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {σF' : ExecStateF}
    (h : applyStmtOpCoreF σF op nt vs = .ok σF') :
    applyStmtOpCore (γF σF) op nt vs = .ok (γF σF') := by
  cases op with
  | makeChan _ => simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | mapDelete _ => simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | clearMap => simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | clearSlice _ => simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | appendSlice _ => simp [applyStmtOpCoreF] at h
  | newValue typ =>
      rcases vs with _ | ⟨tv, _ | ⟨value, _ | ⟨a, rest⟩⟩⟩
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · exact core_newValue_ok h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | mapAssign keyTy valueTy =>
      rcases vs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · exact core_mapAssign_ok h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | makeMap hasSpace =>
      cases hasSpace with
      | false =>
          rcases vs with _ | ⟨tv, _ | ⟨v2, rest⟩⟩
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · exact core_makeMap_false_ok h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      | true =>
          rcases vs with _ | ⟨tv, _ | ⟨spaceV, _ | ⟨v3, rest⟩⟩⟩
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · exact core_makeMap_true_ok h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | makeSlice elem hasCap =>
      cases hasCap with
      | false =>
          rcases vs with _ | ⟨tv, _ | ⟨lenV, _ | ⟨v3, rest⟩⟩⟩
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · exact core_makeSlice_ok (capV? := none) (by simp) h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      | true =>
          rcases vs with _ | ⟨tv, _ | ⟨lenV, _ | ⟨capV, _ | ⟨v4, rest⟩⟩⟩⟩
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
          · exact core_makeSlice_ok (capV? := some capV) (by simp) h
          · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | sortSlice cmp =>
      rcases vs with _ | ⟨baseV, _ | ⟨v2, rest⟩⟩
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · exact core_sortSlice_ok h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
  | copySlice =>
      rcases vs with _ | ⟨tv, _ | ⟨dstV, _ | ⟨srcV, _ | ⟨v4, rest⟩⟩⟩⟩
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h
      · exact core_copySlice_ok h
      · simp [applyStmtOpCoreF, stuck, bind_error_eq, throw, throwThe, MonadExceptOf.throw] at h


theorem applyStmtOpF_ok {σF : ExecStateF} {choices : Choices} {op : StmtOp}
    {nt : Nat} {vs : List GoValue} {σF' : ExecStateF} {ch' : Choices}
    (h : applyStmtOpF σF choices op nt vs = .ok (σF', ch')) :
    applyStmtOp (γF σF) choices op nt vs = .ok (γF σF', ch') := by
  unfold applyStmtOpF at h
  try simp only [buildAppendBackingValue_ctx] at h
  split at h
  case h_2 =>
    rename_i oparm hne
    cases hc : applyStmtOpCoreF σF op nt vs with
    | error e => rw [hc] at h; simp [Bind.bind, Except.bind] at h
    | ok c =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        unfold applyStmtOp
        split
        · rename_i elem
          exact (hne elem rfl).elim
        · simp only [Bind.bind, Except.bind]
          rw [applyStmtOpCoreF_ok hc]
          simp only [pure, Except.pure, h1, h2]
  case h_1 elem =>
    rcases vs with _ | ⟨tv, _ | ⟨sliceV, _ | ⟨elemsV, _ | ⟨v4, rest⟩⟩⟩⟩
    · exact nomatch h
    · exact nomatch h
    · exact nomatch h
    case cons.cons.cons.cons => exact nomatch h
    case cons.cons.cons.nil =>
      simp only [] at h
      cases hsv : valueAsSlice sliceV with
      | error e => rw [hsv] at h; simp [Bind.bind, Except.bind] at h
      | ok slice =>
          rw [hsv] at h
          simp only [bind_ok_eq] at h
          cases hev : valueAsSlice elemsV with
          | error e => rw [hev] at h; simp [bind_error_eq] at h
          | ok elems =>
              rw [hev] at h
              simp only [bind_ok_eq] at h
              cases hv1 : validateSlice slice with
              | error e => rw [hv1] at h; simp [bind_error_eq] at h
              | ok u1 =>
                  rw [hv1] at h
                  simp only [bind_ok_eq] at h
                  cases hv2 : validateSlice elems with
                  | error e => rw [hv2] at h; simp [bind_error_eq] at h
                  | ok u2 =>
                      rw [hv2] at h
                      simp only [bind_ok_eq] at h
                      cases hvv : sliceVisibleValuesF σF elems with
                      | error e => rw [hvv] at h; simp [bind_error_eq] at h
                      | ok elemValues =>
                          rw [hvv] at h
                          simp only [bind_ok_eq] at h
                          cases htl : valueAsLoc tv with
                          | error e => rw [htl] at h; simp [bind_error_eq] at h
                          | ok tloc =>
                              rw [htl] at h
                              simp only [bind_ok_eq] at h
                              split at h
                              case isTrue hle =>
                                cases hwr : forIn elemValues.toList (σF, (0 : Nat))
                                    (fun value st => do
                                      match slice.base with
                                      | some base => do
                                          let c ← storeLocF st.1
                                            (.index base (Int.ofNat (slice.offset + slice.len + st.2))) value
                                          pure (ForInStep.yield (c, st.2 + 1))
                                      | none => stuck s!"cannot append {elemValues.size} element(s) into nil slice in place") with
                                | error e => rw [hwr] at h; simp [bind_error_eq] at h
                                | ok st =>
                                    rw [hwr] at h
                                    simp only [bind_ok_eq] at h
                                    cases hst : storeLocF st.1 tloc
                                        (.slice { slice with len := slice.len + elemValues.size }) with
                                    | error e => rw [hst] at h; simp [bind_error_eq] at h
                                    | ok σFr =>
                                        rw [hst] at h
                                        simp only [pure, Except.pure,
                                          Except.ok.injEq, Prod.mk.injEq] at h
                                        obtain ⟨h1, h2⟩ := h
                                        obtain ⟨swr, hswr, hsrel⟩ :=
                                          list_forIn_sim
                                            (R := fun (pF : ExecStateF × Nat)
                                                (p : MProd ExecState Nat) =>
                                              p.fst = γF pF.1 ∧ p.snd = pF.2)
                                            (body := fun value r => do
                                              match slice.base with
                                              | some base => do
                                                  let c ← storeLoc r.fst
                                                    (Loc.index base (Int.ofNat (slice.offset + slice.len + r.snd))) value
                                                  pure PUnit.unit
                                                  pure (ForInStep.yield ⟨c, r.snd + 1⟩)
                                              | none => do
                                                  stuck (toString "cannot append "
                                                    ++ toString elemValues.size
                                                    ++ toString " element(s) into nil slice in place")
                                                  pure (ForInStep.yield ⟨r.fst, r.snd⟩))
                                            (fun value b' b hR s' hstep => by
                                              obtain ⟨hR1, hR2⟩ := hR
                                              cases hbase : slice.base with
                                              | none => rw [hbase] at hstep; simp [stuck] at hstep
                                              | some base =>
                                                  rw [hbase] at hstep
                                                  simp only [Bind.bind, Except.bind] at hstep
                                                  cases hsl2 : storeLocF b'.1
                                                      (.index base (Int.ofNat (slice.offset + slice.len + b'.2))) value with
                                                  | error e => rw [hsl2] at hstep; simp at hstep
                                                  | ok c =>
                                                      rw [hsl2] at hstep
                                                      simp only [pure, Except.pure,
                                                        Except.ok.injEq] at hstep
                                                      refine ⟨ForInStep.yield ⟨γF c, b'.2 + 1⟩, ?_, ?_⟩
                                                      · simp only [Bind.bind, Except.bind]
                                                        rw [hR2, hR1, storeLocF_ok hsl2]
                                                        simp [Bind.bind, Except.bind, pure, Except.pure]
                                                      · rw [← hstep]
                                                        simp [stepRel])
                                            elemValues.toList
                                            (init := (⟨γF σF, 0⟩ : MProd ExecState Nat))
                                            ⟨rfl, rfl⟩ hwr
                                        unfold applyStmtOp
                                        simp only [hsv, hev, hv1, hv2,
                                          sliceVisibleValuesF_ok hvv, htl, bind_ok_eq,
                                          if_pos hle]
                                        show (do
                                          let r ← forIn elemValues
                                            (⟨γF σF, 0⟩ : MProd ExecState Nat)
                                            (fun value r => do
                                              match slice.base with
                                              | some base => do
                                                  let c ← storeLoc r.fst
                                                    (Loc.index base (Int.ofNat (slice.offset + slice.len + r.snd))) value
                                                  pure PUnit.unit
                                                  pure (ForInStep.yield ⟨c, r.snd + 1⟩)
                                              | none => do
                                                  stuck (toString "cannot append "
                                                    ++ toString elemValues.size
                                                    ++ toString " element(s) into nil slice in place")
                                                  pure (ForInStep.yield ⟨r.fst, r.snd⟩))
                                          let x ← storeLoc r.fst tloc
                                            (GoValue.slice { slice with len := slice.len + elemValues.size })
                                          pure (x, choices)) = Except.ok (γF σF', choices)
                                        rw [← Array.forIn_toList]
                                        simp only [hswr, bind_ok_eq]
                                        obtain ⟨hs1, hs2⟩ := hsrel
                                        rw [hs1, storeLocF_ok hst]
                                        all_goals simp_all [pure, Except.pure, bind_ok_eq]
                              case isFalse hgt =>
                                cases hov : sliceVisibleValuesF σF slice with
                                | error e => rw [hov] at h; simp [bind_error_eq] at h
                                | ok oldValues =>
                                    rw [hov] at h
                                    simp only [bind_ok_eq] at h
                                    unfold applyStmtOp
                                    simp only [hsv, hev, hv1, hv2, sliceVisibleValuesF_ok hvv, htl, bind_ok_eq, if_neg hgt, sliceVisibleValuesF_ok hov]
                                    generalize hNC : slice.len + elemValues.size + ((appendGrowthCap slice.cap (slice.len + elemValues.size) - (slice.len + elemValues.size) + (Choices.consumeAt .appendSpill (appendSpillWidth slice.cap (slice.len + elemValues.size)) choices).1) % appendSpillWidth slice.cap (slice.len + elemValues.size)) = nc at h ⊢
                                    cases hbb : buildAppendBackingValue (γF σF) elem oldValues elemValues nc with
                                    | error e => rw [hbb] at h; simp [bind_error_eq] at h
                                    | ok backing =>
                                        rw [hbb] at h
                                        simp only [bind_ok_eq] at h ⊢
                                        rw [← allocF_loc, ← allocF_state]
                                        cases hst : storeLocF (allocF σF backing (some (Ty.array nc elem))).2 tloc
                                            (GoValue.slice { base := some (allocF σF backing (some (Ty.array nc elem))).1, offset := 0, len := slice.len + elemValues.size, cap := nc }) with
                                        | error e => rw [hst] at h; simp [bind_error_eq] at h
                                        | ok σFr =>
                                            rw [hst] at h
                                            rw [storeLocF_ok hst]
                                            simp only [bind_ok_eq, pure, Except.pure,
                                              Except.ok.injEq, Prod.mk.injEq] at h ⊢
                                            exact ⟨congrArg γF h.1, h.2⟩

end GoLean.FastEval
