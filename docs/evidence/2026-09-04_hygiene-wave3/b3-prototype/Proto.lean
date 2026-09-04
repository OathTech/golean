import GoLean.GoCore.Machine
import GoLean.GoCore.StateWf

namespace GoLean.GoCore.Machine

/-- The tail (immediate continuation) of a frame; `.stop` has none. -/
def Cont.tail : Cont → Option Cont
  | .stop => none
  | .seq _ _ k | .loop _ _ _ k | .frame _ _ _ _ k _ | .deferCalleeK _ _ k
  | .deferArgsK _ _ _ _ k | .breakableK k | .labelK _ k | .callValCalleeK _ _ _ k
  | .callValArgsK _ _ _ _ _ k | .strictK _ _ _ _ k | .andK _ _ k | .orK _ _ k
  | .boolK k | .ifK _ _ _ k | .whileK _ _ _ k | .callArgsK _ _ _ _ _ k
  | .stmtOpK _ _ _ _ _ k | .mapRangeK _ _ _ _ _ _ k | .mapIterK _ _ _ _ _ _ _ _ _ k
  | .panicArgK k | .panicResumeK _ k | .chanStK _ _ _ _ k | .selectOpsK _ _ _ _ _ k
  | .tgtOpK _ _ _ _ _ _ _ _ _ _ k | .rhsK _ _ _ _ _ _ k | .storeK _ _ _ _ k
  | .goCalleeK _ _ k | .goArgsK _ _ _ _ k | .syncStK _ _ _ _ k | .atomicStK _ _ _ _ k => some k

/-- Replace the tail. `.stop` is unchanged. -/
def Cont.withTail : Cont → Cont → Cont
  | .stop, _ => .stop
  | .seq a b _, t => .seq a b t
  | .loop a b c _, t => .loop a b c t
  | .frame a b c d _ w, t => .frame a b c d t w
  | .deferCalleeK a b _, t => .deferCalleeK a b t
  | .deferArgsK a b c d _, t => .deferArgsK a b c d t
  | .breakableK _, t => .breakableK t
  | .labelK a _, t => .labelK a t
  | .callValCalleeK a b c _, t => .callValCalleeK a b c t
  | .callValArgsK a b c d e _, t => .callValArgsK a b c d e t
  | .strictK a b c d _, t => .strictK a b c d t
  | .andK a b _, t => .andK a b t
  | .orK a b _, t => .orK a b t
  | .boolK _, t => .boolK t
  | .ifK a b c _, t => .ifK a b c t
  | .whileK a b c _, t => .whileK a b c t
  | .callArgsK a b c d e _, t => .callArgsK a b c d e t
  | .stmtOpK a b c d e _, t => .stmtOpK a b c d e t
  | .mapRangeK a b c d e f _, t => .mapRangeK a b c d e f t
  | .mapIterK a b c d e f g h i _, t => .mapIterK a b c d e f g h i t
  | .panicArgK _, t => .panicArgK t
  | .panicResumeK a _, t => .panicResumeK a t
  | .chanStK a b c d _, t => .chanStK a b c d t
  | .selectOpsK a b c d e _, t => .selectOpsK a b c d e t
  | .tgtOpK a b c d e f g h i j _, t => .tgtOpK a b c d e f g h i j t
  | .rhsK a b c d e f _, t => .rhsK a b c d e f t
  | .storeK a b c d _, t => .storeK a b c d t
  | .goCalleeK a b _, t => .goCalleeK a b t
  | .goArgsK a b c d _, t => .goArgsK a b c d t
  | .syncStK a b c d _, t => .syncStK a b c d t
  | .atomicStK a b c d _, t => .atomicStK a b c d t

theorem Cont.sizeOf_tail_lt {k k' : Cont} (h : k.tail = some k') : sizeOf k' < sizeOf k := by
  cases k <;> simp_all [Cont.tail] <;> omega

theorem Cont.withTail_tail : ∀ k : Cont, (k.tail.map k.withTail).getD k = k := by
  intro k; cases k <;> rfl

theorem Cont.tail_withTail {k t : Cont} (h : k ≠ .stop) : (k.withTail t).tail = some t := by
  cases k <;> first | exact absurd rfl h | rfl

inductive FrameClass where
  | stmtGlue | exprGlue | callFrame | resumeMarker | stop
  deriving DecidableEq, Repr

def Cont.class : Cont → FrameClass
  | .stop => .stop
  | .frame .. => .callFrame
  | .panicResumeK .. => .resumeMarker
  | .seq .. | .loop .. | .breakableK .. | .labelK .. | .mapIterK .. => .stmtGlue
  | _ => .exprGlue

def Cont.rebuild {β : Type} (descend : Cont → Bool) (act : Cont → Option (β × Cont)) (k : Cont) :
    Option (β × Cont) :=
  if descend k then
    match _h : k.tail with
    | some k' => (Cont.rebuild descend act k').map fun (b, k'') => (b, k.withTail k'')
    | none => act k
  else act k
termination_by sizeOf k
decreasing_by exact Cont.sizeOf_tail_lt _h

def pushDefer' (d : GoValue × List GoValue) (k : Cont) : Option Cont :=
  (Cont.rebuild (fun k => k.class = .stmtGlue)
    (fun k => match k with
      | .frame t te r ds k w => some ((), .frame t te r (d :: ds) k w)
      | _ => none) k).map (·.2)


theorem Cont.rebuild_descend {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    {k : Cont} (hd : descend k = true) :
    Cont.rebuild descend act k =
      match k.tail with
      | some k' => (Cont.rebuild descend act k').map fun (b, k'') => (b, k.withTail k'')
      | none => act k := by
  rw [Cont.rebuild]; simp only [hd, ↓reduceIte]; split <;> simp_all

theorem Cont.rebuild_act {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    {k : Cont} (hd : descend k = false) : Cont.rebuild descend act k = act k := by
  rw [Cont.rebuild]; simp [hd]

theorem Cont.rebuild_stop {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)} :
    Cont.rebuild descend act .stop = act .stop := by
  rw [Cont.rebuild]; split <;> simp [Cont.tail]

theorem pushDefer'_eq (d : GoValue × List GoValue) : ∀ k, pushDefer' d k = pushDefer d k := by
  intro k
  induction k with
  | stop => simp [pushDefer', pushDefer, Cont.rebuild_stop]
  | frame a b c d' k w _ => simp [pushDefer', pushDefer, Cont.rebuild_act, Cont.class]
  | seq a b k ih | loop a b c k ih | breakableK k ih | labelK a k ih
  | mapIterK a b c d' e f g h i k ih =>
      simp only [pushDefer'] at ih
      rw [pushDefer', Cont.rebuild_descend (by simp [Cont.class])]; simp only [Cont.tail]; rw [pushDefer, ← ih]
      cases Cont.rebuild _ _ k <;> simp [Cont.withTail]
  | _ => simp [pushDefer', pushDefer, Cont.rebuild_act, Cont.class]

/-- Glue for the RECOVER walks: statement/expression glue and wrapper frames. -/
def Cont.recoverTransparent : Cont → Bool
  | .frame _ _ _ _ _ w => w
  | k => k.class = .stmtGlue || k.class = .exprGlue

def recoverThroughWrappers' (k : Cont) : Option (GoValue × Cont) :=
  Cont.rebuild Cont.recoverTransparent
    (fun k => match k with
      | .panicResumeK chain k => (markNewestRecovered chain).map fun (v, chain') => (v, .panicResumeK chain' k)
      | _ => none) k

theorem recoverThroughWrappers'_eq : ∀ k, recoverThroughWrappers' k = recoverThroughWrappers k := by
  intro k
  induction k with
  | stop => simp [recoverThroughWrappers', recoverThroughWrappers, Cont.rebuild_stop]
  | panicResumeK a k _ => simp [recoverThroughWrappers', recoverThroughWrappers, Cont.rebuild_act, Cont.recoverTransparent, Cont.class]
  | frame a b c d k w ih =>
      cases w
      · simp [recoverThroughWrappers', recoverThroughWrappers, Cont.rebuild_act, Cont.recoverTransparent]
      · simp only [recoverThroughWrappers'] at ih
        rw [recoverThroughWrappers', Cont.rebuild_descend (by simp [Cont.recoverTransparent])]; simp only [Cont.tail]; rw [recoverThroughWrappers, ← ih]
        cases Cont.rebuild _ _ k <;> simp [Cont.withTail]
  | _ =>
      rename_i k ih
      simp only [recoverThroughWrappers'] at ih
      rw [recoverThroughWrappers', Cont.rebuild_descend (by simp [Cont.recoverTransparent, Cont.class])]; simp only [Cont.tail]; rw [recoverThroughWrappers, ← ih]
      cases Cont.rebuild _ _ k <;> simp [Cont.withTail]

def recoverResult' (k : Cont) : GoValue × Cont :=
  (Cont.rebuild Cont.recoverTransparent
    (fun k => match k with
      | .frame t te r ds k' false =>
          some (match recoverThroughWrappers' k' with
            | some (v, k'') => (v, .frame t te r ds k'' false)
            | none => (.nil, .frame t te r ds k' false))
      | k => some (.nil, k)) k).getD (.nil, k)

theorem recoverResult'_eq : ∀ k, recoverResult' k = recoverResult k := by
  intro k
  induction k with
  | stop => simp [recoverResult', recoverResult, Cont.rebuild_stop]
  | panicResumeK a k _ => simp [recoverResult', recoverResult, Cont.rebuild_act, Cont.recoverTransparent, Cont.class]
  | frame a b c d k w ih =>
      cases w
      · simp [recoverResult', recoverResult, Cont.rebuild_act, Cont.recoverTransparent, recoverThroughWrappers'_eq]
        split <;> simp_all
      · simp only [recoverResult'] at ih
        rw [recoverResult', Cont.rebuild_descend (by simp [Cont.recoverTransparent])]; simp only [Cont.tail]; rw [recoverResult, ← ih]
        cases Cont.rebuild _ _ k <;> simp [Cont.withTail]
  | _ =>
      rename_i k ih
      simp only [recoverResult'] at ih
      rw [recoverResult', Cont.rebuild_descend (by simp [Cont.recoverTransparent, Cont.class])]; simp only [Cont.tail]; rw [recoverResult, ← ih]
      cases Cont.rebuild _ _ k <;> simp [Cont.withTail]

/-- The frame's OWN payload sup (its tail replaced by `.stop`). -/
def Cont.ownSup (k : Cont) : Nat := Cont.locSup (k.withTail .stop)

theorem Cont.locSup_withTail {k k₀ t : Cont} (h : k.tail = some k₀) :
    Cont.locSup (k.withTail t) = max (Cont.ownSup k) (Cont.locSup t) := by
  cases k <;> simp [Cont.tail] at h <;> simp [Cont.withTail, Cont.ownSup, Cont.locSup] <;> omega

theorem Cont.locSup_eq_own_tail {k k₀ : Cont} (h : k.tail = some k₀) :
    Cont.locSup k = max (Cont.ownSup k) (Cont.locSup k₀) := by
  have := Cont.locSup_withTail (t := k₀) h
  rw [← this]; congr 1
  cases k <;> simp_all [Cont.tail, Cont.withTail]

#check @Cont.rebuild.induct

theorem Cont.rebuild_locSup {β : Type} {descend : Cont → Bool} {act : Cont → Option (β × Cont)}
    {bound : Nat}
    (hact : ∀ k b k', act k = some (b, k') → Cont.locSup k' ≤ max bound (Cont.locSup k)) :
    ∀ k b k', Cont.rebuild descend act k = some (b, k') → Cont.locSup k' ≤ max bound (Cont.locSup k) := by
  intro k
  induction k using WellFounded.induction (r := fun a b : Cont => sizeOf a < sizeOf b)
    (hwf := (measure sizeOf).wf) with
  | _ k ih =>
  intro b k' h
  by_cases hd : descend k = true
  · rw [Cont.rebuild_descend hd] at h
    cases ht : k.tail with
    | none => rw [ht] at h; exact hact _ _ _ h
    | some k₀ =>
      rw [ht] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨b₁, k₁⟩, h₁, h₂⟩ := h
      simp only [Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      rw [Cont.locSup_withTail ht, Cont.locSup_eq_own_tail ht]
      have := ih k₀ (Cont.sizeOf_tail_lt ht) b₁ k₁ h₁
      omega
  · rw [Cont.rebuild_act (Bool.eq_false_iff.mpr hd)] at h
    exact hact _ _ _ h

end GoLean.GoCore.Machine
