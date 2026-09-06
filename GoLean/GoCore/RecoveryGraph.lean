import GoLean.GoCore.RecoveryStatements

namespace GoLean.GoCore.RecoveryTyping

/- Direct calls and statically known closure invocations all create edges,
including defers and syntactically unreachable branches. The grammar does
not permit function values hidden in arbitrary expressions or heap cells. -/
mutual
inductive Calls : Stmt → FuncId → Prop
  | direct {targets fid args} : Calls (.call targets fid args) fid
  | closure {targets fid caps args} : Calls (.callValue targets (.funcVal fid caps) args) fid
  | deferred {fid caps args} : Calls (.deferCall (.funcVal fid caps) args) fid
  | seqn {ss fid} : CallsList ss.toList fid → Calls (.seqn ss) fid
  | block {ps ss fid} : CallsList ss.toList fid → Calls (.block ps ss) fid
  | thenBranch {e t f fid} : Calls t fid → Calls (.ifThenElse e t f) fid
  | elseBranch {e t f fid} : Calls f fid → Calls (.ifThenElse e t f) fid
inductive CallsList : List Stmt → FuncId → Prop
  | head {s ss fid} : Calls s fid → CallsList (s :: ss) fid
  | tail {s ss fid} : CallsList ss fid → CallsList (s :: ss) fid
end

mutual
def callIds : Stmt → List FuncId
  | .call _ fid _ => [fid]
  | .callValue _ (.funcVal fid _) _ | .deferCall (.funcVal fid _) _ => [fid]
  | .seqn ss | .block _ ss => callIdsList ss.toList
  | .ifThenElse _ t f => callIds t ++ callIds f
  | _ => []
def callIdsList : List Stmt → List FuncId
  | [] => []
  | s :: ss => callIds s ++ callIdsList ss
end

mutual
theorem callIds_sound (s : Stmt) (fid : FuncId) (h : fid ∈ callIds s) : Calls s fid := by
  cases s <;> try simp only [callIds, List.mem_nil_iff, List.mem_singleton] at h
  case call targets g args => subst fid; exact .direct
  case callValue targets callee args =>
    cases callee <;> simp only [callIds, List.mem_nil_iff, List.mem_singleton] at h
    subst fid
    exact .closure
  case deferCall callee args =>
    cases callee <;> simp only [callIds, List.mem_nil_iff, List.mem_singleton] at h
    subst fid
    exact .deferred
  case seqn ss => exact .seqn (callIdsList_sound ss.toList fid h)
  case block ps ss => exact .block (callIdsList_sound ss.toList fid h)
  case ifThenElse e t f =>
    rcases List.mem_append.mp h with h | h
    · exact .thenBranch (callIds_sound t fid h)
    · exact .elseBranch (callIds_sound f fid h)
termination_by structural s
theorem callIdsList_sound (ss : List Stmt) (fid : FuncId) (h : fid ∈ callIdsList ss) :
    CallsList ss fid := by
  cases ss with
  | nil => contradiction
  | cons s ss =>
      rcases List.mem_append.mp h with h | h
      · exact .head (callIds_sound s fid h)
      · exact .tail (callIdsList_sound ss fid h)
termination_by structural ss
end

theorem callIds_complete {s fid} (h : Calls s fid) : fid ∈ callIds s := by
  induction h using Calls.rec (motive_2 := fun ss fid _ => fid ∈ callIdsList ss) <;>
    simp_all [callIds, callIdsList]

theorem callIds_iff (s : Stmt) (fid : FuncId) : fid ∈ callIds s ↔ Calls s fid :=
  ⟨callIds_sound s fid, callIds_complete⟩

/-- A structural call-tree certificate. Depth counts function nodes, not
execution steps or allocations. The program checker uses its function count;
it imposes no source/function-table ordering. -/
inductive CallDepth (fs : Array Func) : Nat → FuncId → Prop
  | node {n fid f} : findFunctionIn? fs fid = some f →
      (∀ g, Calls f.body g → CallDepth fs n g) → CallDepth fs (n + 1) fid

def checkCallDepth (fs : Array Func) : Nat → FuncId → Bool
  | 0, _ => false
  | n + 1, fid =>
      match findFunctionIn? fs fid with
      | none => false
      | some f => (callIds f.body).all (checkCallDepth fs n)

theorem checkCallDepth_iff (fs : Array Func) (n : Nat) (fid : FuncId) :
    checkCallDepth fs n fid = true ↔ CallDepth fs n fid := by
  induction n generalizing fid with
  | zero =>
      constructor
      · intro h; contradiction
      · intro h; cases h
  | succ n ih =>
      constructor
      · intro h
        unfold checkCallDepth at h
        split at h
        · contradiction
        · rename_i f hf
          refine .node hf (fun g hg => (ih g).mp ?_)
          exact List.all_eq_true.mp h g (callIds_complete hg)
      · intro h
        cases h with
        | node hf hh =>
            simp only [checkCallDepth, hf]
            exact List.all_eq_true.mpr (fun g hg => (ih g).mpr (hh g (callIds_sound _ _ hg)))

instance (fs : Array Func) (n : Nat) (fid : FuncId) : Decidable (CallDepth fs n fid) :=
  decidable_of_iff (checkCallDepth fs n fid = true) (checkCallDepth_iff fs n fid)

theorem CallDepth.down {fs n fid f g} (h : CallDepth fs (n + 1) fid)
    (hf : findFunctionIn? fs fid = some f) (hg : Calls f.body g) : CallDepth fs n g := by
  cases h with
  | node hf' hh =>
      rw [hf] at hf'
      cases hf'
      exact hh _ hg

theorem no_self_call {fs n fid f} (h : CallDepth fs n fid)
    (hf : findFunctionIn? fs fid = some f) : ¬ Calls f.body fid := by
  intro hself
  induction n with
  | zero => cases h
  | succ n ih => exact ih (h.down hf hself)

def CallEdge (fs : Array Func) (fid g : FuncId) : Prop :=
  ∃ f, findFunctionIn? fs fid = some f ∧ Calls f.body g

inductive CallPath (fs : Array Func) : FuncId → FuncId → Prop
  | single {f g} : CallEdge fs f g → CallPath fs f g
  | cons {f g h} : CallEdge fs f g → CallPath fs g h → CallPath fs f h

theorem CallDepth.edge {fs n f g} (h : CallDepth fs n f) (he : CallEdge fs f g) :
    ∃ m, m < n ∧ CallDepth fs m g := by
  obtain ⟨func, hf, hg⟩ := he
  cases n with
  | zero => cases h
  | succ n => exact ⟨n, Nat.lt_succ_self n, h.down hf hg⟩

theorem CallDepth.path {fs n f g} (h : CallDepth fs n f) (hp : CallPath fs f g) :
    ∃ m, m < n ∧ CallDepth fs m g := by
  induction hp generalizing n with
  | single he => exact h.edge he
  | cons he _ ih =>
      obtain ⟨m, hm, hd⟩ := h.edge he
      obtain ⟨k, hk, hd'⟩ := ih hd
      exact ⟨k, Nat.lt_trans hk hm, hd'⟩

theorem CallDepth.no_cycle {fs} (n : Nat) (f : FuncId) (h : CallDepth fs n f) :
    ¬ CallPath fs f f := by
  intro hp
  obtain ⟨m, hm, hd⟩ := h.path hp
  exact CallDepth.no_cycle m f hd hp
termination_by n

def FiniteCalls (fs : Array Func) : Prop :=
  ∀ f ∈ fs.toList, CallDepth fs fs.size f.id

instance (fs : Array Func) : Decidable (FiniteCalls fs) :=
  inferInstanceAs (Decidable (∀ f ∈ fs.toList, CallDepth fs fs.size f.id))

end GoLean.GoCore.RecoveryTyping
