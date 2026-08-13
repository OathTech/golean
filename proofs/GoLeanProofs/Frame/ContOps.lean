import GoLeanProofs.Frame.Sim

/-!
# The executable frame theorem, module 3: continuation-op commutation
(design of record `docs/2026-08-13_executable-frame-theorem.md`)

Renaming commutes with every continuation/environment helper the
`stepFn` arm induction consults: environment lookup/declare/pushScope,
the defer push, panic passthrough, the recover walk
(`recoverThroughWrappers`/`recoverResult` — structural walks over
`Cont`, proved by a uniform per-arm induction), the chain bookkeeping
(`markNewestRecovered`/`chainNewestRecovered`), and the panic payload
coercions. Each lemma is a plain commutation square over the carriers
of `Rename.lean`; no `ShiftSpec` hypothesis appears anywhere — these
helpers never allocate and never compare addresses, so neither
injectivity nor the shift law plays a role.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable (ρ : Nat → Nat)

/-! ## Environment operations -/

theorem scope_lookup_ren (sc : Scope) (id : String) :
    Scope.lookup (renameScope ρ sc) id
      = (Scope.lookup sc id).map (renameLoc ρ) := by
  induction sc with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨name, loc⟩ := p
      simp only [renameScope, List.map_cons] at ih ⊢
      simp only [Scope.lookup]
      cases name == id with
      | false => simpa using ih
      | true => simp

theorem localEnv_lookup_ren (env : LocalEnv) (id : String) :
    LocalEnv.lookup (renameEnv ρ env) id
      = (LocalEnv.lookup env id).map (renameLoc ρ) := by
  induction env with
  | nil => rfl
  | cons sc outer ih =>
      simp only [renameEnv, List.map_cons] at ih ⊢
      simp only [LocalEnv.lookup]
      rw [scope_lookup_ren]
      cases Scope.lookup sc id with
      | none => simpa using ih
      | some l => simp

theorem localEnv_declare_ren (env : LocalEnv) (id : String) (l : Loc) :
    renameEnv ρ (LocalEnv.declare env id l)
      = LocalEnv.declare (renameEnv ρ env) id (renameLoc ρ l) := by
  cases env with
  | nil => rfl
  | cons scope outer => rfl

theorem localEnv_pushScope_ren (env : LocalEnv) :
    renameEnv ρ (LocalEnv.pushScope env) = LocalEnv.pushScope (renameEnv ρ env) :=
  rfl

/-! ## Defer registration and panic passthrough -/

theorem deferrableCallee_ren (v : GoValue) :
    deferrableCallee (renameValue ρ v) = deferrableCallee v := by
  cases v <;> simp [renameValue, deferrableCallee]

theorem pushDefer_ren (d : GoValue × List GoValue) (k : Cont) :
    pushDefer (renameDefer ρ d) (renameCont ρ k)
      = (pushDefer d k).map (renameCont ρ) := by
  induction k
  all_goals
    first
    | rfl
    | (rename_i k ih
       simp only [renameCont, pushDefer]
       rw [ih]
       cases pushDefer d k with
       | none => rfl
       | some k' => rfl)

theorem panicPassthrough_ren (k : Cont) :
    panicPassthrough (renameCont ρ k)
      = (panicPassthrough k).map (renameCont ρ) := by
  cases k <;> rfl

/-! ## Panic-chain bookkeeping -/

theorem renameChain_append (a b : List PanicEntry) :
    renameChain ρ (a ++ b) = renameChain ρ a ++ renameChain ρ b := by
  simp [renameChain]

theorem renameChain_singleton (v : GoValue) (r : Bool) :
    renameChain ρ [⟨v, r⟩] = [⟨renameValue ρ v, r⟩] :=
  rfl

theorem markNewestRecovered_ren (chain : List PanicEntry) :
    markNewestRecovered (renameChain ρ chain)
      = (markNewestRecovered chain).map
          (fun p => (renameValue ρ p.1, renameChain ρ p.2)) := by
  induction chain with
  | nil => rfl
  | cons e rest ih =>
      cases rest with
      | nil =>
          cases he : e.recovered <;>
            simp [renameChain, renameEntry, markNewestRecovered, he]
      | cons r rest' =>
          simp only [renameChain, List.map_cons] at ih ⊢
          simp only [markNewestRecovered]
          rw [ih]
          cases markNewestRecovered (r :: rest') with
          | none => rfl
          | some p => obtain ⟨v, c⟩ := p; rfl

theorem chainNewestRecovered_ren (chain : List PanicEntry) :
    chainNewestRecovered (renameChain ρ chain) = chainNewestRecovered chain := by
  simp only [chainNewestRecovered, renameChain, List.getLast?_map]
  cases chain.getLast? with
  | none => rfl
  | some e => simp [renameEntry]

/-! ## The recover walk -/

theorem recoverThroughWrappers_ren (k : Cont) :
    recoverThroughWrappers (renameCont ρ k)
      = (recoverThroughWrappers k).map
          (fun p => (renameValue ρ p.1, renameCont ρ p.2)) := by
  induction k
  case stop => rfl
  case frame t te r ds k w ih =>
      cases w with
      | false => rfl
      | true =>
          simp only [renameCont, recoverThroughWrappers]
          rw [ih]
          cases recoverThroughWrappers k with
          | none => rfl
          | some p => obtain ⟨v, k'⟩ := p; rfl
  case panicResumeK chain k _ =>
      simp only [renameCont, recoverThroughWrappers]
      rw [markNewestRecovered_ren]
      cases markNewestRecovered chain with
      | none => rfl
      | some p => obtain ⟨v, c⟩ := p; rfl
  all_goals
    rename_i k ih
    simp only [renameCont, recoverThroughWrappers]
    rw [ih]
    cases recoverThroughWrappers k with
    | none => rfl
    | some p => obtain ⟨v, k'⟩ := p; rfl

theorem recoverResult_ren (k : Cont) :
    recoverResult (renameCont ρ k)
      = (renameValue ρ (recoverResult k).1, renameCont ρ (recoverResult k).2) := by
  induction k
  case stop => simp [recoverResult, renameCont, renameValue]
  case panicResumeK chain k _ => simp [recoverResult, renameCont, renameValue]
  case frame t te r ds k w ih =>
      cases w with
      | false =>
          simp only [renameCont, recoverResult]
          rw [recoverThroughWrappers_ren]
          cases recoverThroughWrappers k with
          | none => simp [renameValue, renameCont]
          | some p => obtain ⟨v, k'⟩ := p; rfl
      | true =>
          cases hrk : recoverResult k
          simp only [renameCont, recoverResult, hrk, ih]
  all_goals
    rename_i k ih
    cases hrk : recoverResult k
    simp only [renameCont, recoverResult, hrk, ih]

/-! ## Panic payload coercions -/

theorem runtimeErrorValue_ren (msg : String) :
    renameValue ρ (runtimeErrorValue msg) = runtimeErrorValue msg := by
  simp [runtimeErrorValue, renameValue]

theorem stringPanicValue_ren (msg : String) :
    renameValue ρ (stringPanicValue msg) = stringPanicValue msg := by
  simp [stringPanicValue, renameValue]

theorem panicPayload_ren (v : GoValue) :
    panicPayload (renameValue ρ v) = renameValue ρ (panicPayload v) := by
  cases v <;> simp [panicPayload, renameValue, runtimeErrorValue]

end GoLean.Frame
