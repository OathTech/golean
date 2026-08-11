import GoLeanProofs.ChanD

/-!
# The MEDIATED per-thread Language (channel-logic arc, slice 2)

The cell-mediated decomposition of the pool machine — the O1(b)
refinement the decomposition note recorded and slice 2's design note
(`docs/2026-08-11_channel-protocol-layer.md`) adopts: every delivered
channel value TRANSITS THE PHYSICAL CELL, where the state
interpretation (and hence an Iris invariant) can see it. This is what
makes a value protocol possible at all: on `LangD`'s `StepDC` the
∃-pool pairing rules allow phantom deliveries of arbitrary values with
no interpreted-state trace, so no ghost construction can pin a
delivered value (design note §1 — the slice's central finding).

Rule classes (design note §2b): the `StepE` lift, the marker strip and
`resumeThread` wake (verbatim machine semantics); DEPOSIT rules
(arriving/parked plain send, select send-clause) that push the value
into a `.base` channel cell CAP-RELAXED (raw `Heap.set`, `declaredTy`
preserved); DRAIN rules (arriving/parked plain recv, select
recv-clause) that dequeue the physical head; the `commitClause` select
commit; and the ∃-style `pairArrive`/`pairRelease` residue RESTRICTED
to non-`.base` cells (adversarial-seed channels at path locations —
no law targets them) and parked selects (select laws are deferred).
A parked PLAIN configuration on a `.base` cell has NO ∃-rule: its
completions are wake/deposit/drain only — every one physically
mediated. No spin rules and no state-preserving self-steps exist, so
parked configs at empty open cells are IRREDUCIBLE and the exit runs
at `.MaybeStuck` (design note §2c; `adequate_result` is
stuckness-independent and no exported statement mentions stuckness).

The envelope is wider than the machine's in the deposit direction
(cap-relaxed pushes at any open cell, any time) and in the kept
∃-residue — sound-conservative exactly as slice 1 argued: the
simulation direction is what the exit consumes, and the exports
quantify `execProg` alone. A `StepDM` bug can make a WP unprovable or
a simulation case fail, never a false exported statement provable.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open Iris.ProgramLogic.Language.Notation
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface
open Iris.BI

namespace GoLean.Iris

/-! ## The raw-cell round-trip kit (P-CL1-1's storeLoc round-trip
family, landed at `.base` scope as the simulation's state algebra) -/

/-- In-place heap update collapses: setting the same location twice
keeps only the second write. -/
theorem heap_set_set (h : Heap) (l : Loc) (c₁ c₂ : HeapCell) :
    Heap.set (Heap.set h l c₁) l c₂ = Heap.set h l c₂ := by
  induction h with
  | nil => simp [Heap.set]
  | cons hd rest ih =>
    obtain ⟨l', c'⟩ := hd
    by_cases hl : l' == l
    · simp [Heap.set, hl]
    · simp [Heap.set, hl, ih]

/-- Writing back the looked-up cell is the identity. -/
theorem heap_set_lookup_self {h : Heap} {l : Loc} {c : HeapCell}
    (hl : Heap.lookup h l = some c) :
    Heap.set h l c = h := by
  induction h with
  | nil => cases hl
  | cons hd rest ih =>
    obtain ⟨l', c'⟩ := hd
    by_cases heq : l' == l
    · simp [Heap.lookup, heq] at hl
      simp [Heap.set, heq, hl]
    · simp [Heap.lookup, heq] at hl
      simp [Heap.set, heq, ih hl]

/-- Lookup after set finds the written cell. -/
theorem heap_lookup_set (h : Heap) (l : Loc) (c : HeapCell) :
    Heap.lookup (Heap.set h l c) l = some c := by
  induction h with
  | nil => simp [Heap.set, Heap.lookup]
  | cons hd rest ih =>
    obtain ⟨l', c'⟩ := hd
    by_cases heq : l' == l
    · simp [Heap.set, heq, Heap.lookup]
    · simp [Heap.set, heq, Heap.lookup, ih]

/-- The raw `.base`-cell write (proof-layer; `declaredTy` untouched by
construction — callers pass the full cell). -/
def setCell (σ : ExecState) (a : Addr) (cell : HeapCell) : ExecState :=
  { σ with heap := Heap.set σ.heap (.base a) cell }

theorem setCell_setCell (σ : ExecState) (a : Addr) (c₁ c₂ : HeapCell) :
    setCell (setCell σ a c₁) a c₂ = setCell σ a c₂ := by
  simp [setCell, heap_set_set]

theorem setCell_self {σ : ExecState} {a : Addr} {c : HeapCell}
    (hl : Heap.lookup σ.heap (.base a) = some c) :
    setCell σ a c = σ := by
  simp [setCell, heap_set_lookup_self hl]

theorem lookup_setCell (σ : ExecState) (a : Addr) (c : HeapCell) :
    Heap.lookup (setCell σ a c).heap (.base a) = some c := by
  simp [setCell, heap_lookup_set]

/-- `chanCell` at a `.base` location, inverted to the heap binding. -/
theorem chanCell_base_inv {σ : ExecState} {a : Addr} {buf : Array GoValue}
    {cap : Nat} {closed : Bool}
    (h : chanCell σ (.base a) = .ok (buf, cap, closed)) :
    ∃ dt, Heap.lookup σ.heap (.base a)
      = some ⟨dt, .chanData buf cap closed⟩ := by
  unfold chanCell at h
  cases hl : Heap.lookup σ.heap (.base a) with
  | none =>
    simp [loadLoc, hl, stuck, throw, throwThe, MonadExceptOf.throw,
      Bind.bind, Except.bind] at h
  | some cell =>
    obtain ⟨dt, v⟩ := cell
    simp only [loadLoc, hl, Bind.bind, Except.bind] at h
    cases v <;> simp [stuck, throw, throwThe, MonadExceptOf.throw,
      Pure.pure, Except.pure] at h
    case chanData b c cl =>
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨dt, rfl⟩

/-- `chanCell` reads the raw cell just written. -/
theorem chanCell_setCell (σ : ExecState) (a : Addr) (dt : Option Ty)
    (buf : Array GoValue) (cap : Nat) (closed : Bool) :
    chanCell (setCell σ a ⟨dt, .chanData buf cap closed⟩) (.base a)
      = .ok (buf, cap, closed) := by
  unfold chanCell
  simp only [loadLoc, lookup_setCell, Bind.bind, Except.bind]
  rfl

/-- The normalizer is SUCCESS-IMPLIES-IDENTITY on `chanData` values:
no arm rewrites a channel cell payload — each either fails closed or
returns it unchanged (the `.defined` chain by induction;
`normalizeStructValueWith` on a non-struct is stuck). This is what
lets the machine's own `storeLoc` writes of `chanData` factor through
the raw `Heap.set` (`storeLoc_chanData_raw`). -/
theorem normalize_chanData_id : ∀ {fuel : Nat} {σ : ExecState} {ty : Ty}
    {buf : Array GoValue} {cap : Nat} {closed : Bool} {v : GoValue},
    normalizeValueForTyFuel fuel σ ty (.chanData buf cap closed) = .ok v →
    v = .chanData buf cap closed := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ ty buf cap closed v h
    simp [normalizeValueForTyFuel, unsupported, throw, throwThe,
      MonadExceptOf.throw] at h
  | succ fuel ih =>
    intro σ ty buf cap closed v h
    cases ty
    case defined name =>
      simp only [normalizeValueForTyFuel] at h
      cases hl : TypeEnv.lookup σ.types name with
      | none =>
        rw [hl] at h
        simp [unsupported, throw, throwThe, MonadExceptOf.throw] at h
      | some td =>
        rw [hl] at h
        cases td with
        | «alias» target => exact ih h
        | defined target => exact ih h
        | struct fields =>
          simp [normalizeStructValueWith, stuck, throw, throwThe,
            MonadExceptOf.throw] at h
        | unsupported feature =>
          simp [unsupported, throw, throwThe, MonadExceptOf.throw] at h
        | interfaceDef sigs =>
          simp [unsupported, throw, throwThe, MonadExceptOf.throw] at h
    all_goals
      (simp [normalizeValueForTyFuel, stuck, unsupported, throw, throwThe,
        MonadExceptOf.throw, Pure.pure, Except.pure] at h; try exact h.symm)

/-- A SUCCESSFUL machine `storeLoc` of a `chanData` value into a
`.base` cell is exactly the raw write: the declared-type normalization
and the untyped coercion are both identity on channel payloads when
they succeed (`normalize_chanData_id`; `coerceStoredValue`'s only
matching arm is the identity catch-all). -/
theorem storeLoc_chanData_raw {σ : ExecState} {a : Addr} {dt : Option Ty}
    {old : GoValue} {buf : Array GoValue} {cap : Nat} {closed : Bool}
    {σ' : ExecState}
    (hl : Heap.lookup σ.heap (.base a) = some ⟨dt, old⟩)
    (h : storeLoc σ (.base a) (.chanData buf cap closed) = .ok σ') :
    σ' = setCell σ a ⟨dt, .chanData buf cap closed⟩ := by
  simp only [storeLoc] at h
  rw [hl] at h
  cases dt with
  | none =>
    have hco : coerceStoredValue old (.chanData buf cap closed)
        = .ok (.chanData buf cap closed) := by
      cases old <;> rfl
    simp only [hco, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq] at h
    exact h.symm ▸ rfl
  | some ty =>
    cases hn : normalizeValueForTy σ ty (.chanData buf cap closed) with
    | error e =>
      simp only [normalizeValueForTy] at hn
      simp only [normalizeValueForTy, hn, Bind.bind, Except.bind] at h
      simp at h
    | ok w =>
      have hid : w = .chanData buf cap closed :=
        normalize_chanData_id (by simpa [normalizeValueForTy] using hn)
      subst hid
      simp only [normalizeValueForTy] at hn
      simp only [normalizeValueForTy, hn, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Except.ok.injEq] at h
      exact h.symm ▸ rfl

/-- `storeLoc` of a `chanData` value into an EXISTING untyped
(`declaredTy = none`) `.base` cell always succeeds, at the raw write —
the machine-real channel-cell shape (`makeChan` allocates untyped). -/
theorem storeLoc_chanData_ok {σ : ExecState} {a : Addr}
    {old : GoValue} {buf : Array GoValue} {cap : Nat} {closed : Bool}
    (hl : Heap.lookup σ.heap (.base a) = some ⟨none, old⟩) :
    storeLoc σ (.base a) (.chanData buf cap closed)
      = .ok (setCell σ a ⟨none, .chanData buf cap closed⟩) := by
  simp only [storeLoc]
  rw [hl]
  have hco : coerceStoredValue old (.chanData buf cap closed)
      = .ok (.chanData buf cap closed) := by
    cases old <;> rfl
  simp only [hco, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

/-! ## Array facts (the head-and-refill algebra) -/

theorem array_push_getElem?_zero_of_nonempty {buf : Array GoValue}
    {v x : GoValue} (h : buf[0]? = some v) : (buf.push x)[0]? = some v := by
  have hlt : 0 < buf.size := by
    cases Nat.lt_or_ge 0 buf.size with
    | inl h' => exact h'
    | inr h' =>
      rw [Array.getElem?_eq_none_iff.mpr (by omega)] at h
      simp at h
  rw [Array.getElem?_eq_getElem (by simp [Array.size_push])]
  rw [Array.getElem?_eq_getElem hlt] at h
  injection h with h
  simp [Array.getElem_push, hlt, h]

theorem array_push_getElem?_zero_empty {x : GoValue} {buf : Array GoValue}
    (h : buf[0]? = none) : (buf.push x)[0]? = some x := by
  have hz : buf.size = 0 := by
    have := Array.getElem?_eq_none_iff.mp h
    omega
  have hb : buf = #[] := by
    cases buf with
    | mk l =>
      cases l with
      | nil => rfl
      | cons a t => simp [Array.size] at hz
  subst hb
  rfl

/-- `eraseIdx! 0` commutes with a tail `push` on a nonempty array
(the gc head-and-refill rotate, decomposed). -/
theorem array_eraseIdx_push {buf : Array GoValue} {x : GoValue}
    (h : 0 < buf.size) :
    (buf.push x).eraseIdx! 0 = (buf.eraseIdx! 0).push x := by
  have h' : 0 < (buf.push x).size := by simp [Array.size_push]
  simp only [Array.eraseIdx!, dif_pos h, dif_pos h']
  apply Array.ext'
  simp only [Array.toList_eraseIdx, Array.toList_push]
  rw [List.eraseIdx_append_of_lt_length (by simpa using h)]

/-! ## The mediated per-thread relation -/

/-- The channel cell a pairing candidate operates on: the would-block
shape's own loc for plain ops; the arriving select's picked clause loc
for select arrivals. This is exactly the loc `applyPairing` reads
(`chanCell s loc`), so restricting the ∃-residue rules by it is the
precise base/non-base split. -/
def candLoc (bc : Config) (cand : Nat × PairTarget) : Option Loc :=
  match bc with
  | .blockedSend (some loc) _ _ => some loc
  | .blockedRecv (some loc) _ _ _ _ => some loc
  | .blockedSelect evs _ _ =>
      match evs[cand.1]? with
      | some (.recvEv chv _ _ _) => chanValueLoc chv
      | some (.sendEv chv _ _ _) => chanValueLoc chv
      | none => none
  | _ => none

/-- Is this loc a `.base` address? -/
def locIsBase : Loc → Bool
  | .base _ => true
  | _ => false

/-- May this PARKED shape take the ∃-residue `pairReleaseNB` rule?
Parked PLAIN shapes on `.base` cells may NOT — their completions are
the mediated wake/deposit/drain rules only, which is what makes the
value protocol (and the send-side "completed ⇒ deposited" tie) sound.
Parked selects keep the wide ∃-release (select laws deferred,
P-CL2-5); non-base and nil parks keep it (no law targets them). -/
def parkedReleaseNB : Config → Bool
  | .blockedSend (some (.base _)) _ _ => false
  | .blockedSend _ _ _ => true
  | .blockedRecv (some (.base _)) _ _ _ _ => false
  | .blockedRecv _ _ _ _ _ => true
  | .blockedSelect _ _ _ => true
  | .blockedSync _ _ _ _ => true
  | _ => false

/-- The MEDIATED per-thread relation (module docstring; design note
§2b). Proof infrastructure over the machine's public helpers, exactly
like `StepDC` — the machine itself is untouched. -/
inductive StepDM : Config → ExecState → Config → ExecState → List Config → Prop where
  /-- Sequential steps + the spawn (`StepE`), verbatim. -/
  | lift {c σ c' σ' efs} : StepE c σ c' σ' efs → StepDM c σ c' σ' efs
  /-- The post-spawn marker strip. -/
  | strip {k σ} : StepDM (.spawned k) σ (.next k) σ []
  /-- The parked re-attempt against the cell (machine `resumeThread`). -/
  | wake {c σ c' σ'} :
      isBlockedConfig c = true →
      resumeThread σ c = .ok (c', σ') →
      StepDM c σ c' σ' []
  /-- An arriving plain SEND deposits its normalized value into the
  `.base` cell CAP-RELAXED and completes (the mediated half of every
  send-arriving pairing; also a spontaneous wider-envelope member). -/
  | sendDeposit {σ : ExecState} {elem : Ty} {chv vv v' : GoValue}
      {env : LocalEnv} {k : Cont} {a : Addr} {dt : Option Ty}
      {buf : Array GoValue} {cap : Nat} :
      chanValueLoc chv = some (.base a) →
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap false⟩ →
      normalizeValueForTy σ elem vv = .ok v' →
      StepDM (.retV vv (.chanStK (.send elem) [chv] [] env k)) σ
        (.next k) (setCell σ a ⟨dt, .chanData (buf.push v') cap false⟩) []
  /-- A parked plain sender deposits cap-relaxed and completes — the
  ONLY completion class for a `.base`-parked sender besides `wake`, so
  "completed ⇒ the value entered the buffer or the closed-panic fired"
  holds on this carrier (unlike `StepDC`, where the phantom release
  completed a parked sender with no deposit). -/
  | parkedSendDeposit {σ : ExecState} {v' : GoValue} {k : Cont} {a : Addr}
      {dt : Option Ty} {buf : Array GoValue} {cap : Nat} :
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap false⟩ →
      StepDM (.blockedSend (some (.base a)) v' k) σ
        (.next k) (setCell σ a ⟨dt, .chanData (buf.push v') cap false⟩) []
  /-- An arriving plain RECEIVE drains the physical head of its `.base`
  cell — the delivered value IS the buffer head (the value-protocol
  hinge). Successor via the machine's own delivery entry. -/
  | recvDrain {σ : ExecState} {targets : List Assignee} {elem : Ty}
      {chv : GoValue} {env : LocalEnv} {k : Cont} {a : Addr} {dt : Option Ty}
      {v : GoValue} {buf : Array GoValue} {cap : Nat} {closed : Bool}
      {c' : Config} {σ' : ExecState} :
      chanValueLoc chv = some (.base a) →
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap closed⟩ →
      buf[0]? = some v →
      resumeRecvDelivery (setCell σ a ⟨dt, .chanData (buf.eraseIdx! 0) cap closed⟩)
        v true targets env k = .ok (c', σ') →
      StepDM (.retV chv (.chanStK (.recv targets elem) [] [] env k)) σ c' σ' []
  /-- A parked plain receiver drains the physical head. -/
  | parkedRecvDrain {σ : ExecState} {targets : List Assignee} {elem : Ty}
      {env : LocalEnv} {k : Cont} {a : Addr} {dt : Option Ty} {v : GoValue}
      {buf : Array GoValue} {cap : Nat} {closed : Bool}
      {c' : Config} {σ' : ExecState} :
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap closed⟩ →
      buf[0]? = some v →
      resumeRecvDelivery (setCell σ a ⟨dt, .chanData (buf.eraseIdx! 0) cap closed⟩)
        v true targets env k = .ok (c', σ') →
      StepDM (.blockedRecv (some (.base a)) targets elem env k) σ c' σ' []
  /-- An arriving select's SEND clause deposits cap-relaxed and commits
  its body (`evs` is a function of σ and the config's own operands). -/
  | selSendDeposit {σ : ExecState} {clauses : List (SelectClauseHead × Stmt)}
      {default? : Option Stmt} {done : List GoValue} {v : GoValue}
      {env : LocalEnv} {k : Cont} {evs : List EvClause} {ci : Nat}
      {chv vv : GoValue} {selem : Ty} {body : Stmt} {v' : GoValue}
      {a : Addr} {dt : Option Ty} {buf : Array GoValue} {cap : Nat} :
      evalClauses clauses ((v :: done).reverse) = .ok evs →
      evs[ci]? = some (.sendEv chv vv selem body) →
      chanValueLoc chv = some (.base a) →
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap false⟩ →
      normalizeValueForTy σ selem vv = .ok v' →
      StepDM (.retV v (.selectOpsK clauses default? done [] env k)) σ
        (.exec body env k) (setCell σ a ⟨dt, .chanData (buf.push v') cap false⟩) []
  /-- A parked select's SEND clause deposits cap-relaxed and commits. -/
  | parkedSelSendDeposit {σ : ExecState} {evs : List EvClause}
      {env : LocalEnv} {k : Cont} {ci : Nat} {chv vv : GoValue} {selem : Ty}
      {body : Stmt} {v' : GoValue} {a : Addr} {dt : Option Ty}
      {buf : Array GoValue} {cap : Nat} :
      evs[ci]? = some (.sendEv chv vv selem body) →
      chanValueLoc chv = some (.base a) →
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap false⟩ →
      normalizeValueForTy σ selem vv = .ok v' →
      StepDM (.blockedSelect evs env k) σ
        (.exec body env k) (setCell σ a ⟨dt, .chanData (buf.push v') cap false⟩) []
  /-- An arriving select's RECV clause drains the physical head. -/
  | selRecvDrain {σ : ExecState} {clauses : List (SelectClauseHead × Stmt)}
      {default? : Option Stmt} {done : List GoValue} {v : GoValue}
      {env : LocalEnv} {k : Cont} {evs : List EvClause} {ci : Nat}
      {chv : GoValue} {targets : List Assignee} {selem : Ty} {body : Stmt}
      {a : Addr} {dt : Option Ty} {hd : GoValue} {buf : Array GoValue}
      {cap : Nat} {closed : Bool} {c' : Config} {σ' : ExecState} :
      evalClauses clauses ((v :: done).reverse) = .ok evs →
      evs[ci]? = some (.recvEv chv targets selem body) →
      chanValueLoc chv = some (.base a) →
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap closed⟩ →
      buf[0]? = some hd →
      selectRecvDelivery (setCell σ a ⟨dt, .chanData (buf.eraseIdx! 0) cap closed⟩)
        hd true targets body env k = .ok (c', σ') →
      StepDM (.retV v (.selectOpsK clauses default? done [] env k)) σ c' σ' []
  /-- A parked select's RECV clause drains the physical head. -/
  | parkedSelRecvDrain {σ : ExecState} {evs : List EvClause}
      {env : LocalEnv} {k : Cont} {ci : Nat} {chv : GoValue}
      {targets : List Assignee} {selem : Ty} {body : Stmt} {a : Addr}
      {dt : Option Ty} {hd : GoValue} {buf : Array GoValue} {cap : Nat}
      {closed : Bool} {c' : Config} {σ' : ExecState} :
      evs[ci]? = some (.recvEv chv targets selem body) →
      chanValueLoc chv = some (.base a) →
      Heap.lookup σ.heap (.base a) = some ⟨dt, .chanData buf cap closed⟩ →
      buf[0]? = some hd →
      selectRecvDelivery (setCell σ a ⟨dt, .chanData (buf.eraseIdx! 0) cap closed⟩)
        hd true targets body env k = .ok (c', σ') →
      StepDM (.blockedSelect evs env k) σ c' σ' []
  /-- The ∃-residue ARRIVING rule (`StepDC.pairArrive` restricted to
  NON-`.base` pairing cells — adversarial-seed path-loc channels; no
  law targets them). -/
  | pairArriveNB {c σ} {threads : Array Config} {i : Nat} {bc : Config}
      {cs : List (Nat × PairTarget)} {idx : Nat}
      {ts' : Array Config} {σ'' : ExecState} {c' : Config} :
      threads[i]? = some c →
      isBlockedConfig c = false →
      PairAnalysis σ threads i c bc cs →
      (hidx : idx < cs.length) →
      (∀ l, candLoc bc cs[idx] = some l → locIsBase l = false) →
      applyPairing σ threads i bc cs[idx] = .ok (ts', σ'') →
      ts'[i]? = some c' →
      StepDM c σ c' σ'' []
  /-- The ∃-residue RELEASE rule (`StepDC.pairRelease` restricted by
  `parkedReleaseNB`: parked PLAIN shapes on `.base` cells are
  excluded — no phantom completions, no phantom deliveries, no spins
  for the shapes the protocol laws govern). -/
  | pairReleaseNB {p : Config} {σ'' : ExecState} {p' : Config} :
      isBlockedConfig p = true →
      parkedReleaseNB p = true →
      (∃ (σ₀ : ExecState) (threads : Array Config) (i j : Nat)
         (bc : Config) (cs : List (Nat × PairTarget)) (idx : Nat)
         (ts' : Array Config) (hidx : idx < cs.length),
         threads[j]? = some p ∧ i ≠ j ∧
           applyPairing σ₀ threads i bc cs[idx] = .ok (ts', σ'')
           ∧ ts'[j]? = some p') →
      StepDM p σ'' p' σ'' []
  /-- The L2-picked CELL commit of a multi-ready select arrival
  (`StepDC.selCommit` verbatim — `commitClause` reads the real cell,
  so it is value-clean by construction). -/
  | selCommitCell {c : Config} {σ : ExecState} {cl : EvClause}
      {env : LocalEnv} {k : Cont} {c' : Config} {σ' : ExecState} :
      (∃ (threads : Array Config) (i : Nat) (os : List ArrivalOutcome)
         (sel : Nat),
         threads[i]? = some c
           ∧ arrivalCases σ threads i c = .ok (.multi os)
           ∧ os[sel]? = some (.commit cl env k)) →
      commitClause σ env k cl = .ok (c', σ') →
      StepDM c σ c' σ' []

/-- Per-goroutine configuration on the MEDIATED concurrent carrier. -/
structure PoolCfgDM where
  c : Config

private theorem spawnPlanDM_toVal_aux {c : Config}
    {p : GoValue × List GoValue × Cont} (h : spawnPlan c = some p) :
    (match c with
      | Config.next Cont.stop => some ()
      | _ => (none : Option Unit)) = none := by
  match c, h with
  | .retV _ (.goCalleeK [] _ _), _ => rfl
  | .retV _ (.goArgsK _ _ [] _ _), _ => rfl

instance : ToVal PoolCfgDM Unit where
  toVal e := match e.c with | .next .stop => some () | _ => none
  ofVal _ := ⟨.next .stop⟩
  coe_of_toVal_eq_some {e v} h := by
    obtain ⟨c⟩ := e
    cases c with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

/-- The mediated primitive step. -/
inductive GoPrimStepDM :
    PoolCfgDM × ExecState → List Unit → PoolCfgDM × ExecState × List PoolCfgDM → Prop where
  | step {c σ c' σ' efs} : StepDM c σ c' σ' efs →
      GoPrimStepDM (⟨c⟩, σ) [] (⟨c'⟩, σ', efs.map PoolCfgDM.mk)

instance : PrimStep PoolCfgDM ExecState (List Unit) where
  primStep := GoPrimStepDM

private theorem blockedDM_toVal_aux {c : Config}
    (h : isBlockedConfig c = true) :
    (match c with
      | Config.next Cont.stop => some ()
      | _ => (none : Option Unit)) = none := by
  match c, h with
  | .blockedSend _ _ _, _ => rfl
  | .blockedRecv _ _ _ _ _, _ => rfl
  | .blockedSelect _ _ _, _ => rfl
  | .blockedSync _ _ _ _, _ => rfl

private theorem toValDM_aux_of_ne {c : Config} (h : c ≠ .next .stop) :
    (match c with
      | Config.next Cont.stop => some ()
      | _ => (none : Option Unit)) = none := by
  cases c <;> try rfl
  case next k => cases k <;> first | rfl | exact absurd rfl h

private theorem arrivalDM_terminal {σ : ExecState} {threads : Array Config}
    {i : Nat} {a : ArrivalAnalysis}
    (h : arrivalCases σ threads i (.next .stop) = .ok a) : a = .cellPath := by
  unfold arrivalCases at h
  simp only [pure_eq_ok] at h
  injection h with h
  exact h.symm

instance : Language PoolCfgDM ExecState Unit Unit where
  val_stuck h := by
    cases h with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq => cases sq <;> rfl
        | spawn hsp hstep => exact spawnPlanDM_toVal_aux hsp
      | strip => rfl
      | wake hblk _ => exact blockedDM_toVal_aux hblk
      | sendDeposit _ _ _ => rfl
      | parkedSendDeposit _ => rfl
      | recvDrain _ _ _ _ => rfl
      | parkedRecvDrain _ _ _ => rfl
      | selSendDeposit _ _ _ _ _ => rfl
      | parkedSelSendDeposit _ _ _ _ => rfl
      | selRecvDrain _ _ _ _ _ _ => rfl
      | parkedSelRecvDrain _ _ _ _ _ => rfl
      | pairReleaseNB hblk _ _ => exact blockedDM_toVal_aux hblk
      | pairArriveNB hti hblk hpair hidx hnb happly hproj =>
        refine toValDM_aux_of_ne ?_
        rintro rfl
        rcases hpair with hs | ⟨os, sel, hm, -⟩
        · cases arrivalDM_terminal hs
        · cases arrivalDM_terminal hm
      | selCommitCell hex _ =>
        obtain ⟨threads, i, os, sel, hti, hm, -⟩ := hex
        refine toValDM_aux_of_ne ?_
        rintro rfl
        cases arrivalDM_terminal hm

instance : Inhabited PoolCfgDM := ⟨⟨.next .stop⟩⟩

/-! ## The simulation: every pool-machine step is 1–2 erased DM-steps -/

/-- One DM-step of the thread at position `j` of a pool list, as an
erased thread-pool step (LangD's `poolStepD_at`, on this carrier). -/
theorem poolStepDM_at {l : List PoolCfgDM} {j : Nat} {e e' : PoolCfgDM}
    {σ σ' : ExecState} {efs : List PoolCfgDM}
    (hj : l[j]? = some e)
    (hprim : GoPrimStepDM (e, σ) [] (e', σ', efs)) :
    ((l, σ) : List PoolCfgDM × ExecState) -·->ₜₚ (l.set j e' ++ efs, σ') := by
  have hlt : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hget : l[j] = e := (List.getElem?_eq_some_iff.mp hj).2
  have hdec : l = l.take j ++ e :: l.drop (j + 1) := by
    rw [← hget, List.getElem_cons_drop hlt, List.take_append_drop]
  have hdec' : l.set j e' ++ efs
      = (l.take j ++ e' :: l.drop (j + 1)) ++ efs := by
    rw [List.set_eq_take_append_cons_drop]
    simp [hlt]
  refine ⟨[], ?_⟩
  have hpair : ((l, σ) : List PoolCfgDM × ExecState)
      = (l.take j ++ e :: l.drop (j + 1), σ) := by rw [← hdec]
  rw [hdec', hpair]
  exact Language.Step.of_primStep hprim (t₁ := l.take j) (t₂ := l.drop (j + 1))

/-- The pool list of a `MultiConfig` on the DM-carrier. -/
def poolOfDM (m : MultiConfig) : List PoolCfgDM × ExecState :=
  (m.threads.toList.map PoolCfgDM.mk, m.shared)

private theorem poolOfDM_get {threads : Array Config} {i : Nat} {c : Config}
    (hti : threads[i]? = some c) :
    (threads.toList.map PoolCfgDM.mk)[i]? = some ⟨c⟩ := by
  simp [List.getElem?_map, Array.getElem?_toList, hti]

/-- Two mediated steps at distinct indices compose to the machine
pairing's two-point pool update (the list surgery, mechanized once).
Step 1 runs the thread at `j₁` (`e₁ → e₁'`, `σ → σ₁`), step 2 the
thread at `j₂` (`e₂ → e₂'`, `σ₁ → σ₂`). -/
theorem poolStepDM_two {l : List PoolCfgDM} {j₁ j₂ : Nat}
    {e₁ e₁' e₂ e₂' : PoolCfgDM} {σ σ₁ σ₂ : ExecState}
    (hne : j₁ ≠ j₂)
    (hj₁ : l[j₁]? = some e₁)
    (hj₂ : l[j₂]? = some e₂)
    (h₁ : GoPrimStepDM (e₁, σ) [] (e₁', σ₁, []))
    (h₂ : GoPrimStepDM (e₂, σ₁) [] (e₂', σ₂, [])) :
    ((l, σ) : List PoolCfgDM × ExecState) -·->ₜₚ*
      ((l.set j₁ e₁').set j₂ e₂', σ₂) := by
  have hstep1 := poolStepDM_at hj₁ h₁
  have hj₂' : (l.set j₁ e₁')[j₂]? = some e₂ := by
    rw [List.getElem?_set_ne hne]
    exact hj₂
  have hstep2 := poolStepDM_at hj₂' h₂
  simp only [List.append_nil] at hstep1 hstep2
  exact .head hstep1 (.tail .refl hstep2)

/-- `(l₁ ++ [x]).reverse = [a, b]` inversion for the two-operand apply. -/
private theorem reverse_pair_inv {v x y : GoValue} {done : List GoValue}
    (h : (v :: done).reverse = [x, y]) : v = y ∧ done = [x] := by
  have h' := congrArg List.reverse h
  simp at h'
  exact ⟨h'.1, h'.2⟩

private theorem reverse_singleton_inv {v x : GoValue} {done : List GoValue}
    (h : (v :: done).reverse = [x]) : v = x ∧ done = [] := by
  have h' := congrArg List.reverse h
  simp at h'
  exact ⟨h'.1, h'.2⟩

private theorem beq_false_ne {j i : Nat} (h : (j == i) = false) : j ≠ i := by
  intro he
  subst he
  simp at h

private theorem array_empty_of_getElem?_none {buf : Array GoValue}
    (h : buf[0]? = none) : buf = #[] := by
  have hz : buf.size = 0 := by
    have := Array.getElem?_eq_none_iff.mp h
    omega
  cases buf with
  | mk l =>
    cases l with
    | nil => rfl
    | cons a t => simp [Array.size] at hz

/-- Membership in the RECV-side waiter scan: the target is a parked
plain receiver or a parked select's recv clause ON THE SAME CELL —
the provenance fact the mediated decomposition needs (`applyPairing`
wildcards the partner's channel; the scan is what pins it). -/
theorem recvSideWaiters_mem {threads : Array Config} {i : Nat} {loc : Loc}
    {cn : Nat} {tgt : PairTarget}
    (h : (cn, tgt) ∈ recvSideWaiters threads i loc) :
    (∃ j targets elem envr kr, tgt = .opWaiter j ∧ j ≠ i
        ∧ threads[j]? = some (.blockedRecv (some loc) targets elem envr kr))
    ∨ (∃ j ci evs envs ks chv targets elem body,
        tgt = .selectWaiter j ci ∧ j ≠ i
        ∧ threads[j]? = some (.blockedSelect evs envs ks)
        ∧ evs[ci]? = some (.recvEv chv targets elem body)
        ∧ chanValueLoc chv = some loc) := by
  unfold recvSideWaiters at h
  rw [List.mem_flatMap] at h
  obtain ⟨j, hjr, hmem⟩ := h
  by_cases hji : (j == i) = true
  · simp [hji] at hmem
  · rw [Bool.not_eq_true] at hji
    simp only [hji, Bool.false_eq_true, if_false] at hmem
    split at hmem
    · rename_i loc' targets elem envr kr hjt
      split at hmem
      · rename_i hleq
        have hleq' : loc' = loc := eq_of_beq hleq
        subst hleq'
        simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨-, rfl⟩ := hmem
        exact .inl ⟨j, targets, elem, envr, kr, rfl, beq_false_ne hji, hjt⟩
      · simp at hmem
    · rename_i evs envs ks hjt
      rw [List.mem_filterMap] at hmem
      obtain ⟨ci, hcir, hf⟩ := hmem
      split at hf
      · rename_i chv targets elem body heq
        split at hf
        · rename_i hcl
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl⟩ := hf
          exact .inr ⟨j, ci, evs, envs, ks, chv, targets, elem, body,
            rfl, beq_false_ne hji, hjt, heq, eq_of_beq hcl⟩
        · cases hf
      · cases hf
    · simp at hmem

/-- Membership in the SEND-side waiter scan (the mirror). -/
theorem sendSideWaiters_mem {threads : Array Config} {i : Nat} {loc : Loc}
    {cn : Nat} {tgt : PairTarget}
    (h : (cn, tgt) ∈ sendSideWaiters threads i loc) :
    (∃ j vs ks, tgt = .opWaiter j ∧ j ≠ i
        ∧ threads[j]? = some (.blockedSend (some loc) vs ks))
    ∨ (∃ j ci evs envs ks chv vv elem body,
        tgt = .selectWaiter j ci ∧ j ≠ i
        ∧ threads[j]? = some (.blockedSelect evs envs ks)
        ∧ evs[ci]? = some (.sendEv chv vv elem body)
        ∧ chanValueLoc chv = some loc) := by
  unfold sendSideWaiters at h
  rw [List.mem_flatMap] at h
  obtain ⟨j, hjr, hmem⟩ := h
  by_cases hji : (j == i) = true
  · simp [hji] at hmem
  · rw [Bool.not_eq_true] at hji
    simp only [hji, Bool.false_eq_true, if_false] at hmem
    split at hmem
    · rename_i loc' vs ks hjt
      split at hmem
      · rename_i hleq
        have hleq' : loc' = loc := eq_of_beq hleq
        subst hleq'
        simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨-, rfl⟩ := hmem
        exact .inl ⟨j, vs, ks, rfl, beq_false_ne hji, hjt⟩
      · simp at hmem
    · rename_i evs envs ks hjt
      rw [List.mem_filterMap] at hmem
      obtain ⟨ci, hcir, hf⟩ := hmem
      split at hf
      · rename_i chv vv selem body heq
        split at hf
        · rename_i hcl
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl⟩ := hf
          exact .inr ⟨j, ci, evs, envs, ks, chv, vv, selem, body,
            rfl, beq_false_ne hji, hjt, heq, eq_of_beq hcl⟩
        · cases hf
      · cases hf
    · simp at hmem

/-- `chanArrivalPlan` SEND inversion, strengthened over ChanD's with
the facts the mediated decomposition consumes: the operand shape, the
OPEN cell, and the candidate list's scan identity. -/
theorem chanArrivalPlan_send_inv_full {σ : ExecState} {threads : Array Config}
    {i : Nat} {elem : Ty} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {bc : Config} {cs : List (Nat × PairTarget)}
    (h : chanArrivalPlan σ threads i (.send elem) vs env k
      = .ok (some (bc, cs))) :
    ∃ (chv vv : GoValue) (loc : Loc) (v'' : GoValue) (buf : Array GoValue)
      (cap : Nat),
      vs = [chv, vv]
      ∧ chanValueLoc chv = some loc
      ∧ chanCell σ loc = .ok (buf, cap, false)
      ∧ normalizeValueForTy σ elem vv = .ok v''
      ∧ bc = .blockedSend (some loc) v'' k
      ∧ cs = recvSideWaiters threads i loc := by
  match vs with
  | [] => simp [chanArrivalPlan, Pure.pure, Except.pure] at h
  | [chv] => simp [chanArrivalPlan, Pure.pure, Except.pure] at h
  | chv :: vv :: v₃ :: rest => simp [chanArrivalPlan, Pure.pure, Except.pure] at h
  | [chv, vv] =>
    simp only [chanArrivalPlan] at h
    cases hcl : chanValueLoc chv with
    | none => rw [hcl] at h; simp [Pure.pure, Except.pure] at h
    | some loc =>
      rw [hcl] at h
      by_cases hws : (recvSideWaiters threads i loc).isEmpty
      · simp [hws, Pure.pure, Except.pure] at h
      · rw [Bool.not_eq_true] at hws
        simp only [hws, Bool.false_eq_true, if_false, bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
        cases closed with
        | true => simp [Pure.pure, Except.pure] at h
        | false =>
          simp only [if_false, Bool.false_eq_true, bind_eq_ok] at h
          obtain ⟨v'', hn, h⟩ := h
          simp only [Pure.pure, Except.pure, Except.ok.injEq,
            Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨chv, vv, loc, v'', buf, cap, rfl, hcl, hcell, hn,
            h.1.symm, h.2.symm⟩

/-- `chanArrivalPlan` RECV inversion, strengthened (mirror). -/
theorem chanArrivalPlan_recv_inv_full {σ : ExecState} {threads : Array Config}
    {i : Nat} {targets : List Assignee} {elem : Ty} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {bc : Config} {cs : List (Nat × PairTarget)}
    (h : chanArrivalPlan σ threads i (.recv targets elem) vs env k
      = .ok (some (bc, cs))) :
    ∃ (chv : GoValue) (loc : Loc) (buf : Array GoValue) (cap : Nat),
      vs = [chv]
      ∧ chanValueLoc chv = some loc
      ∧ chanCell σ loc = .ok (buf, cap, false)
      ∧ bc = .blockedRecv (some loc) targets elem env k
      ∧ cs = sendSideWaiters threads i loc := by
  match vs with
  | [] => simp [chanArrivalPlan, Pure.pure, Except.pure] at h
  | chv :: v₂ :: rest => simp [chanArrivalPlan, Pure.pure, Except.pure] at h
  | [chv] =>
    simp only [chanArrivalPlan] at h
    cases hcl : chanValueLoc chv with
    | none => rw [hcl] at h; simp [Pure.pure, Except.pure] at h
    | some loc =>
      rw [hcl] at h
      by_cases hws : (sendSideWaiters threads i loc).isEmpty
      · simp [hws, Pure.pure, Except.pure] at h
      · rw [Bool.not_eq_true] at hws
        simp only [hws, Bool.false_eq_true, if_false, bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, hcell, h⟩ := h
        cases closed with
        | true => simp [Pure.pure, Except.pure] at h
        | false =>
          simp only [Bool.false_eq_true, if_false, Pure.pure, Except.pure,
            Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨chv, loc, buf, cap, rfl, hcl, hcell, h.1.symm, h.2.symm⟩

/-- Successful `mapM` membership inversion (the readiness/outcome
provenance hinge). -/
private theorem mapM_ok_mem {α β : Type} {f : α → Except GoError β}
    {l : List α} {l' : List β} {b : β}
    (h : l.mapM f = .ok l') (hb : b ∈ l') :
    ∃ a ∈ l, f a = .ok b := by
  induction l generalizing l' with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases hb
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    simp only [bind_eq_ok] at h
    obtain ⟨y, hy, ys, hys, h⟩ := h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hb with rfl | hbmem
    · exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨a, hamem, hfa⟩ := ih hys hbmem
      exact ⟨a, List.mem_cons_of_mem _ hamem, hfa⟩

/-- The provenance of a waiter-carrying select-arrival candidate list
(design note §2d): the clause index, the OPEN cell the analysis read,
and the side-waiter scan the candidates came from. -/
def SelCandsSpec (σ : ExecState) (threads : Array Config) (i : Nat)
    (evs : List EvClause) (cands : List (Nat × PairTarget)) : Prop :=
  ∃ (ci : Nat) (ws : List (Nat × PairTarget)),
    cands = ws.map (fun w => (ci, w.2))
    ∧ ((∃ chv targets selem body loc buf cap,
          evs[ci]? = some (.recvEv chv targets selem body)
          ∧ chanValueLoc chv = some loc
          ∧ chanCell σ loc = .ok (buf, cap, false)
          ∧ ws = sendSideWaiters threads i loc)
       ∨ (∃ chv vv selem body loc buf cap,
          evs[ci]? = some (.sendEv chv vv selem body)
          ∧ chanValueLoc chv = some loc
          ∧ chanCell σ loc = .ok (buf, cap, false)
          ∧ ws = recvSideWaiters threads i loc))

/-- Provenance of one WAITER-CARRYING readiness element: the clause
index, its direction, its OPEN cell, and the scan its waiters came
from. Stated over the literal readiness body of `selectArrivalCases`
(definitional agreement — `exact` closes the gap). -/
private theorem readiness_provenance {σ : ExecState} {threads : Array Config}
    {i : Nat} {evs : List EvClause}
    {readiness : List (Nat × Bool × List (Nat × PairTarget))}
    (hmapM : List.mapM (fun (ci : Nat) => do
        match evs[ci]? with
        | some cl => do
            let cell ← clauseReady σ cl
            let ws ←
              match cl with
              | .recvEv chv _ _ _ =>
                  match chanValueLoc chv with
                  | some loc => do
                      let (_, _, closed) ← chanCell σ loc
                      if closed then pure ([] : List (Nat × PairTarget))
                      else pure (sendSideWaiters threads i loc)
                  | none => pure []
              | .sendEv chv _ _ _ =>
                  match chanValueLoc chv with
                  | some loc => do
                      let (_, _, closed) ← chanCell σ loc
                      if closed then pure ([] : List (Nat × PairTarget))
                      else pure (recvSideWaiters threads i loc)
                  | none => pure []
            return (ci, cell, ws)
        | none => return (ci, false, ([] : List (Nat × PairTarget))))
      (List.range evs.length) = .ok readiness)
    {ci : Nat} {cell : Bool} {ws : List (Nat × PairTarget)}
    (hmem : (ci, cell, ws) ∈ readiness)
    (hwsne : ws ≠ []) :
    (∃ chv targets selem body loc buf cap,
        evs[ci]? = some (.recvEv chv targets selem body)
        ∧ chanValueLoc chv = some loc
        ∧ chanCell σ loc = .ok (buf, cap, false)
        ∧ ws = sendSideWaiters threads i loc)
    ∨ (∃ chv vv selem body loc buf cap,
        evs[ci]? = some (.sendEv chv vv selem body)
        ∧ chanValueLoc chv = some loc
        ∧ chanCell σ loc = .ok (buf, cap, false)
        ∧ ws = recvSideWaiters threads i loc) := by
  obtain ⟨a, har, hfa⟩ := mapM_ok_mem hmapM hmem
  simp only [] at hfa
  split at hfa
  · rename_i cl heq
    simp only [bind_eq_ok] at hfa
    obtain ⟨cell', hcr, hfa⟩ := hfa
    split at hfa
    · rename_i chv targets selem body
      split at hfa
      · rename_i loc hcl
        simp only [bind_eq_ok] at hfa
        obtain ⟨⟨b₁, b₂, closed⟩, hcc, hfa⟩ := hfa
        cases closed with
        | true =>
          simp only [if_true, Bind.bind, Except.bind, Pure.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at hfa
          exact absurd hfa.2.2.symm hwsne
        | false =>
          simp only [Bool.false_eq_true, if_false, Pure.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at hfa
          obtain ⟨rfl, -, rfl⟩ := hfa
          exact .inl ⟨chv, targets, selem, body, loc, b₁, b₂, heq, hcl,
            hcc, rfl⟩
      · rename_i hcl
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at hfa
        exact absurd hfa.2.2.symm hwsne
    · rename_i chv vv selem body
      split at hfa
      · rename_i loc hcl
        simp only [bind_eq_ok] at hfa
        obtain ⟨⟨b₁, b₂, closed⟩, hcc, hfa⟩ := hfa
        cases closed with
        | true =>
          simp only [if_true, Bind.bind, Except.bind, Pure.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at hfa
          exact absurd hfa.2.2.symm hwsne
        | false =>
          simp only [Bool.false_eq_true, if_false, Pure.pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at hfa
          obtain ⟨rfl, -, rfl⟩ := hfa
          exact .inr ⟨chv, vv, selem, body, loc, b₁, b₂, heq, hcl, hcc, rfl⟩
      · rename_i hcl
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at hfa
        exact absurd hfa.2.2.symm hwsne
  · rename_i heq
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at hfa
    exact absurd hfa.2.2.symm hwsne

set_option maxHeartbeats 1600000 in
/-- `selectArrivalCases` inversion at `.single`: the analysis pins
`evalClauses`, the `bc` shape, and the candidates' provenance. -/
theorem selectArrivalCases_single_inv {σ : ExecState}
    {threads : Array Config} {i : Nat}
    {clauses : List (SelectClauseHead × Stmt)} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {bc : Config} {cands : List (Nat × PairTarget)}
    (h : selectArrivalCases σ threads i clauses vs env k
      = .ok (.single bc cands)) :
    ∃ evs, evalClauses clauses vs = .ok evs
      ∧ bc = .blockedSelect evs env k
      ∧ SelCandsSpec σ threads i evs cands := by
  unfold selectArrivalCases at h
  split at h
  · exact absurd h (by simp [Pure.pure, Except.pure])
  · split at h
    · exact absurd h (by simp [Pure.pure, Except.pure])
    · simp only [bind_eq_ok] at h
      obtain ⟨evs, hevs, readiness, hmapM, h⟩ := h
      refine ⟨evs, hevs, ?_⟩
      split at h
      · exact absurd h (by simp [Pure.pure, Except.pure])
      · rename_i ci cell ws hflt
        split at h
        · exact absurd h (by simp [Pure.pure, Except.pure])
        · rename_i hwse
          split at h
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · simp only [Pure.pure, Except.pure, Except.ok.injEq,
              ArrivalAnalysis.single.injEq] at h
            obtain ⟨hbc, hcands⟩ := h
            have hmem : (ci, cell, ws) ∈ readiness :=
              (List.mem_filter.mp (by rw [hflt]; exact List.mem_singleton_self _)).1
            have hwsne : ws ≠ [] := by
              intro hws
              subst hws
              simp at hwse
            exact ⟨hbc.symm, ci, ws, hcands.symm,
              readiness_provenance hmapM hmem hwsne⟩
      · exact absurd h (by
          split
          · simp [Pure.pure, Except.pure]
          · intro hcon
            simp only [bind_eq_ok] at hcon
            obtain ⟨os', -, hcon⟩ := hcon
            simp [Pure.pure, Except.pure] at hcon)

set_option maxHeartbeats 1600000 in
/-- `selectArrivalCases` inversion at a `.multi`-selected `.pair`
outcome: the same pins as the `.single` form. -/
theorem selectArrivalCases_multi_pair_inv {σ : ExecState}
    {threads : Array Config} {i : Nat}
    {clauses : List (SelectClauseHead × Stmt)} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {os : List ArrivalOutcome} {sel : Nat}
    {bc : Config} {cands : List (Nat × PairTarget)}
    (h : selectArrivalCases σ threads i clauses vs env k = .ok (.multi os))
    (hos : os[sel]? = some (.pair bc cands)) :
    ∃ evs, evalClauses clauses vs = .ok evs
      ∧ bc = .blockedSelect evs env k
      ∧ SelCandsSpec σ threads i evs cands := by
  unfold selectArrivalCases at h
  split at h
  · exact absurd h (by simp [Pure.pure, Except.pure])
  · split at h
    · exact absurd h (by simp [Pure.pure, Except.pure])
    · simp only [bind_eq_ok] at h
      obtain ⟨evs, hevs, readiness, hmapM, h⟩ := h
      refine ⟨evs, hevs, ?_⟩
      split at h
      · exact absurd h (by simp [Pure.pure, Except.pure])
      · rename_i ci cell ws hflt
        split at h
        · exact absurd h (by simp [Pure.pure, Except.pure])
        · split at h
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [Pure.pure, Except.pure])
      · rename_i ready hne₁ hne₂
        split at h
        · exact absurd h (by simp [Pure.pure, Except.pure])
        · simp only [bind_eq_ok] at h
          obtain ⟨os', hosM, h⟩ := h
          simp only [Pure.pure, Except.pure, Except.ok.injEq,
            ArrivalAnalysis.multi.injEq] at h
          subst h
          have hmemos : ArrivalOutcome.pair bc cands ∈ os' := by
            have hlt : sel < os'.length := (List.getElem?_eq_some_iff.mp hos).1
            have := (List.getElem?_eq_some_iff.mp hos).2
            rw [← this]
            exact List.getElem_mem hlt
          obtain ⟨r, hrr, hmk⟩ := mapM_ok_mem hosM hmemos
          obtain ⟨ci', cell', ws'⟩ := r
          simp only [] at hmk
          split at hmk
          · rename_i hwse'
            split at hmk
            · exact absurd hmk (by simp [Pure.pure, Except.pure])
            · exact absurd hmk (by simp [throw, throwThe, MonadExceptOf.throw])
          · rename_i hwse'
            split at hmk
            · exact absurd hmk (by simp [throw, throwThe, MonadExceptOf.throw])
            · simp only [Pure.pure, Except.pure, Except.ok.injEq,
                ArrivalOutcome.pair.injEq] at hmk
              obtain ⟨hbc, hcands⟩ := hmk
              have hmem : (ci', cell', ws') ∈ readiness :=
                (List.mem_filter.mp hrr).1
              have hwsne : ws' ≠ [] := by
                intro hws
                subst hws
                simp at hwse'
              exact ⟨hbc.symm, ci', ws', hcands.symm,
                readiness_provenance hmapM hmem hwsne⟩

/-- The config shape behind a `.single` arrival analysis. -/
private theorem arrivalCases_single_shape {σ : ExecState}
    {threads : Array Config} {i : Nat} {c : Config} {bc : Config}
    {cs : List (Nat × PairTarget)}
    (h : arrivalCases σ threads i c = .ok (.single bc cs)) :
    (∃ v op done env k, c = .retV v (.chanStK op done [] env k))
    ∨ (∃ v clauses default? done env k,
        c = .retV v (.selectOpsK clauses default? done [] env k)) := by
  unfold arrivalCases at h
  split at h
  · exact .inl ⟨_, _, _, _, _, rfl⟩
  · exact .inr ⟨_, _, _, _, _, _, rfl⟩
  · simp [Pure.pure, Except.pure] at h

/-- The config shape behind a `.multi` arrival analysis (select-only:
the chan-op route never multis). -/
private theorem arrivalCases_multi_shape {σ : ExecState}
    {threads : Array Config} {i : Nat} {c : Config}
    {os : List ArrivalOutcome}
    (h : arrivalCases σ threads i c = .ok (.multi os)) :
    ∃ v clauses default? done env k,
      c = .retV v (.selectOpsK clauses default? done [] env k)
      ∧ selectArrivalCases σ threads i clauses ((v :: done).reverse) env k
          = .ok (.multi os) := by
  unfold arrivalCases at h
  split at h
  · exfalso
    simp only [bind_eq_ok] at h
    obtain ⟨o, ho, h⟩ := h
    cases o <;> simp [Pure.pure, Except.pure] at h
  · exact ⟨_, _, _, _, _, _, rfl, h⟩
  · simp [Pure.pure, Except.pure] at h

/-- The two-point pool endpoint of a machine pairing, as a DM pool. -/
private theorem poolOfDM_two_point {threads : Array Config} {i j : Nat}
    {ci' cj' : Config} {σ'' : ExecState} {cur : Nat}
    (hilt : i < threads.size) (hjlt : j < threads.size) (hne : i ≠ j) :
    poolOfDM ⟨(threads.setIfInBounds i ci').setIfInBounds j cj', σ'', cur⟩
      = (((threads.toList.map PoolCfgDM.mk).set i ⟨ci'⟩).set j ⟨cj'⟩, σ'') := by
  simp [poolOfDM, Array.toList_setIfInBounds, List.map_set]

private theorem parkedReleaseNB_recv_nb {loc : Loc} {targets : List Assignee}
    {elem : Ty} {env : LocalEnv} {k : Cont} (h : locIsBase loc = false) :
    parkedReleaseNB (.blockedRecv (some loc) targets elem env k) = true := by
  cases loc <;> first | rfl | (simp [locIsBase] at h)

private theorem parkedReleaseNB_send_nb {loc : Loc} {v : GoValue} {k : Cont}
    (h : locIsBase loc = false) :
    parkedReleaseNB (.blockedSend (some loc) v k) = true := by
  cases loc <;> first | rfl | (simp [locIsBase] at h)

/-- The pool glue for a two-step decomposition IN MACHINE ORDER
(arriving thread `i` first, partner `j` second). -/
private theorem pair_pool_glue {m : MultiConfig} {i j : Nat}
    {c pc ci0 cj0 : Config} {σ₁ : ExecState} {ts' : Array Config}
    {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some c) (hj : m.threads[j]? = some pc)
    (hne : i ≠ j)
    (hts : ts' = (m.threads.setIfInBounds i ci0).setIfInBounds j cj0)
    (hstep1 : StepDM c m.shared ci0 σ₁ [])
    (hstep2 : StepDM pc σ₁ cj0 σ'' []) :
    poolOfDM m -·->ₜₚ* poolOfDM ⟨ts', σ'', cur⟩ := by
  have hilt : i < m.threads.size := (Array.getElem?_eq_some_iff.mp hti).1
  have hjlt : j < m.threads.size := (Array.getElem?_eq_some_iff.mp hj).1
  have hstep := poolStepDM_two hne (poolOfDM_get hti) (poolOfDM_get hj)
    (.step hstep1) (.step hstep2)
  rw [hts, poolOfDM_two_point hilt hjlt hne]
  exact hstep

/-- The pool glue in PARTNER-FIRST order (the deposit-then-drain arms
where the parked partner deposits and the arriving thread drains). -/
private theorem pair_pool_glue_rev {m : MultiConfig} {i j : Nat}
    {c pc ci0 cj0 : Config} {σ₁ : ExecState} {ts' : Array Config}
    {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some c) (hj : m.threads[j]? = some pc)
    (hne : i ≠ j)
    (hts : ts' = (m.threads.setIfInBounds i ci0).setIfInBounds j cj0)
    (hstep1 : StepDM pc m.shared cj0 σ₁ [])
    (hstep2 : StepDM c σ₁ ci0 σ'' []) :
    poolOfDM m -·->ₜₚ* poolOfDM ⟨ts', σ'', cur⟩ := by
  have hilt : i < m.threads.size := (Array.getElem?_eq_some_iff.mp hti).1
  have hjlt : j < m.threads.size := (Array.getElem?_eq_some_iff.mp hj).1
  have hstep := poolStepDM_two (Ne.symm hne) (poolOfDM_get hj)
    (poolOfDM_get hti) (.step hstep1) (.step hstep2)
  rw [hts, poolOfDM_two_point hilt hjlt hne, List.set_comm _ _ hne]
  exact hstep

/-- The ∃-residue decomposition (`pairArriveNB` then `pairReleaseNB`)
for a pairing whose cell is NOT `.base`; the caller supplies the
computed projections. -/
private theorem pair_erasedDM_nb {m : MultiConfig} {i j : Nat}
    {c bc pc : Config} {cs : List (Nat × PairTarget)} {idx : Nat}
    {ci0 cj0 : Config} {ts' : Array Config} {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some c) (hj : m.threads[j]? = some pc)
    (hne : i ≠ j)
    (hblc : isBlockedConfig c = false)
    (hpcblk : isBlockedConfig pc = true)
    (hrel : parkedReleaseNB pc = true)
    (hpair : PairAnalysis m.shared m.threads i c bc cs)
    (hidx : idx < cs.length)
    (hnb : ∀ l, candLoc bc cs[idx] = some l → locIsBase l = false)
    (happly : applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ''))
    (hts : ts' = (m.threads.setIfInBounds i ci0).setIfInBounds j cj0) :
    poolOfDM m -·->ₜₚ* poolOfDM ⟨ts', σ'', cur⟩ := by
  have hilt : i < m.threads.size := (Array.getElem?_eq_some_iff.mp hti).1
  have hjlt : j < m.threads.size := (Array.getElem?_eq_some_iff.mp hj).1
  have hproji : ts'[i]? = some ci0 := by
    subst hts
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
    simp [hilt]
  have hprojj : ts'[j]? = some cj0 := by
    subst hts
    simp [Array.size_setIfInBounds, hjlt]
  exact pair_pool_glue hti hj hne hts
    (.pairArriveNB hti hblc hpair hidx hnb happly hproji)
    (.pairReleaseNB hpcblk hrel
      ⟨m.shared, m.threads, i, j, bc, cs, idx, ts', hidx, hj, hne, happly,
        hprojj⟩)

set_option maxHeartbeats 3200000 in
/-- The SEND-arriving arms (plain send apply pairs a parked plain
receiver or a parked select's recv clause): `sendDeposit` then
`parkedRecvDrain`/`parkedSelRecvDrain` at `.base` cells; the ∃-residue
at path cells. -/
private theorem pair_erasedDM_send {m : MultiConfig} {i : Nat}
    {elem : Ty} {chv vv : GoValue} {env : LocalEnv} {k : Cont}
    {loc : Loc} {v'' : GoValue} {buf : Array GoValue} {cap : Nat}
    {cs : List (Nat × PairTarget)} {idx : Nat}
    {ts' : Array Config} {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some (.retV vv (.chanStK (.send elem) [chv] [] env k)))
    (hpair : PairAnalysis m.shared m.threads i
      (.retV vv (.chanStK (.send elem) [chv] [] env k))
      (.blockedSend (some loc) v'' k) cs)
    (hidx : idx < cs.length)
    (hclv : chanValueLoc chv = some loc)
    (hcell : chanCell m.shared loc = .ok (buf, cap, false))
    (hnorm : normalizeValueForTy m.shared elem vv = .ok v'')
    (hcseq : cs = recvSideWaiters m.threads i loc)
    (happly : applyPairing m.shared m.threads i (.blockedSend (some loc) v'' k)
      cs[idx] = .ok (ts', σ'')) :
    poolOfDM m -·->ₜₚ* poolOfDM ⟨ts', σ'', cur⟩ := by
  have happly0 := happly
  have hmem : cs[idx] ∈ recvSideWaiters m.threads i loc :=
    hcseq ▸ List.getElem_mem hidx
  rcases hcget : cs[idx] with ⟨cn, tgt⟩
  rw [hcget] at hmem happly happly0
  rcases recvSideWaiters_mem hmem with
    ⟨j, targets, elem2, envr, kr, rfl, hji, hjt⟩ |
    ⟨j, ci, evs, envs, ks, chv2, targets, elem2, body, rfl, hji, hjt, hev, hclv2⟩
  · -- ARM: parked plain receiver
    simp only [applyPairing, hjt] at happly
    simp only [bind_eq_ok] at happly
    obtain ⟨⟨buf', cap', cl'⟩, hcc, happly⟩ := happly
    rw [hcell] at hcc
    injection hcc with hcc
    injection hcc with hb hcc
    injection hcc with hc hcl
    subst hb; subst hc; subst hcl
    split at happly
    · rename_i hbe
      simp only [bind_eq_ok] at happly
      obtain ⟨⟨cr, s'⟩, hres, happly⟩ := happly
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at happly
      obtain ⟨hts, hσ⟩ := happly
      have hs' : s' = m.shared := resumeRecvDelivery_state hres
      subst hs'
      subst hσ
      have hbempty : buf = #[] := by
        cases buf with
        | mk l => cases l with
          | nil => rfl
          | cons x xs => simp [Array.isEmpty] at hbe
      subst hbempty
      by_cases hlb : locIsBase loc = true
      · obtain ⟨a⟩ := (by
          cases loc with
          | base a => exact ⟨a, rfl⟩
          | field b t f => simp [locIsBase] at hlb
          | index b ix => simp [locIsBase] at hlb :
          ∃ a, loc = Loc.base a)
        rename_i hleq
        subst hleq
        obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
        refine pair_pool_glue hti hjt (Ne.symm hji) hts.symm
          (.sendDeposit hclv hlk hnorm) ?_
        refine .parkedRecvDrain (lookup_setCell _ _
          ⟨dt, .chanData #[v''] cap false⟩)
          (show (#[v''] : Array GoValue)[0]? = some v'' from rfl) ?_
        rw [show (#[v''] : Array GoValue).eraseIdx! 0 = #[] by
            apply Array.ext'
            simp [Array.eraseIdx!],
          setCell_setCell, setCell_self hlk]
        exact hres
      · rw [Bool.not_eq_true] at hlb
        exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl
          (parkedReleaseNB_recv_nb hlb) hpair hidx
          (fun l hl => by
            rw [hcget] at hl
            simp only [candLoc, Option.some.injEq] at hl
            subst hl
            exact hlb)
          (hcget ▸ happly0) hts.symm
    · simp [throw, throwThe, MonadExceptOf.throw] at happly
  · -- ARM: parked select's recv clause
    simp only [applyPairing, hjt, hev] at happly
    simp only [bind_eq_ok] at happly
    obtain ⟨⟨buf', cap', cl'⟩, hcc, happly⟩ := happly
    rw [hcell] at hcc
    injection hcc with hcc
    injection hcc with hb hcc
    injection hcc with hc hcl
    subst hb; subst hc; subst hcl
    split at happly
    · rename_i hbe
      simp only [bind_eq_ok] at happly
      obtain ⟨⟨cs', s'⟩, hres, happly⟩ := happly
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at happly
      obtain ⟨hts, hσ⟩ := happly
      have hs' : s' = m.shared := selectRecvDelivery_state hres
      subst hs'
      subst hσ
      have hbempty : buf = #[] := by
        cases buf with
        | mk l => cases l with
          | nil => rfl
          | cons x xs => simp [Array.isEmpty] at hbe
      subst hbempty
      by_cases hlb : locIsBase loc = true
      · obtain ⟨a⟩ := (by
          cases loc with
          | base a => exact ⟨a, rfl⟩
          | field b t f => simp [locIsBase] at hlb
          | index b ix => simp [locIsBase] at hlb :
          ∃ a, loc = Loc.base a)
        rename_i hleq
        subst hleq
        obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
        refine pair_pool_glue hti hjt (Ne.symm hji) hts.symm
          (.sendDeposit hclv hlk hnorm) ?_
        refine .parkedSelRecvDrain hev
          (by rw [hclv2])
          (lookup_setCell _ _ ⟨dt, .chanData #[v''] cap false⟩)
          (show (#[v''] : Array GoValue)[0]? = some v'' from rfl) ?_
        rw [show (#[v''] : Array GoValue).eraseIdx! 0 = #[] by
            apply Array.ext'
            simp [Array.eraseIdx!],
          setCell_setCell, setCell_self hlk]
        exact hres
      · rw [Bool.not_eq_true] at hlb
        exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl rfl
          hpair hidx
          (fun l hl => by
            rw [hcget] at hl
            simp only [candLoc, Option.some.injEq] at hl
            subst hl
            exact hlb)
          (hcget ▸ happly0) hts.symm
    · simp [throw, throwThe, MonadExceptOf.throw] at happly

set_option maxHeartbeats 3200000 in
/-- The RECEIVE-arriving arms (plain recv apply pairs a parked plain
sender or a parked select's send clause): the partner DEPOSITS
(`parkedSendDeposit`/`parkedSelSendDeposit`), the arriving receiver
DRAINS (`recvDrain`) — the head-and-refill rotate falls out of the
`push`/`eraseIdx!` commutation. -/
private theorem pair_erasedDM_recv {m : MultiConfig} {i : Nat}
    {targets : List Assignee} {elem : Ty} {chv : GoValue} {env : LocalEnv}
    {k : Cont} {loc : Loc} {buf : Array GoValue} {cap : Nat}
    {cs : List (Nat × PairTarget)} {idx : Nat}
    {ts' : Array Config} {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some
      (.retV chv (.chanStK (.recv targets elem) [] [] env k)))
    (hpair : PairAnalysis m.shared m.threads i
      (.retV chv (.chanStK (.recv targets elem) [] [] env k))
      (.blockedRecv (some loc) targets elem env k) cs)
    (hidx : idx < cs.length)
    (hclv : chanValueLoc chv = some loc)
    (hcell : chanCell m.shared loc = .ok (buf, cap, false))
    (hcseq : cs = sendSideWaiters m.threads i loc)
    (happly : applyPairing m.shared m.threads i
      (.blockedRecv (some loc) targets elem env k) cs[idx] = .ok (ts', σ'')) :
    poolOfDM m -·->ₜₚ* poolOfDM ⟨ts', σ'', cur⟩ := by
  have happly0 := happly
  have hmem : cs[idx] ∈ sendSideWaiters m.threads i loc :=
    hcseq ▸ List.getElem_mem hidx
  rcases hcget : cs[idx] with ⟨cn, tgt⟩
  rw [hcget] at hmem happly happly0
  rcases sendSideWaiters_mem hmem with
    ⟨j, vs, ks, rfl, hji, hjt⟩ |
    ⟨j, ci, evs, envs, ks, chv2, vv2, selem, body, rfl, hji, hjt, hev, hclv2⟩
  · -- ARM: parked plain sender
    simp only [applyPairing, hjt] at happly
    simp only [bind_eq_ok] at happly
    obtain ⟨⟨buf', cap', cl'⟩, hcc, happly⟩ := happly
    rw [hcell] at hcc
    injection hcc with hcc
    injection hcc with hb hcc
    injection hcc with hc hcl
    subst hb; subst hc; subst hcl
    split at happly
    · -- direct handoff at an empty buffer
      rename_i hbuf
      simp only [bind_eq_ok] at happly
      obtain ⟨⟨cr, s'⟩, hres, happly⟩ := happly
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at happly
      obtain ⟨hts, hσ⟩ := happly
      have hs' : s' = m.shared := resumeRecvDelivery_state hres
      subst hs'
      subst hσ
      have hbempty : buf = #[] := array_empty_of_getElem?_none hbuf
      subst hbempty
      by_cases hlb : locIsBase loc = true
      · obtain ⟨a⟩ := (by
          cases loc with
          | base a => exact ⟨a, rfl⟩
          | field b t f => simp [locIsBase] at hlb
          | index b ix => simp [locIsBase] at hlb :
          ∃ a, loc = Loc.base a)
        rename_i hleq
        subst hleq
        obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
        refine pair_pool_glue_rev hti hjt (Ne.symm hji) hts.symm
          (.parkedSendDeposit hlk) ?_
        refine .recvDrain hclv (lookup_setCell _ _
          ⟨dt, .chanData #[vs] cap false⟩)
          (show (#[vs] : Array GoValue)[0]? = some vs from rfl) ?_
        rw [show (#[vs] : Array GoValue).eraseIdx! 0 = #[] by
            apply Array.ext'
            simp [Array.eraseIdx!],
          setCell_setCell, setCell_self hlk]
        exact hres
      · rw [Bool.not_eq_true] at hlb
        exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl
          (parkedReleaseNB_send_nb hlb) hpair hidx
          (fun l hl => by
            rw [hcget] at hl
            simp only [candLoc, Option.some.injEq] at hl
            subst hl
            exact hlb)
          (hcget ▸ happly0) hts.symm
    · -- head-and-refill at a nonempty buffer
      rename_i hd hbuf
      simp only [bind_eq_ok] at happly
      obtain ⟨s₁, hst, happly⟩ := happly
      obtain ⟨⟨cr, s'⟩, hres, happly⟩ := happly
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at happly
      obtain ⟨hts, hσ⟩ := happly
      have hs' : s' = s₁ := resumeRecvDelivery_state hres
      subst hs'
      subst hσ
      have hbufpos : 0 < buf.size := by
        have := (Array.getElem?_eq_some_iff.mp hbuf).1
        omega
      by_cases hlb : locIsBase loc = true
      · obtain ⟨a⟩ := (by
          cases loc with
          | base a => exact ⟨a, rfl⟩
          | field b t f => simp [locIsBase] at hlb
          | index b ix => simp [locIsBase] at hlb :
          ∃ a, loc = Loc.base a)
        rename_i hleq
        subst hleq
        obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
        have hs₁ : s' = setCell m.shared a
            ⟨dt, .chanData ((buf.eraseIdx! 0).push vs) cap false⟩ :=
          storeLoc_chanData_raw hlk hst
        refine pair_pool_glue_rev hti hjt (Ne.symm hji) hts.symm
          (.parkedSendDeposit hlk) ?_
        refine .recvDrain hclv (lookup_setCell _ _
          ⟨dt, .chanData (buf.push vs) cap false⟩)
          (array_push_getElem?_zero_of_nonempty hbuf) ?_
        rw [array_eraseIdx_push hbufpos, setCell_setCell, ← hs₁]
        exact hres
      · rw [Bool.not_eq_true] at hlb
        exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl
          (parkedReleaseNB_send_nb hlb) hpair hidx
          (fun l hl => by
            rw [hcget] at hl
            simp only [candLoc, Option.some.injEq] at hl
            subst hl
            exact hlb)
          (hcget ▸ happly0) hts.symm
  · -- ARM: parked select's send clause
    simp only [applyPairing, hjt, hev] at happly
    simp only [bind_eq_ok] at happly
    obtain ⟨v', hn', happly⟩ := happly
    obtain ⟨⟨buf', cap', cl'⟩, hcc, happly⟩ := happly
    rw [hcell] at hcc
    injection hcc with hcc
    injection hcc with hb hcc
    injection hcc with hc hcl
    subst hb; subst hc; subst hcl
    split at happly
    · rename_i hbuf
      simp only [bind_eq_ok] at happly
      obtain ⟨⟨cr, s'⟩, hres, happly⟩ := happly
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at happly
      obtain ⟨hts, hσ⟩ := happly
      have hs' : s' = m.shared := resumeRecvDelivery_state hres
      subst hs'
      subst hσ
      have hbempty : buf = #[] := array_empty_of_getElem?_none hbuf
      subst hbempty
      by_cases hlb : locIsBase loc = true
      · obtain ⟨a⟩ := (by
          cases loc with
          | base a => exact ⟨a, rfl⟩
          | field b t f => simp [locIsBase] at hlb
          | index b ix => simp [locIsBase] at hlb :
          ∃ a, loc = Loc.base a)
        rename_i hleq
        subst hleq
        obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
        refine pair_pool_glue_rev hti hjt (Ne.symm hji) hts.symm
          (.parkedSelSendDeposit hev (by rw [hclv2]) hlk hn') ?_
        refine .recvDrain hclv (lookup_setCell _ _
          ⟨dt, .chanData #[v'] cap false⟩)
          (show (#[v'] : Array GoValue)[0]? = some v' from rfl) ?_
        rw [show (#[v'] : Array GoValue).eraseIdx! 0 = #[] by
            apply Array.ext'
            simp [Array.eraseIdx!],
          setCell_setCell, setCell_self hlk]
        exact hres
      · rw [Bool.not_eq_true] at hlb
        exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl rfl
          hpair hidx
          (fun l hl => by
            rw [hcget] at hl
            simp only [candLoc, Option.some.injEq] at hl
            subst hl
            exact hlb)
          (hcget ▸ happly0) hts.symm
    · rename_i hd hbuf
      simp only [bind_eq_ok] at happly
      obtain ⟨s₁, hst, happly⟩ := happly
      obtain ⟨⟨cr, s'⟩, hres, happly⟩ := happly
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at happly
      obtain ⟨hts, hσ⟩ := happly
      have hs' : s' = s₁ := resumeRecvDelivery_state hres
      subst hs'
      subst hσ
      have hbufpos : 0 < buf.size := by
        have := (Array.getElem?_eq_some_iff.mp hbuf).1
        omega
      by_cases hlb : locIsBase loc = true
      · obtain ⟨a⟩ := (by
          cases loc with
          | base a => exact ⟨a, rfl⟩
          | field b t f => simp [locIsBase] at hlb
          | index b ix => simp [locIsBase] at hlb :
          ∃ a, loc = Loc.base a)
        rename_i hleq
        subst hleq
        obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
        have hs₁ : s' = setCell m.shared a
            ⟨dt, .chanData ((buf.eraseIdx! 0).push v') cap false⟩ :=
          storeLoc_chanData_raw hlk hst
        refine pair_pool_glue_rev hti hjt (Ne.symm hji) hts.symm
          (.parkedSelSendDeposit hev (by rw [hclv2]) hlk hn') ?_
        refine .recvDrain hclv (lookup_setCell _ _
          ⟨dt, .chanData (buf.push v') cap false⟩)
          (array_push_getElem?_zero_of_nonempty hbuf) ?_
        rw [array_eraseIdx_push hbufpos, setCell_setCell, ← hs₁]
        exact hres
      · rw [Bool.not_eq_true] at hlb
        exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl rfl
          hpair hidx
          (fun l hl => by
            rw [hcget] at hl
            simp only [candLoc, Option.some.injEq] at hl
            subst hl
            exact hlb)
          (hcget ▸ happly0) hts.symm

set_option maxHeartbeats 3200000 in
/-- The SELECT-arriving arms (a select apply's recv clause pairs a
parked plain sender; its send clause pairs a parked plain receiver):
`parkedSendDeposit`+`selRecvDrain` resp. `selSendDeposit`+
`parkedRecvDrain` at `.base` cells; the ∃-residue at path cells.
Select-with-select candidates are refuted by `applyPairing` itself. -/
private theorem pair_erasedDM_sel {m : MultiConfig} {i : Nat}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {done : List GoValue} {v : GoValue} {env : LocalEnv} {k : Cont}
    {evs : List EvClause} {cs : List (Nat × PairTarget)} {idx : Nat}
    {ts' : Array Config} {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some
      (.retV v (.selectOpsK clauses default? done [] env k)))
    (hpair : PairAnalysis m.shared m.threads i
      (.retV v (.selectOpsK clauses default? done [] env k))
      (.blockedSelect evs env k) cs)
    (hidx : idx < cs.length)
    (hevs : evalClauses clauses ((v :: done).reverse) = .ok evs)
    (hspec : SelCandsSpec m.shared m.threads i evs cs)
    (happly : applyPairing m.shared m.threads i (.blockedSelect evs env k)
      cs[idx] = .ok (ts', σ'')) :
    poolOfDM m -·->ₜₚ* poolOfDM ⟨ts', σ'', cur⟩ := by
  have happly0 := happly
  obtain ⟨ci, ws, hcands, hdisj⟩ := hspec
  have hmem0 : cs[idx] ∈ ws.map (fun w => (ci, w.2)) :=
    hcands ▸ List.getElem_mem hidx
  rcases hcget : cs[idx] with ⟨cn, tgt⟩
  rw [hcget] at hmem0 happly happly0
  obtain ⟨w, hwmem, hweq⟩ := List.mem_map.mp hmem0
  injection hweq with h1 h2
  subst h1
  subst h2
  obtain ⟨cn2, tgt2⟩ := w
  rcases hdisj with
    ⟨chv, targets, selem, body, loc, buf, cap, hev, hclv, hcell, rfl⟩ |
    ⟨chv, vv2, selem, body, loc, buf, cap, hev, hclv, hcell, rfl⟩
  · -- recv clause: partner is a parked SEND side
    rcases sendSideWaiters_mem hwmem with
      ⟨j, vs, ks, heqt, hji, hjt⟩ |
      ⟨j, ci2, evs2, envs, ks, chv3, vv3, selem3, body3, heqt, hji, hjt,
        hev2, hclv3⟩
    · -- plain parked sender: ARM 5
      subst heqt
      simp only [applyPairing, hev, hjt, hclv] at happly
      simp only [bind_eq_ok] at happly
      obtain ⟨⟨buf', cap', cl'⟩, hcc, happly⟩ := happly
      rw [hcell] at hcc
      injection hcc with hcc
      injection hcc with hb hcc
      injection hcc with hc hcl
      subst hb; subst hc; subst hcl
      split at happly
      · -- direct handoff at an empty buffer
        rename_i hbuf
        try simp only [bind_eq_ok] at happly
        obtain ⟨⟨ci', s'⟩, hres, happly⟩ := happly
        simp only [Pure.pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at happly
        obtain ⟨hts, hσ⟩ := happly
        have hs' : s' = m.shared := selectRecvDelivery_state hres
        subst hs'
        subst hσ
        have hbempty : buf = #[] := array_empty_of_getElem?_none hbuf
        subst hbempty
        by_cases hlb : locIsBase loc = true
        · obtain ⟨a⟩ := (by
            cases loc with
            | base a => exact ⟨a, rfl⟩
            | field b t f => simp [locIsBase] at hlb
            | index b ix => simp [locIsBase] at hlb :
            ∃ a, loc = Loc.base a)
          rename_i hleq
          subst hleq
          obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
          refine pair_pool_glue_rev hti hjt (Ne.symm hji) hts.symm
            (.parkedSendDeposit hlk) ?_
          refine .selRecvDrain hevs hev hclv (lookup_setCell _ _
            ⟨dt, .chanData #[vs] cap false⟩)
            (show (#[vs] : Array GoValue)[0]? = some vs from rfl) ?_
          rw [show (#[vs] : Array GoValue).eraseIdx! 0 = #[] by
              apply Array.ext'
              simp [Array.eraseIdx!],
            setCell_setCell, setCell_self hlk]
          exact hres
        · rw [Bool.not_eq_true] at hlb
          exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl
            (parkedReleaseNB_send_nb hlb) hpair hidx
            (fun l hl => by
              rw [hcget] at hl
              simp only [candLoc, hev, hclv, Option.some.injEq] at hl
              subst hl
              exact hlb)
            (hcget ▸ happly0) hts.symm
      · -- head-and-refill at a nonempty buffer
        rename_i hd hbuf
        try simp only [bind_eq_ok] at happly
        obtain ⟨s₁, hst, ⟨ci', s'⟩, hres, happly⟩ := happly
        simp only [Pure.pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at happly
        obtain ⟨hts, hσ⟩ := happly
        have hs' : s' = s₁ := selectRecvDelivery_state hres
        subst hs'
        subst hσ
        have hbufpos : 0 < buf.size := by
          have := (Array.getElem?_eq_some_iff.mp hbuf).1
          omega
        by_cases hlb : locIsBase loc = true
        · obtain ⟨a⟩ := (by
            cases loc with
            | base a => exact ⟨a, rfl⟩
            | field b t f => simp [locIsBase] at hlb
            | index b ix => simp [locIsBase] at hlb :
            ∃ a, loc = Loc.base a)
          rename_i hleq
          subst hleq
          obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
          have hs₁ : s' = setCell m.shared a
              ⟨dt, .chanData ((buf.eraseIdx! 0).push vs) cap false⟩ :=
            storeLoc_chanData_raw hlk hst
          refine pair_pool_glue_rev hti hjt (Ne.symm hji) hts.symm
            (.parkedSendDeposit hlk) ?_
          refine .selRecvDrain hevs hev hclv (lookup_setCell _ _
            ⟨dt, .chanData (buf.push vs) cap false⟩)
            (array_push_getElem?_zero_of_nonempty hbuf) ?_
          rw [array_eraseIdx_push hbufpos, setCell_setCell, ← hs₁]
          exact hres
        · rw [Bool.not_eq_true] at hlb
          exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl
            (parkedReleaseNB_send_nb hlb) hpair hidx
            (fun l hl => by
              rw [hcget] at hl
              simp only [candLoc, hev, hclv, Option.some.injEq] at hl
              subst hl
              exact hlb)
            (hcget ▸ happly0) hts.symm
    · -- select-with-select: refused by the machine
      subst heqt
      simp only [applyPairing, hev] at happly
      simp [throw, throwThe, MonadExceptOf.throw] at happly
  · -- send clause: partner is a parked RECV side
    rcases recvSideWaiters_mem hwmem with
      ⟨j, targetsr, elemr, envr, kr, heqt, hji, hjt⟩ |
      ⟨j, ci2, evs2, envs, ks, chv3, targets3, selem3, body3, heqt, hji, hjt,
        hev2, hclv3⟩
    · -- plain parked receiver: ARM 6
      subst heqt
      simp only [applyPairing, hev, hjt, hclv] at happly
      simp only [bind_eq_ok] at happly
      obtain ⟨⟨buf', cap', cl'⟩, hcc, happly⟩ := happly
      rw [hcell] at hcc
      injection hcc with hcc
      injection hcc with hb hcc
      injection hcc with hc hcl
      subst hb; subst hc; subst hcl
      split at happly
      · rename_i hbe
        try simp only [bind_eq_ok] at happly
        obtain ⟨v', hn', ⟨cr, s'⟩, hres, happly⟩ := happly
        simp only [Pure.pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at happly
        obtain ⟨hts, hσ⟩ := happly
        have hs' : s' = m.shared := resumeRecvDelivery_state hres
        subst hs'
        subst hσ
        have hbempty : buf = #[] := by
          cases buf with
          | mk l => cases l with
            | nil => rfl
            | cons x xs => simp [Array.isEmpty] at hbe
        subst hbempty
        by_cases hlb : locIsBase loc = true
        · obtain ⟨a⟩ := (by
            cases loc with
            | base a => exact ⟨a, rfl⟩
            | field b t f => simp [locIsBase] at hlb
            | index b ix => simp [locIsBase] at hlb :
            ∃ a, loc = Loc.base a)
          rename_i hleq
          subst hleq
          obtain ⟨dt, hlk⟩ := chanCell_base_inv hcell
          refine pair_pool_glue hti hjt (Ne.symm hji) hts.symm
            (.selSendDeposit hevs hev hclv hlk hn') ?_
          refine .parkedRecvDrain (lookup_setCell _ _
            ⟨dt, .chanData #[v'] cap false⟩)
            (show (#[v'] : Array GoValue)[0]? = some v' from rfl) ?_
          rw [show (#[v'] : Array GoValue).eraseIdx! 0 = #[] by
              apply Array.ext'
              simp [Array.eraseIdx!],
            setCell_setCell, setCell_self hlk]
          exact hres
        · rw [Bool.not_eq_true] at hlb
          exact pair_erasedDM_nb hti hjt (Ne.symm hji) rfl rfl
            (parkedReleaseNB_recv_nb hlb) hpair hidx
            (fun l hl => by
              rw [hcget] at hl
              simp only [candLoc, hev, hclv, Option.some.injEq] at hl
              subst hl
              exact hlb)
            (hcget ▸ happly0) hts.symm
      · simp [throw, throwThe, MonadExceptOf.throw] at happly
    · -- select-with-select: refused by the machine
      subst heqt
      simp only [applyPairing, hev] at happly
      simp [throw, throwThe, MonadExceptOf.throw] at happly

set_option maxHeartbeats 3200000 in
/-- **The mediated pairing decomposition** (design note §2d): every
machine pairing at a `.base` cell is DEPOSIT-then-DRAIN through the
physical cell; the non-`.base` residue rides the restricted ∃-rules. -/
theorem pair_erasedDM {m : MultiConfig} {i : Nat} {c bc : Config}
    {cs : List (Nat × PairTarget)} {idx : Nat}
    {ts' : Array Config} {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some c)
    (hblc : isBlockedConfig c = false)
    (hpair : PairAnalysis m.shared m.threads i c bc cs)
    (hidx : idx < cs.length)
    (happly : applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'')) :
    poolOfDM m -·->ₜₚ* poolOfDM ⟨ts', σ'', cur⟩ := by
  have hpair0 := hpair
  rcases hpair0 with harr | ⟨os, sel, harr, hos⟩
  · rcases arrivalCases_single_shape harr with
      ⟨v, op, done, env, k, rfl⟩ | ⟨v, clauses, default?, done, env, k, rfl⟩
    · have hplan := arrivalCases_chanStK_single harr
      cases op with
      | close =>
        rw [show chanArrivalPlan m.shared m.threads i .close
            ((v :: done).reverse) env k = .ok none by
          unfold chanArrivalPlan
          rcases (v :: done).reverse with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> rfl] at hplan
        cases hplan
      | send elem =>
        obtain ⟨chv, vv, loc, v'', buf, cap, hvs, hclv, hcell, hnorm,
          hbceq, hcseq⟩ := chanArrivalPlan_send_inv_full hplan
        obtain ⟨rfl, hdone⟩ := reverse_pair_inv hvs
        subst hdone
        subst hbceq
        exact pair_erasedDM_send hti hpair hidx hclv hcell hnorm hcseq happly
      | recv targets elem =>
        obtain ⟨chv, loc, buf, cap, hvs, hclv, hcell, hbceq, hcseq⟩ :=
          chanArrivalPlan_recv_inv_full hplan
        obtain ⟨rfl, hdone⟩ := reverse_singleton_inv hvs
        subst hdone
        subst hbceq
        exact pair_erasedDM_recv hti hpair hidx hclv hcell hcseq happly
    · have hsel : selectArrivalCases m.shared m.threads i clauses
          ((v :: done).reverse) env k = .ok (.single bc cs) := harr
      obtain ⟨evs, hevs, rfl, hspec⟩ := selectArrivalCases_single_inv hsel
      exact pair_erasedDM_sel hti hpair hidx hevs hspec happly
  · obtain ⟨v, clauses, default?, done, env, k, rfl, hsel⟩ :=
      arrivalCases_multi_shape harr
    obtain ⟨evs, hevs, rfl, hspec⟩ :=
      selectArrivalCases_multi_pair_inv hsel hos
    exact pair_erasedDM_sel hti hpair hidx hevs hspec happly

/-- **THE SIMULATION** (design note §2d): every pool-machine step is
one or two erased DM-Language steps between the corresponding pools —
`thread`/`spawned`/`wake`/`pickCommit` one step each, the two pairing
rules TWO (deposit-then-drain through the physical cell at `.base`
locations; the restricted ∃-residue at path locations). -/
theorem stepM_erasedDM {m m' : MultiConfig} (h : StepM m m') :
    poolOfDM m -·->ₜₚ* poolOfDM m' := by
  cases h with
  | thread hpick hti hblc harr hstep =>
    refine .tail .refl ?_
    have hs := poolStepDM_at (poolOfDM_get hti) (.step (.lift hstep))
    simp only [poolOfDM, Array.toList_append, Array.toList_setIfInBounds,
      List.map_set, List.map_append]
    exact hs
  | spawned hpick hti =>
    refine .tail .refl ?_
    have hs := poolStepDM_at (poolOfDM_get hti) (.step (.strip (σ := m.shared)))
    simp only [List.map_nil, List.append_nil] at hs
    simp only [poolOfDM, Array.toList_setIfInBounds, List.map_set]
    exact hs
  | wake hpick hti hblk hres =>
    refine .tail .refl ?_
    have hs := poolStepDM_at (poolOfDM_get hti) (.step (.wake hblk hres))
    simp only [List.map_nil, List.append_nil] at hs
    simp only [poolOfDM, Array.toList_setIfInBounds, List.map_set]
    exact hs
  | pickCommit hpick hti hblc hsp harr hos hcommit =>
    refine .tail .refl ?_
    have hs := poolStepDM_at (poolOfDM_get hti)
      (.step (.selCommitCell ⟨_, _, _, _, hti, harr, hos⟩ hcommit))
    simp only [List.map_nil, List.append_nil] at hs
    simp only [poolOfDM, Array.toList_setIfInBounds, List.map_set]
    exact hs
  | pair hpick hti hblc hsp harr hidx happly =>
    exact pair_erasedDM hti hblc (.inl harr) hidx happly
  | pickPair hpick hti hblc hsp harr hos hidx happly =>
    exact pair_erasedDM hti hblc (.inr ⟨_, _, harr, hos⟩) hidx happly

/-! ## Run erasure: a completed `execProg` run is a DM-Language trace -/

private theorem mainOutcomeDM_normal_inv {m : MultiConfig} {σf : ExecState}
    (h : m.mainOutcome? = some (.normal σf)) :
    m.threads[0]? = some (.next .stop) ∧ σf = m.shared := by
  unfold MultiConfig.mainOutcome? at h
  cases hti : m.threads[0]? with
  | none => rw [hti] at h; cases h
  | some c =>
    rw [hti] at h
    match c, h with
    | .next .stop, h =>
      injection h with h
      injection h with h
      exact ⟨rfl, h.symm⟩
    | .returning .stop, h => injection h with h; cases h
    | .breaking .stop, h => injection h with h; cases h
    | .continuing .stop, h => injection h with h; cases h

private theorem poolOfDM_main_normal {m : MultiConfig} {σf : ExecState}
    (h : m.mainOutcome? = some (.normal σf)) :
    ∃ rest, poolOfDM m = (⟨.next .stop⟩ :: rest, σf) := by
  obtain ⟨hti, rfl⟩ := mainOutcomeDM_normal_inv h
  rw [← Array.getElem?_toList] at hti
  cases hl : m.threads.toList with
  | nil => rw [hl] at hti; cases hti
  | cons c0 tail =>
    rw [hl] at hti
    injection hti with hti
    refine ⟨tail.map PoolCfgDM.mk, ?_⟩
    simp [poolOfDM, hl, hti]

/-- Run erasure, loop level (LangD's `execProgLoop_erasedD`, verbatim
structure over the mediated simulation). -/
theorem execProgLoop_erasedDM :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState} {ch ch' : Choices}
      {σf : ExecState},
      execProgLoop fuel m r ch = .ok (.normal σf, ch') →
      ∃ rest, poolOfDM m -·->ₜₚ* (⟨.next .stop⟩ :: rest, σf) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r ch ch' σf h
    rw [execProgLoop_unfold] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · rename_i out hmain
          split at h
          all_goals (repeat split at h)
          all_goals
            first
            | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
               rw [h.1] at hmain
               obtain ⟨rest, hp⟩ := poolOfDM_main_normal hmain
               exact ⟨rest, hp ▸ .refl⟩)
            | simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    intro m r ch ch' σf h
    rw [execProgLoop_unfold] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · rename_i out hmain
          split at h
          all_goals (repeat split at h)
          all_goals
            first
            | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
               rw [h.1] at hmain
               obtain ⟨rest, hp⟩ := poolOfDM_main_normal hmain
               exact ⟨rest, hp ▸ .refl⟩)
            | (dsimp only at h
               simp only [bind_eq_ok] at h
               obtain ⟨⟨m', ch₁⟩, hsm, r', -, h⟩ := h
               obtain ⟨rest, htr⟩ := ih h
               exact ⟨rest, .trans (stepM_erasedDM (stepMulti_sound hsm)) htr⟩)
            | simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · dsimp only at h
            simp only [bind_eq_ok] at h
            obtain ⟨⟨m', ch₁⟩, hsm, r', -, h⟩ := h
            obtain ⟨rest, htr⟩ := ih h
            exact ⟨rest, .trans (stepM_erasedDM (stepMulti_sound hsm)) htr⟩

/-- **Run erasure** over the mediated Language. -/
theorem execProg_erasedDM {fuel : Nat} {env : LocalEnv} {σ₀ : ExecState}
    {ch ch' : Choices} {prog : Stmt} {σf : ExecState}
    (h : execProg fuel env σ₀ ch prog = .ok (.normal σf, ch')) :
    ∃ rest : List PoolCfgDM,
      (([⟨.exec prog env .stop⟩] : List PoolCfgDM), σ₀) -·->ₜₚ*
        (⟨.next .stop⟩ :: rest, σf) := by
  obtain ⟨rest, htr⟩ := execProgLoop_erasedDM h
  exact ⟨rest, htr⟩

/-! ## The Iris side: state interpretation, adequacy, and THE EXIT
(at `.MaybeStuck` — parked configurations at empty open cells are
irreducible on this carrier by design; `adequate_result`, the only
field the exit consumes, is stuckness-independent) -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

instance : IrisGS_gen hlc PoolCfgDM GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end

/-- Strong adequacy with initial-heap handover over the DM-Language
(`goD_heap_adequacy_own` at `.MaybeStuck` — the WP obligations of this
carrier's laws are stated there because parked-empty configurations
are irreducible; no exported statement mentions stuckness). -/
theorem goDM_heap_adequacy_own {GF : BundledGFunctors} [GoCoreGpreS .hasLC GF]
    (c : PoolCfgDM) (σ : ExecState)
    (Ψ : ∀ [GoCoreGS .hasLC GF], Unit → IProp GF)
    (φ : Unit → ExecState → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      iprop([∗map] l ↦ cell ∈ heapToMap σ.heap, l ↦ cell)
        ⊢@{IProp GF} (WP c @ Stuckness.MaybeStuck ; ⊤ {{ v, Ψ v }}))
    (Hext : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      ∀ (σ2 : ExecState) (v : Unit),
        iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ2.heap) ∗ Ψ v)
          ⊢ |==> ⌜φ v σ2⌝) :
    adequate Stuckness.MaybeStuck c σ φ := by
  refine (adequate_alt _ c σ φ).mpr ?_
  intro t2 σ2 hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) Stuckness.MaybeStuck
    (Hsteps := hsteps) (numLaters := fun _ => 0)
  iintro %Hinv
  imod (genHeap_init_names (GF := GF) (heapToMap σ.heap))
    with ⟨%γh, %γm, Hσ, Hpts, Htok⟩
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩, σ.functions, σ.methods, σ.types⟩
  imodintro
  iexists (fun σ' _ _ _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ σ'.methods = σ.methods
          ∧ σ'.types = σ.types ∧ HeapWf σ'⌝))
  iexists [(fun v => Ψ v)], (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨rfl, rfl, rfl, hσwf⟩
  isplitl [Hpts]
  · iapply BigSepL2.bigSepL2_singleton
    iapply (Hwp rfl rfl rfl) $$ Hpts
  iintro %es' %t2' %Heq %Hlen %HNS Hst Hwptp _
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hwptp with ⟨%e', %_, %Heq', Hpost, H⟩
  subst Heq' Heq
  icases BigSepL2.bigSepL2_nil_inv_right $$ H with %Heq
  subst Heq
  icases Hst with ⟨Hgh, %Hpure⟩
  cases h : toVal e'
  · iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind
  · dsimp only [Option.elim_some]
    imod (Hext rfl rfl rfl σ2 _) $$ [$Hgh $Hpost] with %Hφv
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind

section

variable {types : TypeEnv} {funcs : Array Func} {methods : Array MethodInfo}
  {env₀ : LocalEnv} {P Q : HProp} {prog : Stmt}

private theorem goTripleC_adequateDM
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      GoCoreGS.methods GoCoreS = methods → GoCoreGS.types GoCoreS = types →
      embed (GF := GoCoreS) P
        ⊢ WP (PoolCfgDM.mk (.exec prog env₀ .stop)) @ Stuckness.MaybeStuck ; ⊤
            {{ _v, embed Q }})
    {hp : Heap} {na : Nat} {hP F : Heaplet}
    (hinit : InitialSplit P hp na hP F funcs env₀ prog) :
    adequate Stuckness.MaybeStuck (PoolCfgDM.mk (.exec prog env₀ .stop))
      (ExecState.mk (types := types) (functions := funcs) (methods := methods)
        (methodSets := #[]) (heap := hp) (nextAddr := na))
      (fun _ σ2 => ∃ hQ : Heaplet,
        (∀ k, hQ.get? k = none ∨ F.get? k = none)
        ∧ Heaplet.sub hQ (heapToMap σ2.heap)
        ∧ Heaplet.sub F (heapToMap σ2.heap) ∧ sat hQ Q) := by
  refine goDM_heap_adequacy_own (GF := GoCoreS) _ _
    (Ψ := fun _ => iprop(ownHeaplet F ∗ embed Q))
    (φ := fun _ σ2 => ∃ hQ : Heaplet,
      (∀ k, hQ.get? k = none ∨ F.get? k = none)
      ∧ Heaplet.sub hQ (heapToMap σ2.heap)
      ∧ Heaplet.sub F (heapToMap σ2.heap) ∧ sat hQ Q)
    hinit.heapBounded ?_ ?_
  · intro _inst hprog hmeths htypes
    have hsplit : ownHeaplet (GF := GoCoreS) (heapToMap hp)
        ⊢ embed P ∗ ownHeaplet F := by
      rw [← heapletOf_eq_heapToMap]
      refine ((BigSepM.bigSepM_eqv_of_perm
        (cover_equiv hinit.disj hinit.cover)).1).trans ?_
      exact ((ownHeaplet_union hinit.disj).1).trans
        (sep_mono (reflect P hP hinit.sat_pre) .rfl)
    exact hsplit.trans ((BI.sep_comm.1).trans
      ((sep_mono .rfl (Hwp hprog hmeths htypes)).trans wp_frame_l))
  · intro _inst _hprog _hmeths _htypes σ2 _v
    iintro ⟨Hσ, HF, HQ⟩
    icases (embed_toHeaplet Q) $$ HQ with ⟨%hQ, %hsQ, HownQ⟩
    ihave %hdisjQF := ownHeaplet_disjoint $$ [$HownQ $HF]
    ihave HU := (ownHeaplet_union hdisjQF).2 $$ [$HownQ $HF]
    ihave %hsub := ownHeaplet_sub $$ [$Hσ $HU]
    imodintro
    ipureintro
    obtain ⟨h1, h2⟩ := sub_union_split hdisjQF hsub
    exact ⟨hQ, hdisjQF, h1, h2, hsQ⟩

/-- **THE EXIT: `GoTripleC` from a DM-Language WP** — LangD's
`goTripleC_of_wpD` re-plumbed through the mediated simulation. The WP
obligation is at `.MaybeStuck` (module docstring; the judgment itself
is unchanged and stuckness-free). -/
theorem goTripleC_of_wpDM
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      GoCoreGS.methods GoCoreS = methods → GoCoreGS.types GoCoreS = types →
      embed (GF := GoCoreS) P
        ⊢ WP (PoolCfgDM.mk (.exec prog env₀ .stop)) @ Stuckness.MaybeStuck ; ⊤
            {{ _v, embed Q }}) :
    GoTripleC types funcs methods env₀ P prog Q := by
  intro hp na hP F hinit fuel ch σf ch' hrun
  obtain ⟨rest, htr⟩ := execProg_erasedDM hrun
  have hres := (goTripleC_adequateDM Hwp hinit).adequate_result rest σf () htr
  obtain ⟨hQ, hd, h1, h2, hs⟩ := hres
  exact ⟨hQ, hd, by rw [heapletOf_eq_heapToMap]; exact h1,
    by rw [heapletOf_eq_heapToMap]; exact h2, hs⟩

end

/-! ## The DM-carrier WP law kit (ports of the `wpD_*` kit; the
mediated rules are refuted by the same two shape side-conditions) -/

/-- The mediated rules are silent away from apply positions and
blocked shapes (the refutation kit for the pure lifts). -/
theorem stepDM_shape_cases {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} {efs : List Config}
    (hblk : isBlockedConfig c = false)
    (hpos : chanSelApplyPos c = false)
    (h : StepDM c σ c' σ' efs) :
    StepE c σ c' σ' efs ∨ (∃ k, c = .spawned k ∧ c' = .next k ∧ σ' = σ ∧ efs = []) := by
  cases h with
  | lift hs => exact .inl hs
  | strip => exact .inr ⟨_, rfl, rfl, rfl, rfl⟩
  | wake hb _ => rw [hblk] at hb; cases hb
  | pairReleaseNB hb _ _ => rw [hblk] at hb; cases hb
  | parkedSendDeposit _ => simp [isBlockedConfig] at hblk
  | parkedRecvDrain _ _ _ => simp [isBlockedConfig] at hblk
  | parkedSelSendDeposit _ _ _ _ => simp [isBlockedConfig] at hblk
  | parkedSelRecvDrain _ _ _ _ _ => simp [isBlockedConfig] at hblk
  | sendDeposit _ _ _ => simp [chanSelApplyPos] at hpos
  | recvDrain _ _ _ _ => simp [chanSelApplyPos] at hpos
  | selSendDeposit _ _ _ _ _ => simp [chanSelApplyPos] at hpos
  | selRecvDrain _ _ _ _ _ _ => simp [chanSelApplyPos] at hpos
  | pairArriveNB hti hb hpair hidx hnb happly hproj =>
    rcases hpair with hs | ⟨os, sel, hm, -⟩
    · rw [arrivalCases_of_nonApply hpos] at hs
      cases hs
    · rw [arrivalCases_of_nonApply hpos] at hm
      cases hm
  | selCommitCell hex _ =>
    obtain ⟨threads, i, os, sel, hti, hm, -⟩ := hex
    rw [arrivalCases_of_nonApply hpos] at hm
    cases hm

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- The pure deterministic lift on the DM-carrier. -/
theorem wpDM_pure_det {c c' : Config}
    (hsp : spawnPlan c = none) (hsc : spawnedCont c = none)
    (hblk : isBlockedConfig c = false) (hpos : chanSelApplyPos c = false)
    (hstep : ∀ σ : ExecState, Step c σ c' σ)
    (hdet : ∀ (σ : ExecState) (c₂ : Config) (σ₂ : ExecState),
      Step c σ c₂ σ₂ → c₂ = c' ∧ σ₂ = σ) :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk c') @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk c) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := PoolCfgDM.mk c')
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], ⟨c'⟩, σ, [], GoPrimStepDM.step (.lift (.lift (hstep σ)))⟩
      · exact Language.val_stuck (GoPrimStepDM.step (.lift (.lift (hstep σ))))
    )
    (Hpuredet := by
      intro σ₁ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        rcases stepDM_shape_cases hblk hpos st with hse | ⟨k, rfl, -⟩
        · cases hse with
          | lift sq =>
            obtain ⟨rfl, rfl⟩ := hdet _ _ _ sq
            exact ⟨rfl, rfl, rfl, rfl⟩
          | spawn hsp' _ =>
            rw [hsp] at hsp'
            cases hsp'
        · simp [spawnedCont] at hsc))
  iexact H

/-- The marker strip on the DM-carrier. -/
theorem wpDM_spawned_strip {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.spawned k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := PoolCfgDM.mk (.next k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], ⟨.next k⟩, σ, [], GoPrimStepDM.step .strip⟩
      · rfl)
    (Hpuredet := by
      intro σ₁ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        rcases stepDM_shape_cases rfl rfl st with hse | ⟨k', hk, rfl, rfl, rfl⟩
        · cases hse with
          | lift sq => exact absurd sq (step_spawnedMarker_elim rfl)
          | spawn hsp' _ => cases hsp'
        · injection hk with hk
          subst hk
          exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Resource-conditioned deterministic NON-MUTATING step core on the
DM-carrier. -/
theorem wpDM_det_step_keep {P : IProp GF} {c₀ c₁ : Config}
    (hnv : ToVal.toVal (PoolCfgDM.mk c₀) = (none : Option Unit))
    (hsp : spawnPlan c₀ = none) (hsc : spawnedCont c₀ = none)
    (hblk : isBlockedConfig c₀ = false) (hpos : chanSelApplyPos c₀ = false)
    (hred : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ₁.heap) ∗ P)
        ⊢ |==> ⌜Step c₀ σ₁ c₁ σ₁ ∧
            (∀ c' s', Step c₀ σ₁ c' s' → c' = c₁ ∧ s' = σ₁)⌝) :
    P ∗ (P -∗ WP (PoolCfgDM.mk c₁) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk c₀) @ s ; E {{ Φ }} := by
  iintro ⟨HP, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  ihave %Hstep : ⌜Step c₀ σ₁ c₁ σ₁ ∧
      (∀ c' s', Step c₀ σ₁ c' s' → c' = c₁ ∧ s' = σ₁)⌝ $$ [Hσ HP]
  · icases (hred σ₁ hfns hmeths htypes) $$ [$Hσ $HP] with >%h
    ipureintro
    exact h
  obtain ⟨hstep, hdet⟩ := Hstep
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], PoolCfgDM.mk c₁, _, [], GoPrimStepDM.step (.lift (.lift hstep))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep2 Hcred
  cases Hstep2 with
  | step st =>
    rcases stepDM_shape_cases hblk hpos st with hse | ⟨kk, hkk, -⟩
    · cases hse with
      | lift sq =>
        obtain ⟨rfl, rfl⟩ := hdet _ _ sq
        imod Hclose
        imodintro
        simp only [List.map_nil, Algebra.BigOpL.bigOpL_nil]
        isplitl [Hσ]
        · isplitl [Hσ]
          · iexact Hσ
          · ipureintro
            exact ⟨hfns, hmeths, htypes, hwf⟩
        · isplitl [HP Hcont]
          · iapply Hcont $$ HP
          · itrivial
      | spawn hsp' _ =>
        rw [hsp] at hsp'
        cases hsp'
    · rw [hkk] at hsc
      simp [spawnedCont] at hsc

/-- The variable-load step on the DM-carrier. -/
theorem wpDM_eval_var {id : String} {a : Addr} {dq : DFrac} {cell : HeapCell}
    {env : LocalEnv} {k : Cont}
    (hres : LocalEnv.lookup env id = some (.base a)) :
    a.id ↦{dq} cell
      ∗ (a.id ↦{dq} cell -∗ WP (PoolCfgDM.mk (.retV cell.value k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.evalE (.var id) env k)) @ s ; E {{ Φ }} := by
  iapply wpDM_det_step_keep (P := iprop(a.id ↦{dq} cell))
    (c₁ := Config.retV cell.value k) (hnv := rfl) (hsp := rfl) (hsc := rfl)
    (hblk := rfl) (hpos := rfl)
  intro σ₁ _hfns _hmeths _htypes
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok cell.value := by
    simp [loadLoc, hlook]
  imodintro
  ipureintro
  refine ⟨Step.evalVar hres hload, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.evalVar hres hload) hst
  exact ⟨h1.symm, h2.symm⟩

/-- The owned-cell STORE core on the DM-carrier (the delivery-frame
walk's engine — `wp_store_step`'s port). -/
theorem wpDM_store_step {a : Addr} {oldcell newcell : HeapCell}
    {c₀ c₁ : Config}
    (hnv : ToVal.toVal (PoolCfgDM.mk c₀) = (none : Option Unit))
    (hsp : spawnPlan c₀ = none) (hsc : spawnedCont c₀ = none)
    (hblk : isBlockedConfig c₀ = false) (hpos : chanSelApplyPos c₀ = false)
    (hstep : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step c₀ σ₁ c₁ { σ₁ with
        heap := Heap.set σ₁.heap (.base a) newcell }
      ∧ (∀ c' s', Step c₀ σ₁ c' s' → c' = c₁
          ∧ s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell })) :
    a.id ↦ oldcell
      ∗ (a.id ↦ newcell -∗ WP (PoolCfgDM.mk c₁) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk c₀) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some oldcell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some oldcell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  obtain ⟨hstep1, hdet⟩ := hstep σ₁ hfns hmeths htypes hlook
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], PoolCfgDM.mk c₁, _, [], GoPrimStepDM.step (.lift (.lift hstep1))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep2 Hcred
  cases Hstep2 with
  | step st =>
    rcases stepDM_shape_cases hblk hpos st with hse | ⟨kk, hkk, -⟩
    · cases hse with
      | lift sq =>
        obtain ⟨rfl, rfl⟩ := hdet _ _ sq
        imod (genHeap_update (v₂ := newcell)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
        imod Hclose
        imodintro
        simp only [List.map_nil, Algebra.BigOpL.bigOpL_nil]
        isplitl [Hσ]
        · isplitl [Hσ]
          · iapply (genHeapInterp_eqv
              (fun kk => (heapToMap_set_base σ₁.heap a newcell kk).symm)) $$ Hσ
          · ipureintro
            exact ⟨hfns, hmeths, htypes, hwf.set_existing hlook⟩
        isplitl [Hpt Hcont]
        · iapply Hcont $$ Hpt
        · itrivial
      | spawn hsp' _ =>
        rw [hsp] at hsp'
        cases hsp'
    · rw [hkk] at hsc
      simp [spawnedCont] at hsc

/-- **The ALLOCATING FORK on the DM-carrier** (`wpD_fork_alloc₁`'s
port; the one-parameter spawn class — the exemplar's worker). -/
theorem wpDM_fork_alloc₁ {c : Config} {cv : GoValue} {args : List GoValue}
    {k : Cont} {pcell : HeapCell} (childOf : Addr → Config)
    (hsp : spawnPlan c = some (cv, args, k))
    (hspawn : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      spawnStep σ cv args k = .ok (.spawned k, childOf ⟨σ.nextAddr⟩,
        allocMany σ [pcell])) :
    ▷ iprop(∀ pa : Addr, pa.id ↦ pcell -∗
        WP (PoolCfgDM.mk (childOf pa)) @ s ; ⊤ {{ fun _ => iprop(True) }})
      ∗ ▷ WP (PoolCfgDM.mk (.spawned k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfgDM.mk c) @ s ; E {{ Φ }} := by
  iintro ⟨Hchild, Hparent⟩
  have hnv : ToVal.toVal (PoolCfgDM.mk c) = (none : Option Unit) := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  have hblk : isBlockedConfig c = false := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  have hpos : chanSelApplyPos c = false := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  iapply wp_lift_step hnv
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hfresh : get? (heapToMap σ₁.heap) σ₁.nextAddr = none := hwf.fresh_get?
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.spawned k⟩, _, [⟨childOf ⟨σ₁.nextAddr⟩⟩],
        GoPrimStepDM.step (.lift (.spawn hsp (hspawn σ₁ hfns hmeths htypes)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  have hshape : e₂ = PoolCfgDM.mk (.spawned k) ∧ σ₂ = allocMany σ₁ [pcell]
      ∧ eₜ = [PoolCfgDM.mk (childOf ⟨σ₁.nextAddr⟩)] := by
    cases Hstep with
    | step st =>
      rcases stepDM_shape_cases hblk hpos st with hse | ⟨k', hk, -⟩
      · cases hse with
        | lift sq => exact absurd sq (step_spawnPos_elim hsp)
        | spawn hsp' hstep' =>
          rw [hsp] at hsp'
          injection hsp' with heq
          injection heq with h1 hrest
          injection hrest with h2 h3
          subst h1
          subst h2
          subst h3
          rw [hspawn σ₁ hfns hmeths htypes] at hstep'
          injection hstep' with hp
          injection hp with hpar hrest'
          injection hrest' with hchild hσ
          subst hpar
          subst hchild
          subst hσ
          exact ⟨rfl, rfl, rfl⟩
      · rw [hk] at hsp
        cases hsp
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  simp only [allocMany]
  imod (genHeap_alloc (v := pcell) hfresh) $$ Hσ with ⟨Hσ, Hp, Htok⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · isplitl [Hσ]
    · iapply (genHeapInterp_eqv
        (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ pcell kk).symm)) $$ Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, HeapWf.allocMany [pcell] hwf⟩
  isplitl [Hparent]
  · iexact Hparent
  · simp only [Algebra.BigOpL.bigOpL_cons, Algebra.BigOpL.bigOpL_nil]
    isplitl [Hchild Hp]
    · iapply Hchild $$ %(⟨σ₁.nextAddr⟩ : Addr) [$Hp]
    · itrivial

/-- **The TWO-PARAMETER allocating fork on the DM-carrier** (the dsp
child's shape: `go lit0(&c, &signal)` — two consecutive param cells;
the continuation receives the first machine-chosen address, the second
is its successor). -/
theorem wpDM_fork_alloc₂ {c : Config} {cv : GoValue} {args : List GoValue}
    {k : Cont} {pcell₁ pcell₂ : HeapCell} (childOf : Addr → Config)
    (hsp : spawnPlan c = some (cv, args, k))
    (hspawn : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      spawnStep σ cv args k = .ok (.spawned k, childOf ⟨σ.nextAddr⟩,
        allocMany σ [pcell₁, pcell₂])) :
    ▷ iprop(∀ pa : Addr, pa.id ↦ pcell₁ ∗ (pa.id + 1) ↦ pcell₂ -∗
        WP (PoolCfgDM.mk (childOf pa)) @ s ; ⊤ {{ fun _ => iprop(True) }})
      ∗ ▷ WP (PoolCfgDM.mk (.spawned k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfgDM.mk c) @ s ; E {{ Φ }} := by
  iintro ⟨Hchild, Hparent⟩
  have hnv : ToVal.toVal (PoolCfgDM.mk c) = (none : Option Unit) := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  have hblk : isBlockedConfig c = false := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  have hpos : chanSelApplyPos c = false := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  iapply wp_lift_step hnv
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hfresh : get? (heapToMap σ₁.heap) σ₁.nextAddr = none := hwf.fresh_get?
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.spawned k⟩, _, [⟨childOf ⟨σ₁.nextAddr⟩⟩],
        GoPrimStepDM.step (.lift (.spawn hsp (hspawn σ₁ hfns hmeths htypes)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  have hshape : e₂ = PoolCfgDM.mk (.spawned k)
      ∧ σ₂ = allocMany σ₁ [pcell₁, pcell₂]
      ∧ eₜ = [PoolCfgDM.mk (childOf ⟨σ₁.nextAddr⟩)] := by
    cases Hstep with
    | step st =>
      rcases stepDM_shape_cases hblk hpos st with hse | ⟨k', hk, -⟩
      · cases hse with
        | lift sq => exact absurd sq (step_spawnPos_elim hsp)
        | spawn hsp' hstep' =>
          rw [hsp] at hsp'
          injection hsp' with heq
          injection heq with h1 hrest
          injection hrest with h2 h3
          subst h1
          subst h2
          subst h3
          rw [hspawn σ₁ hfns hmeths htypes] at hstep'
          injection hstep' with hp
          injection hp with hpar hrest'
          injection hrest' with hchild hσ
          subst hpar
          subst hchild
          subst hσ
          exact ⟨rfl, rfl, rfl⟩
      · rw [hk] at hsp
        cases hsp
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  simp only [allocMany]
  imod (genHeap_alloc (v := pcell₁) hfresh) $$ Hσ with ⟨Hσ, Hp₁, Htok₁⟩
  have hfresh₂ : get? (insert (heapToMap σ₁.heap) σ₁.nextAddr pcell₁)
      (σ₁.nextAddr + 1) = none := by
    rw [get?_insert_ne (by omega)]
    rw [get?_heapToMap]
    exact hwf (σ₁.nextAddr + 1) (by omega)
  imod (genHeap_alloc (v := pcell₂) hfresh₂) $$ Hσ with ⟨Hσ, Hp₂, Htok₂⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · isplitl [Hσ]
    · iapply (genHeapInterp_eqv (fun kk =>
        ((heapToMap_set_base₂ σ₁.heap ⟨σ₁.nextAddr⟩ ⟨σ₁.nextAddr + 1⟩
          pcell₁ pcell₂) kk).symm)) $$ Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, HeapWf.allocMany [pcell₁, pcell₂] hwf⟩
  isplitl [Hparent]
  · iexact Hparent
  · simp only [Algebra.BigOpL.bigOpL_cons, Algebra.BigOpL.bigOpL_nil]
    isplitl [Hchild Hp₁ Hp₂]
    · iapply Hchild $$ %(⟨σ₁.nextAddr⟩ : Addr)
      isplitl [Hp₁]
      · iexact Hp₁
      · iexact Hp₂
    · itrivial

end

end GoLean.Iris