import GoLeanProofs.Sym.Mirror

/-!
# Concretization: mirror shapes → GoCore shapes (WP arc slice 4)

The generic interpretation layer (log JC-4): ONE family of
concretization functions over an `Interp D` pack serves BOTH gated
theorems —

- at the CONCRETE domain (`cInterp`: identities, no atoms), `conc*` is
  the design §6.1 EMBEDDING `emb*`, and the master step-commutation is
  THE DRIFT THEOREM (`Sym/Drift.lean`, default build target);
- at the SYMBOLIC domain (`symInterp ρ`: `γI ρ`/`γB ρ`/`ρ.vals`),
  `conc*` is the design §5.1 γ family, and the same master theorem is
  the per-step half of THE REFINEMENT THEOREM (phase 2's window
  induction composes it).

`Interp.Sound` is the equation pack the walk consumes — its fields ARE
the design §6.2 "scalar leaves" (one per `ScalarDom` op, plus the two
inspection-soundness laws). The concrete instance's pack closes by
`rfl`; the symbolic instance's is discharged from the `γ` display
equations and `closedI?_sound`/`closedB?_sound`.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- An interpretation of a scalar domain's payloads into the machine's
values. -/
structure Interp (D : ScalarDom) where
  intV : D.IntR → Int
  boolV : D.BoolR → Bool
  atomV : D.Atom → GoValue
  /-- Whole-cell atoms (JC-6). -/
  cellV : D.Atom → GoCore.HeapCell

variable {D : ScalarDom}

/-- The soundness pack: the interpretation respects every domain
operation (the ~15 scalar leaves of design §6.2 layer 1). The
`toInt?`/`toBool?` laws are the closedness-soundness direction only —
exactly what quit-on-`none` requires (a refused inspection asserts
nothing). -/
structure Interp.Sound (I : Interp D) : Prop where
  litI : ∀ n, I.intV (D.litI n) = n
  litB : ∀ b, I.boolV (D.litB b) = b
  add : ∀ a b, I.intV (D.add a b) = I.intV a + I.intV b
  sub : ∀ a b, I.intV (D.sub a b) = I.intV a - I.intV b
  mul : ∀ a b, I.intV (D.mul a b) = I.intV a * I.intV b
  divC : ∀ a k, I.intV (D.divC a k) = Int.tdiv (I.intV a) k
  modC : ∀ a k, I.intV (D.modC a k) = Int.tmod (I.intV a) k
  neg : ∀ a, I.intV (D.neg a) = 0 - I.intV a
  norm : ∀ kind a, I.intV (D.norm kind a) = kind.normalize (I.intV a)
  notB : ∀ a, I.boolV (D.notB a) = !(I.boolV a)
  eqI : ∀ a b, I.boolV (D.eqI a b) = (I.intV a == I.intV b)
  ltI : ∀ a b, I.boolV (D.ltI a b) = decide (I.intV a < I.intV b)
  leI : ∀ a b, I.boolV (D.leI a b) = decide (I.intV a ≤ I.intV b)
  toInt? : ∀ a n, D.toInt? a = some n → I.intV a = n
  toBool? : ∀ a b, D.toBool? a = some b → I.boolV a = b

/-! ## The concretization functions -/

def concV (I : Interp D) : Value D → GoValue
  | .unit => .unit
  | .bool b => .bool (I.boolV b)
  | .int v kind => .int (I.intV v) kind
  | .float bits kind => .float bits kind
  | .string s => .string s
  | .addr loc => .addr loc
  | .nil => .nil
  | .interface dynTy inner => .interface dynTy (concV I inner)
  | .struct tid fields => .struct tid (fields.attach.map
      (fun ⟨(name, v), _⟩ => (name, concV I v)))
  | .array values => .array (values.attach.map (fun ⟨v, _⟩ => concV I v))
  | .slice sv => .slice sv
  | .map mv => .map mv
  | .mapData entries => .mapData (entries.attach.map
      (fun ⟨(k, v), _⟩ => (concV I k, concV I v)))
  | .chan cv => .chan cv
  | .chanData buf capacity closed =>
      .chanData (buf.attach.map (fun ⟨v, _⟩ => concV I v)) capacity closed
  | .funcVal fid captured =>
      .funcVal fid (captured.attach.map (fun ⟨v, _⟩ => concV I v))
  | .syncData p => .syncData p
  | .atom a => I.atomV a
termination_by v => sizeOf v
decreasing_by
  all_goals
    first
      | (rename_i h
         first
           | (have hlt := Array.sizeOf_lt_of_mem h; simp_all; omega)
           | (have hlt := List.sizeOf_lt_of_mem h; simp_all; omega))
      | (simp_all; omega)
      | omega

def concEntry (I : Interp D) (e : PanicEntry D) : Machine.PanicEntry :=
  ⟨concV I e.value, e.recovered⟩

def concRef (I : Interp D) : TargetRef D → Machine.TargetRef
  | .chain anchor idxs steps =>
      .chain (concV I anchor) (idxs.map (concV I)) steps
  | .mapElem b k kt vt => .mapElem (concV I b) (concV I k) kt vt

def concClause (I : Interp D) : EvClause D → Machine.EvClause
  | .sendEv chv v elem body => .sendEv (concV I chv) (concV I v) elem body
  | .recvEv chv targets elem body => .recvEv (concV I chv) targets elem body

def concCell (I : Interp D) : HeapCell D → GoCore.HeapCell
  | .mk declaredTy value => ⟨declaredTy, concV I value⟩
  | .atom a => I.cellV a

def concHeap (I : Interp D) (h : Heap D) : GoCore.Heap :=
  h.map (fun (loc, cell) => (loc, concCell I cell))

/-- The state concretization is parametric in the ∀-quantified `σ`
(design §5.1's `γS`): the program tables ride from the outer binder —
the campaign's `kSt σ H na` form made structural. -/
def concS (I : Interp D) (σ : ExecState) (s : State D) : ExecState :=
  { σ with heap := concHeap I s.heap, nextAddr := s.nextAddr }

def concK (I : Interp D) : Cont D → Machine.Cont
  | .stop => .stop
  | .seq rest env k => .seq rest env (concK I k)
  | .loop c b env k => .loop c b env (concK I k)
  | .frame targets tenv results defers k w =>
      .frame targets tenv results
        (defers.map (fun (cv, args) => (concV I cv, args.map (concV I))))
        (concK I k) w
  | .deferCalleeK args env k => .deferCalleeK args env (concK I k)
  | .deferArgsK callee vals pending env k =>
      .deferArgsK (concV I callee) (vals.map (concV I)) pending env (concK I k)
  | .breakableK k => .breakableK (concK I k)
  | .labelK label k => .labelK label (concK I k)
  | .callValCalleeK targets args env k =>
      .callValCalleeK targets args env (concK I k)
  | .callValArgsK callee targets vals pending env k =>
      .callValArgsK (concV I callee) targets (vals.map (concV I)) pending env
        (concK I k)
  | .strictK op done pending env k =>
      .strictK op (done.map (concV I)) pending env (concK I k)
  | .andK right env k => .andK right env (concK I k)
  | .orK right env k => .orK right env (concK I k)
  | .boolK k => .boolK (concK I k)
  | .ifK t e env k => .ifK t e env (concK I k)
  | .whileK c b env k => .whileK c b env (concK I k)
  | .callArgsK fid targets vals pending env k =>
      .callArgsK fid targets (vals.map (concV I)) pending env (concK I k)
  | .stmtOpK op nt done pending env k =>
      .stmtOpK op nt (done.map (concV I)) pending env (concK I k)
  | .mapRangeK kv vv kt vt body env k =>
      .mapRangeK kv vv kt vt body env (concK I k)
  | .mapIterK kv vv kt vt body base produced start env k =>
      .mapIterK kv vv kt vt body base
        (produced.map (concV I)) (start.map (concV I)) env (concK I k)
  | .panicArgK k => .panicArgK (concK I k)
  | .panicResumeK chain k =>
      .panicResumeK (chain.map (concEntry I)) (concK I k)
  | .chanStK op done pending env k =>
      .chanStK op (done.map (concV I)) pending env (concK I k)
  | .selectOpsK clauses default? done pending env k =>
      .selectOpsK clauses default? (done.map (concV I)) pending env (concK I k)
  | .tgtOpK sh ops pending refs targets rop rhs vals body env k =>
      .tgtOpK sh (ops.map (concV I)) pending (refs.map (concRef I)) targets
        rop rhs (vals.map (concV I)) body env (concK I k)
  | .rhsK rop refs done pending body env k =>
      .rhsK rop (refs.map (concRef I)) (done.map (concV I)) pending body env
        (concK I k)
  | .storeK refs vals body env k =>
      .storeK (refs.map (concRef I)) (vals.map (concV I)) body env (concK I k)
  | .goCalleeK args env k => .goCalleeK args env (concK I k)
  | .goArgsK callee vals pending env k =>
      .goArgsK (concV I callee) (vals.map (concV I)) pending env (concK I k)
  | .syncStK op done pending env k =>
      .syncStK op (done.map (concV I)) pending env (concK I k)

def concC (I : Interp D) : Config D → Machine.Config
  | .exec stmt env k => .exec stmt env (concK I k)
  | .evalE e env k => .evalE e env (concK I k)
  | .retV v k => .retV (concV I v) (concK I k)
  | .next k => .next (concK I k)
  | .breaking k => .breaking (concK I k)
  | .continuing k => .continuing (concK I k)
  | .returning k => .returning (concK I k)
  | .breakingTo label k => .breakingTo label (concK I k)
  | .continuingTo label k => .continuingTo label (concK I k)
  | .panicking chain k => .panicking (chain.map (concEntry I)) (concK I k)
  | .panicked msg => .panicked msg
  | .blockedSend ch v k => .blockedSend ch (concV I v) (concK I k)
  | .blockedRecv ch targets elem env k =>
      .blockedRecv ch targets elem env (concK I k)
  | .blockedSelect clauses env k =>
      .blockedSelect (clauses.map (concClause I)) env (concK I k)
  | .opDone sc inner => .opDone sc (concC I inner)
  | .blockedSync op loc env k => .blockedSync op loc env (concK I k)

/-! ## The two interpretations -/

/-- The CONCRETE interpretation: payloads are already the machine's
values; no atoms exist. `concV cInterp` is the design §6.1 embedding
`embV` (and kin). -/
def cInterp : Interp cdom where
  intV := id
  boolV := id
  atomV := Empty.elim
  cellV := Empty.elim

/-- The concrete pack closes definitionally — which is exactly the
design's "the concrete instance's methods ARE the machine's
operations" claim, checked. -/
theorem cInterp_sound : cInterp.Sound where
  litI _ := rfl
  litB _ := rfl
  add _ _ := rfl
  sub _ _ := rfl
  mul _ _ := rfl
  divC _ _ := rfl
  modC _ _ := rfl
  neg _ := rfl
  norm _ _ := rfl
  notB _ := rfl
  eqI _ _ := rfl
  ltI _ _ := rfl
  leI _ _ := rfl
  toInt? _ _ h := Option.some.inj h
  toBool? _ _ h := Option.some.inj h

/-- The SYMBOLIC interpretation at a valuation: `concV (symInterp ρ)`
is the design §5.1 `γV ρ` (and kin). -/
def symInterp (ρ : Valuation) : Interp symDom where
  intV := γI ρ
  boolV := γB ρ
  atomV := ρ.vals
  cellV := ρ.cells

/-- The symbolic pack: the γ display equations + closedness
soundness — design §6.2's scalar leaves, discharged. -/
theorem symInterp_sound (ρ : Valuation) : (symInterp ρ).Sound where
  litI _ := rfl
  litB _ := rfl
  add _ _ := rfl
  sub _ _ := rfl
  mul _ _ := rfl
  divC _ _ := rfl
  modC _ _ := rfl
  neg _ := rfl
  norm _ _ := rfl
  notB _ := rfl
  eqI _ _ := rfl
  ltI _ _ := rfl
  leI _ _ := rfl
  toInt? _ _ h := closedI?_sound ρ h
  toBool? _ _ h := closedB?_sound ρ h

/-! ## γ-notation (the design §5's names, as abbreviations) -/

/-- `γV ρ` — symbolic value concretization (design §5.1). -/
abbrev γV (ρ : Valuation) : SymValue → GoValue := concV (symInterp ρ)

/-- `γH ρ` — symbolic heap concretization. -/
abbrev γH (ρ : Valuation) : SymHeap → GoCore.Heap := concHeap (symInterp ρ)

/-- `γS ρ σ` — symbolic state concretization over the ∀-quantified
table-carrier `σ`. -/
abbrev γS (ρ : Valuation) (σ : ExecState) (S : SymState) : ExecState :=
  concS (symInterp ρ) σ S

/-- `γK ρ` — symbolic continuation concretization. -/
abbrev γK (ρ : Valuation) : SymCont → Machine.Cont := concK (symInterp ρ)

/-- `γC ρ` — symbolic configuration concretization. -/
abbrev γC (ρ : Valuation) : SymConfig → Machine.Config := concC (symInterp ρ)

end GoLean.Sym
