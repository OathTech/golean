import GoLeanProofs.Specs.Raft.SpanS23Cells
import GoLeanProofs.Specs.Raft.SpanApplyGetters

/-!
# The spelled `main.twin.apply` + the S23 projection bridge
(A4d-SM2, vocabulary layer)

1. **The spelled `Func` + PIN**: `applyBody` — the whole lowered
   `main.twin.apply` (twin-lib.go:298-335) spelled statement-for-
   statement from the verbatim dump (`artifacts/probe/
   harvestdump.out`), with every branch a NAMED def the walk
   references; `apply_pinned` is the whole-`Func` kernel equality
   (`utoa_pinned`'s pattern — the strongest byte anchor: a
   re-lowering that reshapes `apply` turns it red).
2. **The frame entry** (`apply_enterFrame`): three pointer-argument
   cells at the frontier, targetless frame.
3. **The projection bridge** (data refinement): `projBy` maps the
   machine's slot list to the model's `byIndex` rows (`encGS` on the
   data); `lookupIdx_projBy` (first-match agreement),
   `lookupIdx_projBy_append` (machine append-if-absent ≈ model cons,
   lookup-extensionally), `s2guard_proj` (the machine's short-circuit
   `s.term != trm || s.data != data` Bool IS the model's `s2Hit`
   disagreement decision at the projection), `LookupEqB` + the
   `s23Step`/fold congruences (counters and cursors EXACT through
   folds — the bridge's `0 < violS2/violS3` predicates transfer on
   the nose).

LINEAGE: data refinement (abstraction function + operation
commutation), the `SpanS1` projection layer's pattern at the S23
state.
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.RaftSeam.UtoaSpan (twinSt)
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.SpanS1 (tyTwinD tyNodeD tidT tidN idE)
open GoLean.RaftSeam.NativeSpec (AEv S23St lookupIdx s2Hit s23Step
  s23Run)
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! ## 1. The spelled statements -/

abbrev tyEntD : Ty := .defined ⟨"raftpb.Entry"⟩
abbrev tidS : TypeId := ⟨"main.slot"⟩

/-- `nd.applied`. -/
def appliedE : Expr :=
  .fieldGet (.deref (.var "nd") tyNodeD) tidN "applied"
/-- `nd.lastTrm`. -/
def lastTrmE : Expr :=
  .fieldGet (.deref (.var "nd") tyNodeD) tidN "lastTrm"
/-- `nd.got`. -/
def gotE : Expr := .fieldGet (.deref (.var "nd") tyNodeD) tidN "got"
/-- `t.byIndex`. -/
def byIndexE : Expr :=
  .fieldGet (.deref (.var "t") tyTwinD) tidT "byIndex"
/-- `t.committed`. -/
def committedE : Expr :=
  .fieldGet (.deref (.var "t") tyTwinD) tidT "committed"

/-- A `$cN := utoa(arg)` unit. -/
def utoaUnit (c : String) (arg : Expr) : Stmt :=
  .seqn #[.initialization { id := c, typ := .string },
    .call #[.var c] ⟨"utoa"⟩ #[arg]]

/-- The S3-index violation branch (3 `utoa` calls + `viol`). -/
def s3IdxBranch : Stmt :=
  .block #[]
    #[utoaUnit "$c2298" idE,
      utoaUnit "$c2299" (.var "idx"),
      utoaUnit "$c2300" appliedE,
      .call #[] ⟨"main.twin.viol"⟩
        #[.var "t",
          .add (.add (.add (.add (.add
            (.stringLit (gs [83, 51, 32, 109, 111, 110, 111, 116, 111,
              110, 105, 99, 105, 116, 121, 58, 32, 110, 111, 100, 101,
              32]))
            (.var "$c2298"))
            (.stringLit (gs [32, 97, 112, 112, 108, 105, 101, 100, 32,
              105, 110, 100, 101, 120, 32])))
            (.var "$c2299"))
            (.stringLit (gs [32, 97, 102, 116, 101, 114, 32, 105, 110,
              100, 101, 120, 32])))
            (.var "$c2300")]]

/-- The S3-term violation branch. -/
def s3TermBranch : Stmt :=
  .block #[]
    #[utoaUnit "$c2301" idE,
      utoaUnit "$c2302" (.var "trm"),
      utoaUnit "$c2303" lastTrmE,
      .call #[] ⟨"main.twin.viol"⟩
        #[.var "t",
          .add (.add (.add (.add (.add
            (.stringLit (gs [83, 51, 32, 109, 111, 110, 111, 116, 111,
              110, 105, 99, 105, 116, 121, 58, 32, 110, 111, 100, 101,
              32]))
            (.var "$c2301"))
            (.stringLit (gs [32, 97, 112, 112, 108, 105, 101, 100, 32,
              116, 101, 114, 109, 32])))
            (.var "$c2302"))
            (.stringLit (gs [32, 97, 102, 116, 101, 114, 32, 116, 101,
              114, 109, 32])))
            (.var "$c2303")]]

/-- The anomaly branch (2 `utoa` calls + `viol` + EARLY RETURN). -/
def anomalyBranch : Stmt :=
  .block #[]
    #[utoaUnit "$c2305" idE,
      utoaUnit "$c2306" (.var "idx"),
      .call #[] ⟨"main.twin.viol"⟩
        #[.var "t",
          .add (.add (.add
            (.stringLit (gs [83, 51, 32, 97, 110, 111, 109, 97, 108,
              121, 58, 32, 110, 111, 100, 101, 32]))
            (.var "$c2305"))
            (.stringLit (gs [32, 117, 110, 109, 111, 100, 101, 108,
              101, 100, 32, 101, 110, 116, 114, 121, 32, 116, 121,
              112, 101, 32, 97, 116, 32, 105, 110, 100, 101, 120,
              32])))
            (.var "$c2306")],
      .returnStmt]

/-- The S2 violation branch (5 `utoa` calls + the 13-part concat +
`viol`). -/
def s2Branch : Stmt :=
  .block #[]
    #[utoaUnit "$c2309" (.var "idx"),
      utoaUnit "$c2310" (.fieldGet (.var "s") tidS "term"),
      utoaUnit "$c2311" (.fieldGet (.var "s") tidS "node"),
      utoaUnit "$c2312" (.var "trm"),
      utoaUnit "$c2313" idE,
      .call #[] ⟨"main.twin.viol"⟩
        #[.var "t",
          .add (.add (.add (.add (.add (.add (.add (.add (.add (.add
            (.add (.add (.add
            (.stringLit (gs [83, 50, 32, 97, 103, 114, 101, 101, 109,
              101, 110, 116, 58, 32, 105, 110, 100, 101, 120, 32]))
            (.var "$c2309"))
            (.stringLit (gs [32, 105, 115, 32, 40, 116, 101, 114, 109,
              61])))
            (.var "$c2310"))
            (.stringLit (gs [44])))
            (.fieldGet (.var "s") tidS "data"))
            (.stringLit (gs [41, 32, 111, 110, 32, 110, 111, 100, 101,
              32])))
            (.var "$c2311"))
            (.stringLit (gs [32, 98, 117, 116, 32, 40, 116, 101, 114,
              109, 61])))
            (.var "$c2312"))
            (.stringLit (gs [44])))
            (.var "data"))
            (.stringLit (gs [41, 32, 111, 110, 32, 110, 111, 100, 101,
              32])))
            (.var "$c2313")]]

/-- The S2 guard: `s.term != trm || s.data != data` (short-circuit). -/
def s2GuardE : Expr :=
  .or
    (.neqCmp (.int .uint64) (.fieldGet (.var "s") tidS "term")
      (.var "trm"))
    (.neqCmp .string (.fieldGet (.var "s") tidS "data") (.var "data"))

/-- The byIndex block: comma-ok lookup, then S2-check-or-insert. -/
def byIdxBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "s", typ := .defined tidS },
        .initialization { id := "ok", typ := .bool },
        .mapLookup (.var "s") (.var "ok") byIndexE (.var "idx")
          (.int .uint64) (.defined tidS)],
      .ifThenElse (.var "ok")
        (.block #[]
          #[.ifThenElse s2GuardE s2Branch (.seqn #[])])
        (.block #[]
          #[.mapAssign byIndexE (.var "idx")
              (.structLit (.defined tidS)
                #[.var "trm", .var "data", idE])
              (.int .uint64) (.defined tidS)])]

/-- A `$cN := Entry.getter(e)` unit. -/
def getterUnit (c : String) (ty : Ty) (getter : String) : Stmt :=
  .seqn #[.initialization { id := c, typ := ty },
    .call #[.var c] ⟨getter⟩ #[.var "e"]]

/-- **The whole `main.twin.apply` body**, spelled
(`artifacts/probe/harvestdump.out` lines 660-1023). -/
def applyBody : Stmt :=
  .block #[]
    #[getterUnit "idx" (.int .uint64) "raftpb.Entry.GetIndex",
      getterUnit "trm" (.int .uint64) "raftpb.Entry.GetTerm",
      .ifThenElse (.atMostCmp (.var "idx") appliedE)
        s3IdxBranch (.seqn #[]),
      .ifThenElse (.lessCmp (.var "trm") lastTrmE)
        s3TermBranch (.seqn #[]),
      .seqn #[.assign (.addr (.fieldAddr (.var "nd") tidN "applied"))
        (.var "idx")],
      .seqn #[.assign (.addr (.fieldAddr (.var "nd") tidN "lastTrm"))
        (.var "trm")],
      getterUnit "$c2304" (.defined ⟨"raftpb.EntryType"⟩)
        "raftpb.Entry.GetType",
      .ifThenElse (.neqCmp (.defined ⟨"raftpb.EntryType"⟩)
          (.var "$c2304") (.intLit 0 .int32))
        anomalyBranch (.seqn #[]),
      getterUnit "$c2307" (.slice (.int .uint8)) "raftpb.Entry.GetData",
      .ifThenElse (.eqCmp (.int .int)
          (.length (.var "$c2307") (some (.slice (.int .uint8))))
          (.intLit 0 .int))
        (.block #[] #[.returnStmt]) (.seqn #[]),
      getterUnit "$c2308" (.slice (.int .uint8)) "raftpb.Entry.GetData",
      .seqn #[.initialization { id := "data", typ := .string },
        .assign (.var "data")
          (.stringFromByteSlice (.var "$c2308"))],
      .mapAssign gotE (.var "data") (.boolLit true) .string .bool,
      .assign (.addr (.fieldAddr (.var "t") tidT "committed"))
        (.add committedE (.intLit 1 .int)),
      byIdxBlock]

/-- The whole `main.twin.apply` `Func`, spelled. -/
def applyFunc : Func :=
  { id := ⟨"main.twin.apply"⟩,
    args := #[{ id := "t", typ := .pointer tyTwinD },
      { id := "nd", typ := .pointer tyNodeD },
      { id := "e", typ := .pointer tyEntD }],
    results := #[],
    body := applyBody }

/-- **PIN**: the pinned lowering's `main.twin.apply` IS the spelled
function (whole-`Func` kernel equality; `#eval`'d true first,
`artifacts/probe/applypin.out`). -/
theorem apply_pinned :
    findFunctionIn? twinLowered.funcs ⟨"main.twin.apply"⟩
      = some applyFunc := by
  kernel_rfl

/-! ## 2. The frame entry -/

/-- The `apply` frame environment (params reversed, one scope — the
`viol` pattern at three arguments). -/
def applyEnv (na : Nat) : LocalEnv :=
  [[("e", .base ⟨na + 2⟩), ("nd", .base ⟨na + 1⟩), ("t", .base ⟨na⟩)]]

/-- Raw `enterFrame` at `apply` (twin tables, symbolic everything —
the three pointer arguments normalize as identities). -/
theorem apply_enterFrame (h : Heap) (na : Nat) (tw nw ew : Nat) :
    enterFrame (twinSt h na) ⟨"main.twin.apply"⟩
        [.addr (.base ⟨tw⟩), .addr (.base ⟨nw⟩), .addr (.base ⟨ew⟩)]
      = .ok (applyFunc, applyEnv na, [],
          twinSt
            (Heap.set (Heap.set (Heap.set h (.base ⟨na⟩)
                ⟨some (.pointer tyTwinD), .addr (.base ⟨tw⟩)⟩)
              (.base ⟨na + 1⟩)
                ⟨some (.pointer tyNodeD), .addr (.base ⟨nw⟩)⟩)
              (.base ⟨na + 2⟩)
                ⟨some (.pointer tyEntD), .addr (.base ⟨ew⟩)⟩)
            (na + 3)) := by
  kernel_rfl

/-! ## 3. The projection bridge -/

/-- The abstraction function: the machine's slot list down to the
model's `byIndex` rows — `(idx, term, encGS data, node)`. -/
def projBy (kvs : List (Int × SlotA)) : List (Nat × Nat × Nat × Nat) :=
  kvs.map (fun p => (p.1.toNat, p.2.1, encGS p.2.2.1, p.2.2.2))

/-- Well-formed machine keys (uint64 payloads). -/
def KeysWfB (kvs : List (Int × SlotA)) : Prop :=
  ∀ p ∈ kvs, 0 ≤ p.1 ∧ p.1 < 2 ^ 64

/-- First-match lookup agrees across the projection. -/
theorem lookupIdx_projBy {kvs : List (Int × SlotA)}
    (hwf : KeysWfB kvs) {w : Nat} (hw : w < 2 ^ 64) :
    lookupIdx (projBy kvs) w
      = (bget? kvs (w : Int)).map
          (fun s => (s.1, encGS s.2.1, s.2.2)) := by
  induction kvs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, s⟩ := p
    have hk := hwf (k, s) (List.mem_cons_self ..)
    have hrest : KeysWfB rest := fun q hq =>
      hwf q (List.mem_cons_of_mem _ hq)
    show (if k.toNat = w then some (s.1, encGS s.2.1, s.2.2) else
      lookupIdx (projBy rest) w) = _
    by_cases hke : k = (w : Int)
    · have hkn : k.toNat = w := by omega
      rw [if_pos hkn]
      show _ = (bget? ((k, s) :: rest) (w : Int)).map _
      simp [bget?, hke]
    · have hkn : k.toNat ≠ w := by omega
      rw [if_neg hkn, ih hrest]
      simp [bget?, hke]

/-- The machine's append-if-absent projects to a lookup-equal cons —
the `s23Step` byIndex transport. -/
theorem lookupIdx_projBy_append {kvs : List (Int × SlotA)}
    (hwf : KeysWfB kvs) {w : Nat} (_hw : w < 2 ^ 64)
    (hmiss : bIdxOf? kvs (w : Int) = none) (sl : SlotA) :
    ∀ i, lookupIdx (projBy (kvs ++ [((w : Int), sl)])) i
      = lookupIdx ((w, sl.1, encGS sl.2.1, sl.2.2)
          :: projBy kvs) i := by
  intro i
  induction kvs with
  | nil =>
    show (if (w : Int).toNat = i then some (sl.1, encGS sl.2.1, sl.2.2)
      else lookupIdx [] i) = _
    rw [Int.toNat_natCast]
    rfl
  | cons p rest ih =>
    obtain ⟨k, s⟩ := p
    have hk := hwf (k, s) (List.mem_cons_self ..)
    have hrest : KeysWfB rest := fun q hq =>
      hwf q (List.mem_cons_of_mem _ hq)
    have hkw : ¬ (k = (w : Int)) := by
      intro he
      simp [bIdxOf?, he] at hmiss
    have hmrest : bIdxOf? rest (w : Int) = none := by
      simp only [bIdxOf?, if_neg hkw] at hmiss
      cases hidx : bIdxOf? rest (w : Int) <;> simp [hidx] at hmiss ⊢
    have hknw : k.toNat ≠ w := by omega
    show (if k.toNat = i then some (s.1, encGS s.2.1, s.2.2) else
      lookupIdx (projBy (rest ++ [((w : Int), sl)])) i)
      = lookupIdx ((w, sl.1, encGS sl.2.1, sl.2.2)
          :: projBy ((k, s) :: rest)) i
    rw [show lookupIdx ((w, sl.1, encGS sl.2.1, sl.2.2)
        :: projBy ((k, s) :: rest)) i
      = (if w = i then some (sl.1, encGS sl.2.1, sl.2.2) else
          (if k.toNat = i then some (s.1, encGS s.2.1, s.2.2) else
            lookupIdx (projBy rest) i)) from rfl]
    by_cases hki : k.toNat = i
    · have hwine : ¬ (w = i) := fun h => hknw (by omega)
      rw [if_pos hki, if_neg hwine, if_pos hki]
    · rw [if_neg hki, ih hrest hmrest]
      show (if w = i then some (sl.1, encGS sl.2.1, sl.2.2) else
        lookupIdx (projBy rest) i) = _
      by_cases hwi : w = i
      · rw [if_pos hwi, if_pos hwi]
      · rw [if_neg hwi, if_neg hwi, if_neg hki]

/-- The machine's short-circuit S2 guard value IS the model's
disagreement decision at the projection. -/
theorem s2guard_proj (s : SlotA) (tm : Nat) (dv : GoString) :
    (!(((s.1 : Nat) : Int) == ((tm : Nat) : Int)) || !(s.2.1 == dv))
      = decide (s.1 ≠ tm ∨ encGS s.2.1 ≠ encGS dv) := by
  rw [gsBeq_encGS]
  by_cases h1 : s.1 = tm
  · subst h1
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or]
    by_cases h2 : encGS s.2.1 = encGS dv
    · rw [h2]
      simp
    · have : (encGS s.2.1 == encGS dv) = false := by
        cases hb : (encGS s.2.1 == encGS dv)
        · rfl
        · exact absurd (beq_iff_eq.mp hb) h2
      rw [this]
      simp [h2]
  · have : (((s.1 : Nat) : Int) == ((tm : Nat) : Int)) = false := by
      cases hb : (((s.1 : Nat) : Int) == ((tm : Nat) : Int))
      · rfl
      · exfalso
        apply h1
        have := beq_iff_eq.mp hb
        omega
    rw [this]
    simp [h1]

/-! ### Lookup-equality and the `s23Step` congruences -/

/-- Two model states equal on counters and cursors, lookup-extensional
on `byIndex`. -/
def LookupEqB (st st' : S23St) : Prop :=
  (∀ i, lookupIdx st.byIndex i = lookupIdx st'.byIndex i)
    ∧ st.applied = st'.applied ∧ st.lastTrm = st'.lastTrm
    ∧ st.violS2 = st'.violS2 ∧ st.violS3 = st'.violS3

theorem LookupEqB.refl (st : S23St) : LookupEqB st st :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl⟩

theorem s2Hit_congr {st st' : S23St} (h : LookupEqB st st')
    (e : AEv) : s2Hit st e = s2Hit st' e := by
  unfold s2Hit
  rw [h.1 e.idx]

theorem s23Step_congr {st st' : S23St} (h : LookupEqB st st')
    (e : AEv) : LookupEqB (s23Step st e) (s23Step st' e) := by
  obtain ⟨hby, hap, hlt, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show lookupIdx (if e.data = 0 then st.byIndex else _) i
      = lookupIdx (if e.data = 0 then st'.byIndex else _) i
    by_cases hd : e.data = 0
    · simp only [if_pos hd]
      exact hby i
    · simp only [if_neg hd, hby e.idx]
      cases hidx : lookupIdx st'.byIndex e.idx with
      | some p => exact hby i
      | none =>
        show lookupIdx ((e.idx, e.trm, e.data, e.node) :: st.byIndex) i
          = lookupIdx ((e.idx, e.trm, e.data, e.node) :: st'.byIndex) i
        show (if e.idx = i then _ else lookupIdx st.byIndex i)
          = (if e.idx = i then _ else lookupIdx st'.byIndex i)
        by_cases hi : e.idx = i
        · rw [if_pos hi, if_pos hi]
        · rw [if_neg hi, if_neg hi]
          exact hby i
  · show (fun n => if n = e.node then e.idx else st.applied n) = _
    funext n
    rw [hap]
    rfl
  · show (fun n => if n = e.node then e.trm else st.lastTrm n) = _
    funext n
    rw [hlt]
    rfl
  · show st.violS2 + s2Hit st e = st'.violS2 + s2Hit st' e
    rw [h2, s2Hit_congr ⟨hby, hap, hlt, h2, h3⟩ e]
  · show st.violS3 + _ + _ = st'.violS3 + _ + _
    rw [h3, hap, hlt]

/-- Fold congruence: lookup-equal starts fold to lookup-equal ends. -/
theorem s23Fold_congr {st st' : S23St} (h : LookupEqB st st') :
    ∀ evs : List AEv,
      LookupEqB (evs.foldl s23Step st) (evs.foldl s23Step st') := by
  intro evs
  induction evs generalizing st st' with
  | nil => exact h
  | cons e rest ih =>
    simp only [List.foldl_cons]
    exact ih (s23Step_congr h e)

end GoLean.RaftSeam.SpanS23
