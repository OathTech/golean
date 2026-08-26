import GoLeanProofs.Specs.Raft.SpanS23Apply

/-!
# The apply walk, part 1 (A4d-SM2): shared units + the getters prelude

Split from the walk proper for iteration speed (the SM1 file-split
convention). Contents:

1. **`sliceVisibleValues_of_array`** — the Data slice's visible bytes
   from the backing-array window (first-order premises: the array
   cell + the pointwise window fact), so the span theorem never
   quantifies over states.
2. **`utoaUnit_walk`** — ONE generic walk of a `$c := utoa(arg)` unit
   (splice/init/call-plan glue + `utoa_call_span`), parameterized by
   the argument-delivery fact at the post-init state. The thirteen
   `utoa` call sites across the four violation branches all ride this
   lemma (the lift-repeated-patterns rule — SpanS1Walk paid this
   shape inline three times; SM2 has thirteen).
3. **The spelled body segments** (named views of `applyBody`'s
   statement list) + **`s23_getters_seg`** — the deterministic
   118-step prelude: frame entry, `idx`/`trm` delivered by the two
   pinned getter call spans, landing on the S3-index guard.
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.SpanS1 (tyTwinD tyNodeD tidT tidN idE)
open GoLean.RaftSeam.SpanApplyGetters
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! ## 1. The Data window -/

private theorem forIn_push_eq {α : Type}
    {body : α → Array GoValue → Except GoError (ForInStep (Array GoValue))}
    {g : α → GoValue} :
    ∀ (l : List α),
      (∀ x ∈ l, ∀ r, body x r = .ok (.yield (r.push (g x)))) →
    ∀ (acc : Array GoValue),
      forIn l acc body = .ok (acc ++ (l.map g).toArray)
  | [], _, acc => by simp [List.forIn_nil, pure, Except.pure]
  | x :: xs, hshape, acc => by
    rw [List.forIn_cons, hshape x (by simp) acc]
    simp only [Bind.bind, Except.bind]
    rw [forIn_push_eq xs (fun y hy r => hshape y (by simp [hy]) r)
      (acc.push (g x))]
    simp

/-- The visible values of a slice over an array-cell window: the
byte list, elementwise (first-order premises — the walk transports
the array-cell fact through its frame clauses). -/
theorem sliceVisibleValues_of_array {σ : ExecState} {da : Nat}
    {dty : Option Ty} {arr : Array GoValue} {off cap : Nat}
    {bs : List UInt8}
    (harr : Heap.lookup σ.heap (.base ⟨da⟩) = some ⟨dty, .array arr⟩)
    (hwin : ∀ i, (hi : i < bs.length) →
      arr[off + i]? = some (.int ((bs[i].toNat : Int)) .uint8))
    (hcap : bs.length ≤ cap) :
    sliceVisibleValues σ ⟨some (.base ⟨da⟩), off, bs.length, cap⟩
      = .ok (bytesArr bs) := by
  unfold sliceVisibleValues
  rw [show validateSlice ⟨some (.base ⟨da⟩), off, bs.length, cap⟩
      = .ok () from by
    simp [validateSlice, Nat.not_lt.mpr hcap]]
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show ([:bs.length] : Std.Legacy.Range).size = bs.length from by
    simp [Std.Legacy.Range.size]]
  rw [forIn_push_eq (g := fun i =>
    match bs[i]? with
    | some b => .int ((b.toNat : Int)) .uint8
    | none => .nil) (List.range' 0 bs.length 1) ?hsh #[]]
  case hsh =>
    intro x hx r
    have hxlt : x < bs.length := by
      have := List.mem_range'_1.mp hx
      omega
    have hget := hwin x hxlt
    have hsz : off + x < arr.size := by
      rcases Nat.lt_or_ge (off + x) arr.size with h | hge
      · exact h
      · exfalso
        rw [Array.getElem?_eq_none (by omega)] at hget
        cases hget
    have hidxnat : arrayIndexNat arr (Int.ofNat (off + x))
        = .ok (off + x) := by
      simp only [arrayIndexNat]
      rw [if_neg (show ¬ ((Int.ofNat (off + x)) < 0) from by
        rw [show Int.ofNat (off + x) = ((off + x : Nat) : Int) from
          rfl]
        omega)]
      rw [show (Int.ofNat (off + x)).toNat = off + x from
        Int.toNat_natCast _]
      rw [if_pos hsz]
      rfl
    have hload : loadLoc σ (.index (.base ⟨da⟩) (Int.ofNat (off + x)))
        = .ok (.int ((bs[x].toNat : Int)) .uint8) := by
      simp only [loadLoc, harr, Bind.bind, Except.bind, pure,
        Except.pure, arrayGet, hidxnat, hget]
    have hidxloc : sliceIndexLoc
        ⟨some (.base ⟨da⟩), off, bs.length, cap⟩ (Int.ofNat x)
        = .ok (.index (.base ⟨da⟩) (Int.ofNat (off + x))) := by
      simp only [sliceIndexLoc, validateSlice, Bind.bind, Except.bind,
        pure, Except.pure]
      rw [if_neg (show ¬ (bs.length > cap) from Nat.not_lt.mpr hcap)]
      rw [if_neg (show ¬ ((Int.ofNat x) < 0) from by
        rw [show Int.ofNat x = ((x : Nat) : Int) from rfl]
        omega)]
      rw [show (Int.ofNat x).toNat = x from Int.toNat_natCast _]
      show (if x < bs.length then
          Except.ok ((Loc.base ⟨da⟩).index (Int.ofNat (off + x)))
        else indexOutOfRangePanic (Int.ofNat x) bs.length) = _
      rw [if_pos hxlt]
    simp only [hidxloc, hload, List.getElem?_eq_getElem hxlt]
  rw [show (#[] : Array GoValue)
      ++ (List.map (fun i =>
        match bs[i]? with
        | some b => GoValue.int ((b.toNat : Int)) .uint8
        | none => GoValue.nil) (List.range' 0 bs.length)).toArray
    = bytesArr bs from by
      apply Array.ext'
      simp only [Array.toList_append, List.nil_append, bytesArr]
      apply List.ext_getElem
      · simp
      · intro j hj hj2
        have hjn : j < bs.length := by
          simp only [List.length_map, List.length_range'] at hj
          omega
        simp only [List.getElem_map]
        rw [show (List.range' 0 bs.length)[j]'(by simp; omega) = j
          from by simp [List.getElem_range']]
        rw [List.getElem?_eq_getElem hjn]]

/-! ## 2. The generic `utoa` unit -/

/-- **ONE `$c := utoa(arg)` unit walk** (splice/init/call-plan glue +
`utoa_call_span`): from the unit under its governing sequence to the
caller's resumption, the fresh `c` cell holding SOME string (the
banked weak form). The argument-delivery fact enters at the post-init
state; the thirteen call sites across the four violation branches all
ride this lemma. -/
theorem utoaUnit_walk {envQ : LocalEnv} {rest : List Stmt} {K : Cont}
    {c : String} {argE : Expr} {ka : Nat} {av : Nat}
    (σ0 : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ0)
    (hfr : ∀ x, σ0.nextAddr ≤ x →
      Heap.lookup σ0.heap (.base ⟨x⟩) = none)
    (hav : av < 2 ^ 64)
    (henvc : LocalEnv.lookup (envQ.declare c (.base ⟨σ0.nextAddr⟩)) c
      = some (.base ⟨σ0.nextAddr⟩))
    (harg : stepFnIter ka
        { σ0 with heap := Heap.set σ0.heap (.base ⟨σ0.nextAddr⟩) (sCell (gs [])), nextAddr := σ0.nextAddr + 1 }
        (.evalE argE (envQ.declare c (.base ⟨σ0.nextAddr⟩))
          (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref c])] [] []
            (envQ.declare c (.base ⟨σ0.nextAddr⟩))
            (.seq rest (envQ.declare c (.base ⟨σ0.nextAddr⟩)) K))) ch
      = .ok (.retV (.int (av : Int) .uint64)
          (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref c])] [] []
            (envQ.declare c (.base ⟨σ0.nextAddr⟩))
            (.seq rest (envQ.declare c (.base ⟨σ0.nextAddr⟩)) K)),
        { σ0 with heap := Heap.set σ0.heap (.base ⟨σ0.nextAddr⟩) (sCell (gs [])), nextAddr := σ0.nextAddr + 1 }, ch)) :
    ∃ m ≤ ka + 1572, ∃ str : GoString, ∃ σU : ExecState,
      stepFnIter m σ0
          (.exec (utoaUnit c argE) envQ (.seq rest envQ K)) ch
        = .ok (.exec (.seqn #[])
            (envQ.declare c (.base ⟨σ0.nextAddr⟩))
            (.seq rest (envQ.declare c (.base ⟨σ0.nextAddr⟩)) K),
          σU, ch)
      ∧ Heap.lookup σU.heap (.base ⟨σ0.nextAddr⟩) = some (sCell str)
      ∧ σ0.nextAddr + 3 ≤ σU.nextAddr ∧ σU.nextAddr ≤ σ0.nextAddr + 5
      ∧ (∀ x, x < σ0.nextAddr →
          Heap.lookup σU.heap (.base ⟨x⟩)
            = Heap.lookup σ0.heap (.base ⟨x⟩))
      ∧ (∀ x, σU.nextAddr ≤ x →
          Heap.lookup σU.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σU := by
  let env' : LocalEnv := envQ.declare c (.base ⟨σ0.nextAddr⟩)
  let σF : ExecState := { σ0 with heap := Heap.set σ0.heap (.base ⟨σ0.nextAddr⟩) (sCell (gs [])), nextAddr := σ0.nextAddr + 1 }
  -- U1: splice + pop (2)
  have hU1 : stepFnIter 2 σ0
      (.exec (utoaUnit c argE) envQ (.seq rest envQ K)) ch
      = .ok (.exec (.initialization { id := c, typ := .string }) envQ
          (.seq (.call #[.var c] ⟨"utoa"⟩ #[argE] :: rest) envQ K),
        σ0, ch) :=
    stepFnIter_splice_pop
      (ss := #[.initialization { id := c, typ := .string },
        .call #[.var c] ⟨"utoa"⟩ #[argE]]) rfl
  -- U2: init (1)
  have hU2 : stepFnIter 1 σ0
      (.exec (.initialization { id := c, typ := .string }) envQ
        (.seq (.call #[.var c] ⟨"utoa"⟩ #[argE] :: rest) envQ K)) ch
      = .ok (.next (.seq (.call #[.var c] ⟨"utoa"⟩ #[argE] :: rest)
          env' K), σF, ch) :=
    stepFnIter_one (stepFn_init_seq (hdef := defaultValue_string))
  -- U3: pop (1)
  have hU3 : stepFnIter 1 σF
      (.next (.seq (.call #[.var c] ⟨"utoa"⟩ #[argE] :: rest)
        env' K)) ch
      = .ok (.exec (.call #[.var c] ⟨"utoa"⟩ #[argE]) env'
          (.seq rest env' K), σF, ch) :=
    stepFnIter_one stepFn_seq_pop
  -- U4: the call plan (1)
  have hU4 : stepFnIter 1 σF
      (.exec (.call #[.var c] ⟨"utoa"⟩ #[argE]) env'
        (.seq rest env' K)) ch
      = .ok (.evalE argE env'
          (.callArgsK ⟨"utoa"⟩ [(.chain [], [.ref c])] [] [] env'
            (.seq rest env' K)), σF, ch) := by
    with_unfolding_all rfl
  -- U6: the utoa call span at σF
  have hσFag : bfTB.Agrees σF := hag
  have htcF : Heap.lookup σF.heap (.base ⟨σ0.nextAddr⟩)
      = some (sCell (gs [])) := lookup_set_self
  have hfrF : ∀ x, σF.nextAddr ≤ x →
      Heap.lookup σF.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx1 : σ0.nextAddr + 1 ≤ x := hx
    show Heap.lookup (Heap.set σ0.heap (.base ⟨σ0.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ0.nextAddr ≠ x)]
    exact hfr x (by omega)
  obtain ⟨mU, hmU, str, σ', hrun, hcell, hna, hfrm, hfrs, hagU⟩ :=
    utoa_call_span (envC := env') (tgt := c)
      (ltc := σ0.nextAddr) (Kc := .seq rest env' K)
      henvc hav σF ch (gs []) hσFag htcF hfrF
  refine ⟨2 + 1 + 1 + 1 + ka + mU, ?_, str, σ', ?_, hcell, ?_, ?_,
    ?_, hfrs, hagU⟩
  · have h20 := GoLean.RaftSeam.SpanS1.dig10_le20 hav
    omega
  · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hU1 hU2) hU3) hU4) harg)
      hrun
  · rw [hna]
    show σ0.nextAddr + 3 ≤ σ0.nextAddr + 1 + 2 + _
    split <;> omega
  · rw [hna]
    show σ0.nextAddr + 1 + 2 + _ ≤ σ0.nextAddr + 5
    split <;> omega
  · intro x hx
    rw [hfrm x (by show x < σ0.nextAddr + 1; omega) (by omega)]
    show Heap.lookup (Heap.set σ0.heap (.base ⟨σ0.nextAddr⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (by omega : σ0.nextAddr ≠ x)]

/-! ## 3. Named views of the body + the getters prelude -/

/-- The uint64 default (any state; `SpanS1Walk` keeps its own copy —
this module does not import the S1 walk). -/
theorem defaultValue_u64' {σ : ExecState} :
    defaultValue σ (.int .uint64) = .ok (.int 0 .uint64) := by
  with_unfolding_all rfl

def s3IdxIfS : Stmt :=
  .ifThenElse (.atMostCmp (.var "idx") appliedE) s3IdxBranch (.seqn #[])
def s3TermIfS : Stmt :=
  .ifThenElse (.lessCmp (.var "trm") lastTrmE) s3TermBranch (.seqn #[])
def appliedAsn : Stmt :=
  .seqn #[.assign (.addr (.fieldAddr (.var "nd") tidN "applied"))
    (.var "idx")]
def lastTrmAsn : Stmt :=
  .seqn #[.assign (.addr (.fieldAddr (.var "nd") tidN "lastTrm"))
    (.var "trm")]
def anomalyIfS : Stmt :=
  .ifThenElse (.neqCmp (.defined ⟨"raftpb.EntryType"⟩)
    (.var "$c2304") (.intLit 0 .int32)) anomalyBranch (.seqn #[])
def lenIfS : Stmt :=
  .ifThenElse (.eqCmp (.int .int)
      (.length (.var "$c2307") (some (.slice (.int .uint8))))
      (.intLit 0 .int))
    (.block #[] #[.returnStmt]) (.seqn #[])
def dataAsn : Stmt :=
  .seqn #[.initialization { id := "data", typ := .string },
    .assign (.var "data") (.stringFromByteSlice (.var "$c2308"))]
def gotAsn : Stmt :=
  .mapAssign gotE (.var "data") (.boolLit true) .string .bool
def commitAsn : Stmt :=
  .assign (.addr (.fieldAddr (.var "t") tidT "committed"))
    (.add committedE (.intLit 1 .int))

/-- The statements after the two getter units. -/
def restAfterGetters : List Stmt :=
  [s3IdxIfS, s3TermIfS, appliedAsn, lastTrmAsn,
    getterUnit "$c2304" (.defined ⟨"raftpb.EntryType"⟩)
      "raftpb.Entry.GetType",
    anomalyIfS,
    getterUnit "$c2307" (.slice (.int .uint8)) "raftpb.Entry.GetData",
    lenIfS,
    getterUnit "$c2308" (.slice (.int .uint8)) "raftpb.Entry.GetData",
    dataAsn, gotAsn, commitAsn, byIdxBlock]

theorem applyBody_view : applyBody = .block #[]
    ⟨getterUnit "idx" (.int .uint64) "raftpb.Entry.GetIndex"
      :: getterUnit "trm" (.int .uint64) "raftpb.Entry.GetTerm"
      :: restAfterGetters⟩ := rfl

/-- The targetless apply frame. -/
abbrev FKa (envC : LocalEnv) (Kc : Cont) : Cont :=
  .frame [] envC [] [] Kc false

/-- The env after the two getter declarations. -/
def envG2 (na : Nat) : LocalEnv :=
  [("trm", .base ⟨na + 6⟩), ("idx", .base ⟨na + 3⟩)] :: applyEnv na

/-- The three frame-argument cells. -/
abbrev tParA (tw : Nat) : HeapCell :=
  ⟨some (.pointer tyTwinD), .addr (.base ⟨tw⟩)⟩
abbrev ndParA (nw : Nat) : HeapCell :=
  ⟨some (.pointer tyNodeD), .addr (.base ⟨nw⟩)⟩
abbrev eParA (ew : Nat) : HeapCell :=
  ⟨some (.pointer tyEntD), .addr (.base ⟨ew⟩)⟩

/-- The state after the getters prelude: the three frame cells, the
`idx`/`trm` cells (delivered), the two getter frames' dead cells —
the exact set-nest the two pinned call spans produce, frontier `+9`. -/
def gettersSt (tw nw ew : Nat) (ixN tmN : Nat) (σ : ExecState) :
    ExecState :=
  twinSt
    (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (tParA tw))
        (.base ⟨σ.nextAddr + 1⟩) (ndParA nw))
        (.base ⟨σ.nextAddr + 2⟩) (eParA ew))
        (.base ⟨σ.nextAddr + 3⟩) ⟨some (.int .uint64), .int 0 .uint64⟩)
        (.base ⟨σ.nextAddr + 4⟩) (xCell ew))
        (.base ⟨σ.nextAddr + 5⟩)
          ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
        (.base ⟨σ.nextAddr + 3⟩)
          ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
        (.base ⟨σ.nextAddr + 6⟩) ⟨some (.int .uint64), .int 0 .uint64⟩)
        (.base ⟨σ.nextAddr + 7⟩) (xCell ew))
        (.base ⟨σ.nextAddr + 8⟩)
          ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩)
        (.base ⟨σ.nextAddr + 6⟩)
          ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩)
    (σ.nextAddr + 9)

section Getters

variable {envC : LocalEnv} {Kc : Cont} {tw nw ew li lt2 : Nat}
  {dtyEw dtyI dtyT2 : Option Ty} {fsE : Array (String × GoValue)}
  {ixN tmN : Nat}

/-- **The getters prelude** (117 steps): frame entry, `idx := 
Entry.GetIndex(e)`, `trm := Entry.GetTerm(e)`, landing on the
S3-index guard with both values delivered. -/
theorem s23_getters_seg
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hEw : Heap.lookup σ.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hfI : StructFields.lookup fsE "Index" = some (.addr (.base ⟨li⟩)))
    (hfT : StructFields.lookup fsE "Term" = some (.addr (.base ⟨lt2⟩)))
    (hIc : Heap.lookup σ.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int (ixN : Int) .uint64⟩)
    (hTc : Heap.lookup σ.heap (.base ⟨lt2⟩)
      = some ⟨dtyT2, .int (tmN : Int) .uint64⟩)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (hix : ixN < 2 ^ 64) (htm : tmN < 2 ^ 64) :
    stepFnIter 117 σ (.retV (.addr (.base ⟨ew⟩))
        (.callArgsK ⟨"main.twin.apply"⟩ []
          [.addr (.base ⟨tw⟩), .addr (.base ⟨nw⟩)] [] envC Kc)) ch
      = .ok (.exec s3IdxIfS (envG2 σ.nextAddr)
          (.seq (restAfterGetters.tail) (envG2 σ.nextAddr)
            (FKa envC Kc)),
        gettersSt tw nw ew ixN tmN σ, ch) := by
  have hσ := twinSt_of_agrees hag
  -- bounds
  have hewna : ew < σ.nextAddr := by
    rcases Nat.lt_or_ge ew σ.nextAddr with h | h
    · exact h
    · rw [hfr ew h] at hEw; cases hEw
  have hlina : li < σ.nextAddr := by
    rcases Nat.lt_or_ge li σ.nextAddr with h | h
    · exact h
    · rw [hfr li h] at hIc; cases hIc
  have hlt2na : lt2 < σ.nextAddr := by
    rcases Nat.lt_or_ge lt2 σ.nextAddr with h | h
    · exact h
    · rw [hfr lt2 h] at hTc; cases hTc
  -- G1: the frame entry (1)
  have henter : enterFrame σ ⟨"main.twin.apply"⟩
      [.addr (.base ⟨tw⟩), .addr (.base ⟨nw⟩), .addr (.base ⟨ew⟩)]
      = .ok (applyFunc, applyEnv σ.nextAddr, [],
        twinSt (Heap.set (Heap.set (Heap.set σ.heap
            (.base ⟨σ.nextAddr⟩) (tParA tw))
            (.base ⟨σ.nextAddr + 1⟩) (ndParA nw))
            (.base ⟨σ.nextAddr + 2⟩) (eParA ew))
          (σ.nextAddr + 3)) := by
    have h0 := apply_enterFrame σ.heap σ.nextAddr tw nw ew
    rw [← hσ] at h0
    exact h0
  let σ1 : ExecState := twinSt (Heap.set (Heap.set (Heap.set σ.heap
    (.base ⟨σ.nextAddr⟩) (tParA tw))
    (.base ⟨σ.nextAddr + 1⟩) (ndParA nw))
    (.base ⟨σ.nextAddr + 2⟩) (eParA ew)) (σ.nextAddr + 3)
  have hG1 : stepFnIter 1 σ (.retV (.addr (.base ⟨ew⟩))
      (.callArgsK ⟨"main.twin.apply"⟩ []
        [.addr (.base ⟨tw⟩), .addr (.base ⟨nw⟩)] [] envC Kc)) ch
      = .ok (.exec applyBody (applyEnv σ.nextAddr) (FKa envC Kc),
        σ1, ch) :=
    stepFnIter_one (stepFn_call_enter
      (vals := [.addr (.base ⟨tw⟩), .addr (.base ⟨nw⟩)])
      (v := .addr (.base ⟨ew⟩)) (h := henter))
  -- G2: block + pop (2)
  have hG2 : stepFnIter 2 σ1
      (.exec applyBody (applyEnv σ.nextAddr) (FKa envC Kc)) ch
      = .ok (.exec (getterUnit "idx" (.int .uint64)
            "raftpb.Entry.GetIndex") ([] :: applyEnv σ.nextAddr)
          (.seq (getterUnit "trm" (.int .uint64)
              "raftpb.Entry.GetTerm" :: restAfterGetters)
            ([] :: applyEnv σ.nextAddr) (FKa envC Kc)), σ1, ch) := by
    rw [applyBody_view]
    exact stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- G3: idx unit prelude (2+1+1+1+1 = 6)
  let envI : LocalEnv :=
    [("idx", .base ⟨σ.nextAddr + 3⟩)] :: applyEnv σ.nextAddr
  let σI : ExecState := { σ1 with heap := Heap.set σ1.heap (.base ⟨σ.nextAddr + 3⟩) ⟨some (.int .uint64), .int 0 .uint64⟩, nextAddr := σ.nextAddr + 4 }
  let KIseq : Cont := .seq restAfterGetters envI (FKa envC Kc)
  have hG3 : stepFnIter 6 σ1
      (.exec (getterUnit "idx" (.int .uint64) "raftpb.Entry.GetIndex")
        ([] :: applyEnv σ.nextAddr)
        (.seq (getterUnit "trm" (.int .uint64) "raftpb.Entry.GetTerm"
            :: restAfterGetters)
          ([] :: applyEnv σ.nextAddr) (FKa envC Kc))) ch
      = .ok (.retV (.addr (.base ⟨ew⟩))
          (.callArgsK ⟨"raftpb.Entry.GetIndex"⟩
            [(.chain [], [.ref "idx"])] [] [] envI
            (.seq (getterUnit "trm" (.int .uint64)
                "raftpb.Entry.GetTerm" :: restAfterGetters)
              envI (FKa envC Kc))), σI, ch) := by
    have g1 : stepFnIter 2 σ1
        (.exec (getterUnit "idx" (.int .uint64)
          "raftpb.Entry.GetIndex") ([] :: applyEnv σ.nextAddr)
          (.seq (getterUnit "trm" (.int .uint64)
              "raftpb.Entry.GetTerm" :: restAfterGetters)
            ([] :: applyEnv σ.nextAddr) (FKa envC Kc))) ch
        = .ok (.exec (.initialization { id := "idx", typ := .int .uint64 })
            ([] :: applyEnv σ.nextAddr)
            (.seq (.call #[.var "idx"] ⟨"raftpb.Entry.GetIndex"⟩
                #[.var "e"] :: getterUnit "trm" (.int .uint64)
                "raftpb.Entry.GetTerm" :: restAfterGetters)
              ([] :: applyEnv σ.nextAddr) (FKa envC Kc)), σ1, ch) :=
      stepFnIter_splice_pop
        (ss := #[.initialization { id := "idx", typ := .int .uint64 },
          .call #[.var "idx"] ⟨"raftpb.Entry.GetIndex"⟩ #[.var "e"]])
        rfl
    have g2 : stepFnIter 1 σ1
        (.exec (.initialization { id := "idx", typ := .int .uint64 })
          ([] :: applyEnv σ.nextAddr)
          (.seq (.call #[.var "idx"] ⟨"raftpb.Entry.GetIndex"⟩
              #[.var "e"] :: getterUnit "trm" (.int .uint64)
              "raftpb.Entry.GetTerm" :: restAfterGetters)
            ([] :: applyEnv σ.nextAddr) (FKa envC Kc))) ch
        = .ok (.next (.seq (.call #[.var "idx"]
              ⟨"raftpb.Entry.GetIndex"⟩ #[.var "e"]
              :: getterUnit "trm" (.int .uint64)
              "raftpb.Entry.GetTerm" :: restAfterGetters)
            envI (FKa envC Kc)), σI, ch) :=
      stepFnIter_one (stepFn_init_seq
        (hdef := defaultValue_u64'))
    have g3 : stepFnIter 1 σI (.next (.seq (.call #[.var "idx"]
          ⟨"raftpb.Entry.GetIndex"⟩ #[.var "e"]
          :: getterUnit "trm" (.int .uint64) "raftpb.Entry.GetTerm"
          :: restAfterGetters) envI (FKa envC Kc))) ch
        = .ok (.exec (.call #[.var "idx"] ⟨"raftpb.Entry.GetIndex"⟩
            #[.var "e"]) envI
            (.seq (getterUnit "trm" (.int .uint64)
                "raftpb.Entry.GetTerm" :: restAfterGetters)
              envI (FKa envC Kc)), σI, ch) :=
      stepFnIter_one stepFn_seq_pop
    have g4 : stepFnIter 1 σI (.exec (.call #[.var "idx"]
        ⟨"raftpb.Entry.GetIndex"⟩ #[.var "e"]) envI
        (.seq (getterUnit "trm" (.int .uint64)
            "raftpb.Entry.GetTerm" :: restAfterGetters)
          envI (FKa envC Kc))) ch
        = .ok (.evalE (.var "e") envI
            (.callArgsK ⟨"raftpb.Entry.GetIndex"⟩
              [(.chain [], [.ref "idx"])] [] [] envI
              (.seq (getterUnit "trm" (.int .uint64)
                  "raftpb.Entry.GetTerm" :: restAfterGetters)
                envI (FKa envC Kc))), σI, ch) := by
      with_unfolding_all rfl
    have heI : Heap.lookup σI.heap (.base ⟨σ.nextAddr + 2⟩)
        = some (eParA ew) := by
      show Heap.lookup (Heap.set _ (.base ⟨σ.nextAddr + 3⟩) _)
        (.base ⟨σ.nextAddr + 2⟩) = _
      rw [lookup_set_other (by omega : σ.nextAddr + 3 ≠ σ.nextAddr + 2)]
      exact lookup_set_self
    have g5 : stepFnIter 1 σI (.evalE (.var "e") envI
        (.callArgsK ⟨"raftpb.Entry.GetIndex"⟩
          [(.chain [], [.ref "idx"])] [] [] envI
          (.seq (getterUnit "trm" (.int .uint64)
              "raftpb.Entry.GetTerm" :: restAfterGetters)
            envI (FKa envC Kc)))) ch
        = .ok (.retV (.addr (.base ⟨ew⟩))
            (.callArgsK ⟨"raftpb.Entry.GetIndex"⟩
              [(.chain [], [.ref "idx"])] [] [] envI
              (.seq (getterUnit "trm" (.int .uint64)
                  "raftpb.Entry.GetTerm" :: restAfterGetters)
                envI (FKa envC Kc))), σI, ch) :=
      stepFnIter_one (stepFn_var (henv := rfl) (hlook := heI))
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain g1 g2) g3) g4) g5
  -- G4: the GetIndex call span (49)
  have hEwI : Heap.lookup σI.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 2⟩) _) (.base ⟨σ.nextAddr + 3⟩) _)
      (.base ⟨ew⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 3 ≠ ew),
      lookup_set_other (by omega : σ.nextAddr + 2 ≠ ew),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ ew),
      lookup_set_other (by omega : σ.nextAddr ≠ ew)]
    exact hEw
  have hIcI : Heap.lookup σI.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int (ixN : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 2⟩) _) (.base ⟨σ.nextAddr + 3⟩) _)
      (.base ⟨li⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 3 ≠ li),
      lookup_set_other (by omega : σ.nextAddr + 2 ≠ li),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ li),
      lookup_set_other (by omega : σ.nextAddr ≠ li)]
    exact hIc
  have hTcI : Heap.lookup σI.heap (.base ⟨lt2⟩)
      = some ⟨dtyT2, .int (tmN : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 2⟩) _) (.base ⟨σ.nextAddr + 3⟩) _)
      (.base ⟨lt2⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 3 ≠ lt2),
      lookup_set_other (by omega : σ.nextAddr + 2 ≠ lt2),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ lt2),
      lookup_set_other (by omega : σ.nextAddr ≠ lt2)]
    exact hTc
  have hfrI : ∀ x, σI.nextAddr ≤ x →
      Heap.lookup σI.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx4 : σ.nextAddr + 4 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
      (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 2⟩) _) (.base ⟨σ.nextAddr + 3⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr + 3 ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 2 ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ.nextAddr ≠ x)]
    exact hfr x (by omega)
  have hG4 := getIndex_call_span (envC := envI) (tgt := "idx")
    (ltc := σ.nextAddr + 3)
    (Kc := .seq (getterUnit "trm" (.int .uint64)
        "raftpb.Entry.GetTerm" :: restAfterGetters) envI
      (FKa envC Kc))
    rfl hix σI ch (⟨rfl, rfl, rfl, rfl⟩ : bfTB.Agrees σI) hEwI hfI
    hIcI lookup_set_self hfrI (by omega) (by omega)
  -- the state after GetIndex
  let σI' : ExecState := twinSt (Heap.set (Heap.set (Heap.set σI.heap
    (.base ⟨σI.nextAddr⟩) (xCell ew)) (.base ⟨σI.nextAddr + 1⟩)
    ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
    (.base ⟨σ.nextAddr + 3⟩)
    ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
    (σI.nextAddr + 2)
  -- G5: drain (2)
  have hG5 : stepFnIter 2 σI'
      (.exec (.seqn #[]) envI
        (.seq (getterUnit "trm" (.int .uint64)
            "raftpb.Entry.GetTerm" :: restAfterGetters) envI
          (FKa envC Kc))) ch
      = .ok (.exec (getterUnit "trm" (.int .uint64)
            "raftpb.Entry.GetTerm") envI
          (.seq restAfterGetters envI (FKa envC Kc)), σI', ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- G6: trm unit prelude (6)
  let σT : ExecState := { σI' with heap := Heap.set σI'.heap (.base ⟨σ.nextAddr + 6⟩) ⟨some (.int .uint64), .int 0 .uint64⟩, nextAddr := σ.nextAddr + 7 }
  have hG6 : stepFnIter 6 σI'
      (.exec (getterUnit "trm" (.int .uint64) "raftpb.Entry.GetTerm")
        envI (.seq restAfterGetters envI (FKa envC Kc))) ch
      = .ok (.retV (.addr (.base ⟨ew⟩))
          (.callArgsK ⟨"raftpb.Entry.GetTerm"⟩
            [(.chain [], [.ref "trm"])] [] [] (envG2 σ.nextAddr)
            (.seq restAfterGetters (envG2 σ.nextAddr)
              (FKa envC Kc))), σT, ch) := by
    have g1 : stepFnIter 2 σI'
        (.exec (getterUnit "trm" (.int .uint64)
          "raftpb.Entry.GetTerm") envI
          (.seq restAfterGetters envI (FKa envC Kc))) ch
        = .ok (.exec (.initialization { id := "trm", typ := .int .uint64 })
            envI
            (.seq (.call #[.var "trm"] ⟨"raftpb.Entry.GetTerm"⟩
                #[.var "e"] :: restAfterGetters)
              envI (FKa envC Kc)), σI', ch) :=
      stepFnIter_splice_pop
        (ss := #[.initialization { id := "trm", typ := .int .uint64 },
          .call #[.var "trm"] ⟨"raftpb.Entry.GetTerm"⟩ #[.var "e"]])
        rfl
    have g2 : stepFnIter 1 σI'
        (.exec (.initialization { id := "trm", typ := .int .uint64 })
          envI
          (.seq (.call #[.var "trm"] ⟨"raftpb.Entry.GetTerm"⟩
              #[.var "e"] :: restAfterGetters)
            envI (FKa envC Kc))) ch
        = .ok (.next (.seq (.call #[.var "trm"]
              ⟨"raftpb.Entry.GetTerm"⟩ #[.var "e"]
              :: restAfterGetters)
            (envG2 σ.nextAddr) (FKa envC Kc)), σT, ch) := by
      have h0 := stepFn_init_seq (σ := σI')
        (p := { id := "trm", typ := .int .uint64 })
        (rest := .call #[.var "trm"] ⟨"raftpb.Entry.GetTerm"⟩
            #[.var "e"] :: restAfterGetters)
        (env := envI) (k := FKa envC Kc) (ch := ch)
        (hdef := defaultValue_u64')
      exact stepFnIter_one h0
    have g3 : stepFnIter 1 σT (.next (.seq (.call #[.var "trm"]
          ⟨"raftpb.Entry.GetTerm"⟩ #[.var "e"] :: restAfterGetters)
        (envG2 σ.nextAddr) (FKa envC Kc))) ch
        = .ok (.exec (.call #[.var "trm"] ⟨"raftpb.Entry.GetTerm"⟩
            #[.var "e"]) (envG2 σ.nextAddr)
            (.seq restAfterGetters (envG2 σ.nextAddr) (FKa envC Kc)),
          σT, ch) :=
      stepFnIter_one stepFn_seq_pop
    have g4 : stepFnIter 1 σT (.exec (.call #[.var "trm"]
        ⟨"raftpb.Entry.GetTerm"⟩ #[.var "e"]) (envG2 σ.nextAddr)
        (.seq restAfterGetters (envG2 σ.nextAddr) (FKa envC Kc))) ch
        = .ok (.evalE (.var "e") (envG2 σ.nextAddr)
            (.callArgsK ⟨"raftpb.Entry.GetTerm"⟩
              [(.chain [], [.ref "trm"])] [] [] (envG2 σ.nextAddr)
              (.seq restAfterGetters (envG2 σ.nextAddr)
                (FKa envC Kc))), σT, ch) := by
      with_unfolding_all rfl
    have heT : Heap.lookup σT.heap (.base ⟨σ.nextAddr + 2⟩)
        = some (eParA ew) := by
      show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
        σI.heap (.base ⟨σI.nextAddr⟩) (xCell ew))
        (.base ⟨σI.nextAddr + 1⟩)
          ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
        (.base ⟨σ.nextAddr + 3⟩)
          ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩)
        (.base ⟨σ.nextAddr + 6⟩)
          ⟨some (.int .uint64), .int 0 .uint64⟩)
        (.base ⟨σ.nextAddr + 2⟩) = _
      rw [lookup_set_other (by omega : σ.nextAddr + 6 ≠ σ.nextAddr + 2),
        lookup_set_other (by omega : σ.nextAddr + 3 ≠ σ.nextAddr + 2),
        lookup_set_other (show σI.nextAddr + 1 ≠ σ.nextAddr + 2 by
          show σ.nextAddr + 4 + 1 ≠ σ.nextAddr + 2; omega),
        lookup_set_other (show σI.nextAddr ≠ σ.nextAddr + 2 by
          show σ.nextAddr + 4 ≠ σ.nextAddr + 2; omega)]
      show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) _) (.base ⟨σ.nextAddr + 1⟩) _)
        (.base ⟨σ.nextAddr + 2⟩) _) (.base ⟨σ.nextAddr + 3⟩) _)
        (.base ⟨σ.nextAddr + 2⟩) = _
      rw [lookup_set_other (by omega : σ.nextAddr + 3 ≠ σ.nextAddr + 2)]
      exact lookup_set_self
    have g5 : stepFnIter 1 σT (.evalE (.var "e") (envG2 σ.nextAddr)
        (.callArgsK ⟨"raftpb.Entry.GetTerm"⟩
          [(.chain [], [.ref "trm"])] [] [] (envG2 σ.nextAddr)
          (.seq restAfterGetters (envG2 σ.nextAddr)
            (FKa envC Kc)))) ch
        = .ok (.retV (.addr (.base ⟨ew⟩))
            (.callArgsK ⟨"raftpb.Entry.GetTerm"⟩
              [(.chain [], [.ref "trm"])] [] [] (envG2 σ.nextAddr)
              (.seq restAfterGetters (envG2 σ.nextAddr)
                (FKa envC Kc))), σT, ch) :=
      stepFnIter_one (stepFn_var (henv := rfl) (hlook := heT))
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain g1 g2) g3) g4) g5
  -- G7: the GetTerm call span (49)
  have hEwT : Heap.lookup σT.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      σI.heap (.base ⟨σI.nextAddr⟩) _) (.base ⟨σI.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 3⟩) _) (.base ⟨σ.nextAddr + 6⟩) _)
      (.base ⟨ew⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 6 ≠ ew),
      lookup_set_other (by omega : σ.nextAddr + 3 ≠ ew),
      lookup_set_other (show σI.nextAddr + 1 ≠ ew by
        show σ.nextAddr + 4 + 1 ≠ ew; omega),
      lookup_set_other (show σI.nextAddr ≠ ew by
        show σ.nextAddr + 4 ≠ ew; omega)]
    exact hEwI
  have hTcT : Heap.lookup σT.heap (.base ⟨lt2⟩)
      = some ⟨dtyT2, .int (tmN : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      σI.heap (.base ⟨σI.nextAddr⟩) _) (.base ⟨σI.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 3⟩) _) (.base ⟨σ.nextAddr + 6⟩) _)
      (.base ⟨lt2⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 6 ≠ lt2),
      lookup_set_other (by omega : σ.nextAddr + 3 ≠ lt2),
      lookup_set_other (show σI.nextAddr + 1 ≠ lt2 by
        show σ.nextAddr + 4 + 1 ≠ lt2; omega),
      lookup_set_other (show σI.nextAddr ≠ lt2 by
        show σ.nextAddr + 4 ≠ lt2; omega)]
    exact hTcI
  have htcT : Heap.lookup σT.heap (.base ⟨σ.nextAddr + 6⟩)
      = some ⟨some (.int .uint64), .int 0 .uint64⟩ := lookup_set_self
  have hfrT : ∀ x, σT.nextAddr ≤ x →
      Heap.lookup σT.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx7 : σ.nextAddr + 7 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      σI.heap (.base ⟨σI.nextAddr⟩) _) (.base ⟨σI.nextAddr + 1⟩) _)
      (.base ⟨σ.nextAddr + 3⟩) _) (.base ⟨σ.nextAddr + 6⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ.nextAddr + 6 ≠ x),
      lookup_set_other (by omega : σ.nextAddr + 3 ≠ x),
      lookup_set_other (show σI.nextAddr + 1 ≠ x by
        show σ.nextAddr + 4 + 1 ≠ x; omega),
      lookup_set_other (show σI.nextAddr ≠ x by
        show σ.nextAddr + 4 ≠ x; omega)]
    exact hfrI x (by
      show σ.nextAddr + 4 ≤ x
      omega)
  have hG7 := getTerm_call_span (envC := envG2 σ.nextAddr)
    (tgt := "trm") (ltc := σ.nextAddr + 6)
    (Kc := .seq restAfterGetters (envG2 σ.nextAddr) (FKa envC Kc))
    rfl htm σT ch (⟨rfl, rfl, rfl, rfl⟩ : bfTB.Agrees σT) hEwT hfT
    hTcT htcT hfrT (by omega) (by omega)
  -- the state after GetTerm
  let σT' : ExecState := twinSt (Heap.set (Heap.set (Heap.set σT.heap
    (.base ⟨σT.nextAddr⟩) (xCell ew)) (.base ⟨σT.nextAddr + 1⟩)
    ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩)
    (.base ⟨σ.nextAddr + 6⟩)
    ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩)
    (σT.nextAddr + 2)
  -- G8: drain to the S3-index guard (2)
  have hG8 : stepFnIter 2 σT'
      (.exec (.seqn #[]) (envG2 σ.nextAddr)
        (.seq restAfterGetters (envG2 σ.nextAddr) (FKa envC Kc))) ch
      = .ok (.exec s3IdxIfS (envG2 σ.nextAddr)
          (.seq (restAfterGetters.tail) (envG2 σ.nextAddr)
            (FKa envC Kc)), σT', ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- assemble (1 + 2 + 6 + 49 + 2 + 6 + 49 + 2 = 117)
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hG1 hG2) hG3) hG4) hG5) hG6) hG7) hG8
  exact hall

end Getters

end GoLean.RaftSeam.SpanS23
