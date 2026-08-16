import GoLeanProofs.Examples.FibMemoProgram
import GoLeanProofs.Examples.FibMemo.Pure
import GoLeanProofs.SliceMem
import GoLeanProofs.MapMem
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure

/-!
# FibMemo — Rec: the continuation-stack-parametric recursion induction

THE NEW SHAPE (Gallery Campaign G1, hard lane). Every earlier gallery
example is loop-shaped: its machine run stays inside ONE frame, so its
state families can carry a concrete heap front and its segments close
by `with_unfolding_all rfl`. `fibMemo` RECURSES: the machine pushes a
`.frame` continuation per call, the heap interleaves live frame cells
with the dead cells of completed sub-calls, and no concrete heap shape
exists — the shape is the DATA.

The route (recorded here because it is the unit's contribution):

* **Footprint-style segments.** Every frame-body segment is stated
  over `fmSt h na` — the machine state at a FULLY ABSTRACT heap `h` —
  with the segment's heap reads/writes carried as `Heap.lookup`
  hypotheses and `Heap.set` result terms. Statement-spine steps reduce
  definitionally even over abstract `h` (they never consult the
  heap); only the genuinely heap-touching steps are conditioned.
* **Continuation-parametric statements.** The call-span lemmas
  (`fmCall_base`, `fmCall_hit`, `fmCall_build`) quantify over the
  RETURN continuation `K` and the caller environment, so a recursive
  instantiation supplies the concrete frame continuation the machine
  built one level up. This is what makes the induction go through: the
  induction is on the ARGUMENT `k`, and the growing continuation
  stack rides in `K`.
* **The sandwich invariant.** A call site's heap is
  `h = … live cells … dead cells …` with everything relevant carried
  as three facts: the map data cell's content (`Heap.lookup h bM`),
  the caller's target cell (`Heap.lookup h aT`), and whole-heap
  freshness above `na` (`FreshFrom h na`). The conclusion returns the
  heap as `(h.set bM …).set aT … ++ junk` with the same three facts
  re-established — a by-hand small-footprint spec.

KIT-CANDIDATE note (chartered consumers: any future recursive
example): the `fmSt`/`FreshFrom` vocabulary, the enterFrame fact at a
symbolic `nextAddr`, and the frame-exit store fact are program-generic
in all but the function's name and would lift to `StepKit` as a
"recursive-call frame induction" pack. The SEGMENTS are this program's
own transcription and would not lift. Recorded in the campaign log's
kit-gap list; not lifted here (single consumer today).
-/

namespace GoLean.Examples.FibMemo

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Vocabulary -/

abbrev tU : Ty := .int .uint64
abbrev tMapUU : Ty := .map tU tU

/-- uint64 cell -/
abbrev u64c (v : Int) : HeapCell := ⟨some tU, .int v .uint64⟩
/-- bool cell -/
abbrev bc (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
/-- map-HANDLE cell pointing at the map data cell `bM` -/
abbrev mapHc (bM : Nat) : HeapCell := ⟨some tMapUU, .map ⟨some (.base ⟨bM⟩)⟩⟩
/-- the (untyped) map DATA cell holding table `M` -/
abbrev mapDc (M : List (Int × Nat)) : HeapCell := ⟨none, .mapData (toEntries M)⟩
/-- the map handle VALUE -/
abbrev mapHv (bM : Nat) : GoValue := .map ⟨some (.base ⟨bM⟩)⟩

/-- The machine state of the `fibmemo` program at heap `h`, next
address `na` — the footprint style's single state former. -/
def fmSt (h : Heap) (na : Nat) : ExecState :=
  { types := fibmemoLowered.typeDefs.toList,
    functions := fibmemoLowered.funcs,
    methods := fibmemoLowered.methods,
    heap := h, nextAddr := na }

/-- Whole-heap freshness at and above `na` (the `DeadFrom` shape, on
the full heap rather than a dead tail). -/
def FreshFrom (h : Heap) (na : Nat) : Prop :=
  ∀ x : Nat, na ≤ x → Heap.lookup h (.base ⟨x⟩) = none

theorem FreshFrom.mono {h : Heap} {na na' : Nat} (hle : na ≤ na')
    (hf : FreshFrom h na) : FreshFrom h na' :=
  fun x hx => hf x (by omega)

/-- Appending a cell AT the boundary preserves freshness one up. -/
theorem FreshFrom.push {h : Heap} {na : Nat} {c : HeapCell}
    (hf : FreshFrom h na) :
    FreshFrom (h ++ [(.base ⟨na⟩, c)]) (na + 1) := by
  intro x hx
  rw [lookup_append_right (hf x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
  rfl

/-- A `set` below the boundary preserves freshness. -/
theorem FreshFrom.set {h : Heap} {na a : Nat} {c : HeapCell}
    (hf : FreshFrom h na) (ha : a < na) :
    FreshFrom (Heap.set h (.base ⟨a⟩) c) na := by
  intro x hx
  rw [Machine.Heap.lookup_set_ne
    (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega
      : (Loc.base ⟨a⟩ : Loc) ≠ .base ⟨x⟩)]
  exact hf x hx

/-- Lookup through a `set` at a DIFFERENT base address. -/
theorem lookup_set_other {h : Heap} {a x : Nat} {c : HeapCell} (hne : a ≠ x) :
    Heap.lookup (Heap.set h (.base ⟨a⟩) c) (.base ⟨x⟩) = Heap.lookup h (.base ⟨x⟩) :=
  Machine.Heap.lookup_set_ne
    (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega)

/-- Lookup at the `set` address itself. -/
theorem lookup_set_self {h : Heap} {l : Loc} {c : HeapCell} :
    Heap.lookup (Heap.set h l c) l = some c := by
  induction h with
  | nil => simp [Heap.set, Heap.lookup]
  | cons p rest ih =>
      obtain ⟨loc, old⟩ := p
      simp only [Heap.set]
      cases hb : (loc == l) with
      | true => simp [Heap.lookup, eq_of_beq hb]
      | false => simp [Heap.lookup, hb, ih]

/-! ## The callee `Func`, verbatim, pinned -/

abbrev fmGuardZero : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.var "n"), .returnStmt]]
abbrev fmGuardIf : Stmt :=
  .ifThenElse (.lessCmp (.var "n") (.intLit 2 .uint64)) fmGuardZero (.seqn #[])
abbrev fmHitZero : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.var "v"), .returnStmt]]
abbrev fmLkSeq : Stmt :=
  .seqn #[.initialization { id := "v", typ := tU },
          .initialization { id := "ok", typ := .bool },
          .mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU]
abbrev fmOkIf : Stmt := .ifThenElse (.var "ok") fmHitZero (.seqn #[])
abbrev fmLkBlock : Stmt := .block #[] #[fmLkSeq, fmOkIf]
abbrev fmC0Seqn : Stmt :=
  .seqn #[.initialization { id := "$c0", typ := tU },
          .call #[.var "$c0"] ⟨"fibMemo"⟩
            #[.sub (.var "n") (.intLit 1 .uint64), .var "memo"]]
abbrev fmC1Seqn : Stmt :=
  .seqn #[.initialization { id := "$c1", typ := tU },
          .call #[.var "$c1"] ⟨"fibMemo"⟩
            #[.sub (.var "n") (.intLit 2 .uint64), .var "memo"]]
abbrev fmRSeqn : Stmt :=
  .seqn #[.initialization { id := "r", typ := tU },
          .assign (.var "r") (.add (.var "$c0") (.var "$c1"))]
abbrev fmMapAsgn : Stmt :=
  .mapAssign (.var "memo") (.var "n") (.var "r") tU tU
abbrev fmRetSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "r"), .returnStmt]

def fibMemoFunc : Func :=
  { id := { key := "fibMemo" },
    args := #[{ id := "n", typ := tU }, { id := "memo", typ := tMapUU }],
    results := #[{ id := "$res0", typ := tU }],
    body := .block #[]
      #[fmGuardIf, fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn],
    variadic := false, wrapper := false }

/-- The lowering pin: the transcription above IS the frontend's
`fibMemo`. -/
theorem fibMemoFunc_pin :
    findFunctionIn? fibmemoLowered.funcs ⟨"fibMemo"⟩ = some fibMemoFunc := rfl

/-- The frame env `enterFrame` builds (one scope: results then args,
newest first). -/
def frEnv (f : Nat) : LocalEnv :=
  [[("$res0", .base ⟨f + 2⟩), ("memo", .base ⟨f + 1⟩), ("n", .base ⟨f⟩)]]

/-- The body block's env: one pushed scope over the frame env. -/
def frEnv2 (f : Nat) : LocalEnv := [] :: frEnv f

/-! ## The enterFrame fact at a symbolic `nextAddr` -/

/-- Raw reduct over a fully symbolic heap: the three parameter/result
allocations stay as symbolic `Heap.set`s; everything else computes. -/
theorem fm_enterFrame_raw (h : Heap) (na : Nat) (kv : Int) (mv : MapValue) :
    enterFrame (fmSt h na) ⟨"fibMemo"⟩ [.int kv .uint64, .map mv]
      = .ok (fibMemoFunc, frEnv na, [.base ⟨na + 2⟩],
          fmSt (((h.set (.base ⟨na⟩)
                (u64c (IntKind.normalize .uint64 kv))).set
              (.base ⟨na + 1⟩) ⟨some tMapUU, .map mv⟩).set
              (.base ⟨na + 2⟩) (u64c 0))
            (na + 3)) := by
  with_unfolding_all rfl

/-- The composition-facing form: entering `fibMemo (k, memo)` on a
fresh-from-`na` heap appends the three frame cells. -/
theorem fm_enterFrame (h : Heap) (na : Nat) (k : Nat) (bM : Nat)
    (hk : k < 2 ^ 64) (hf : FreshFrom h na) :
    enterFrame (fmSt h na) ⟨"fibMemo"⟩ [.int (k : Int) .uint64, mapHv bM]
      = .ok (fibMemoFunc, frEnv na, [.base ⟨na + 2⟩],
          fmSt (h ++ [(.base ⟨na⟩, u64c (k : Int)), (.base ⟨na + 1⟩, mapHc bM),
                      (.base ⟨na + 2⟩, u64c 0)]) (na + 3)) := by
  have hraw := fm_enterFrame_raw h na (k : Int) ⟨some (.base ⟨bM⟩)⟩
  rw [unorm_nat_of_lt hk] at hraw
  have e0 : Heap.lookup h (.base ⟨na⟩) = none := hf na (by omega)
  rw [set_fresh e0] at hraw
  have e1 : Heap.lookup (h ++ [(.base ⟨na⟩, u64c (k : Int))]) (.base ⟨na + 1⟩) = none := by
    rw [lookup_append_right (hf (na + 1) (by omega))]
    exact lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))
  rw [set_fresh e1] at hraw
  have e2 : Heap.lookup (h ++ [(.base ⟨na⟩, u64c (k : Int))]
      ++ [(.base ⟨na + 1⟩, ⟨some tMapUU, .map ⟨some (.base ⟨bM⟩)⟩⟩)]) (.base ⟨na + 2⟩) = none := by
    rw [lookup_append_right (by
      rw [lookup_append_right (hf (na + 2) (by omega))]
      exact lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)))]
    exact lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))
  rw [set_fresh e2] at hraw
  simpa [List.append_assoc] using hraw

/-! ## Continuation vocabulary

Every call site's return continuation is a `.frame` whose target plan
stores one result into the caller's `$c`-cell through `.ref tv`, and
whose own continuation is the caller's remaining sequence — so the
call-span lemmas are parametric in exactly `(tv, envC, rest, K₀)`.
`f` is the FRAME BASE: the callee's three entry cells sit at
`f`, `f+1`, `f+2`. -/

/-- The return continuation every `fibMemo` call site builds. -/
def frameK (tv : String) (envC : LocalEnv) (f : Nat)
    (rest : List Stmt) (K₀ : Cont) : Cont :=
  .frame [(.chain [], [.ref tv])] envC [.base ⟨f + 2⟩] []
    (.seq rest envC K₀) false

/-- The guard delivery point. -/
def kGuardIf (f : Nat) (KT : Cont) : Cont :=
  .ifK fmGuardZero (.seqn #[]) (frEnv2 f)
    (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
      (frEnv2 f) KT)

/-! ## Segments (footprint style: abstract heap, conditioned steps) -/

/-- S1 — body entry → the `n < 2` guard's delivery. 8 steps; reads the
`n` cell at `f`. -/
theorem fm_seg1 (h : Heap) (na f : Nat) (kv : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hn : Heap.lookup h (.base ⟨f⟩) = some (u64c kv)) :
    stepFnIter 8 (fmSt h na)
        (.exec fibMemoFunc.body (frEnv f) (frameK tv envC f rest K₀)) ch
      = .ok (.retV (.bool (decide (kv < 2)))
            (kGuardIf f (frameK tv envC f rest K₀)),
          fmSt h na, ch) := by
  show stepFnIter (4 + 1 + 2 + 1) _ _ _ = _
  have hA : stepFnIter 4 (fmSt h na)
      (.exec fibMemoFunc.body (frEnv f) (frameK tv envC f rest K₀)) ch
      = .ok (.evalE (.var "n") (frEnv2 f)
          (.strictK (.lessCmp) [] [.intLit 2 .uint64] (frEnv2 f)
            (kGuardIf f (frameK tv envC f rest K₀))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have hv := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "n") (env := frEnv2 f) (a := ⟨f⟩)
    (k := .strictK (.lessCmp) [] [.intLit 2 .uint64] (frEnv2 f)
      (kGuardIf f (frameK tv envC f rest K₀)))
    (ch := ch) (c := u64c kv) rfl hn)
  have hB : stepFnIter 2 (fmSt h na)
      (.retV (.int kv .uint64)
        (.strictK (.lessCmp) [] [.intLit 2 .uint64] (frEnv2 f)
          (kGuardIf f (frameK tv envC f rest K₀)))) ch
      = .ok (.retV (.int 2 .uint64)
          (.strictK (.lessCmp) [.int kv .uint64] [] (frEnv2 f)
            (kGuardIf f (frameK tv envC f rest K₀))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have happ := stepFnIter_one (stepFn_strict_apply
    (σ := fmSt h na) (σ' := fmSt h na) (op := .lessCmp)
    (done := [.int kv .uint64]) (v := .int 2 .uint64)
    (out := .bool (decide (kv < 2)))
    (env := frEnv2 f) (k := kGuardIf f (frameK tv envC f rest K₀))
    (ch := ch) (applyStrictOp_lessCmp_int))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hv) hB) happ

/-- S2a — guard TRUE → `$res0 := n`, return, drain to the frame. 17
steps; reads `n` at `f`, writes `$res0` at `f+2`. -/
theorem fm_seg2a (h : Heap) (na f : Nat) (kv : Int) (old0 : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hn : Heap.lookup h (.base ⟨f⟩) = some (u64c kv))
    (hres : Heap.lookup h (.base ⟨f + 2⟩) = some (u64c old0))
    (hkv : IntKind.normalize .uint64 kv = kv) :
    stepFnIter 17 (fmSt h na)
        (.retV (.bool true) (kGuardIf f (frameK tv envC f rest K₀))) ch
      = .ok (.returning (frameK tv envC f rest K₀),
          fmSt (h.set (.base ⟨f + 2⟩) (u64c kv)) na, ch) := by
  show stepFnIter (3 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 4) _ _ _ = _
  have hA1 : stepFnIter 3 (fmSt h na)
      (.retV (.bool true) (kGuardIf f (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.seqn #[.assign (.var "$res0") (.var "n"), .returnStmt])
            ([] :: frEnv2 f)
            (.seq [] ([] :: frEnv2 f)
              (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
                     fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀))),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hA2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[.assign (.var "$res0") (.var "n"), .returnStmt])
    (env := ([] :: frEnv2 f)) (rest := [])
    (k := .seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
                fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀))
    (ch := ch))
  have hA3 : stepFnIter 4 (fmSt h na)
      (.next (.seq ((#[.assign (.var "$res0") (.var "n"),
              .returnStmt] : Array Stmt).toList ++ [])
        ([] :: frEnv2 f)
        (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
               fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀)))) ch
      = .ok (.evalE (.var "n") ([] :: frEnv2 f)
          (.rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
            (.seqn #[]) ([] :: frEnv2 f)
            (.seq [.returnStmt] ([] :: frEnv2 f)
              (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
                     fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀)))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have hv := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "n") (env := ([] :: frEnv2 f)) (a := ⟨f⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
      (.seqn #[]) ([] :: frEnv2 f)
      (.seq [.returnStmt] ([] :: frEnv2 f)
        (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
               fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀))))
    (ch := ch) (c := u64c kv) rfl hn)
  have hB : stepFnIter 1 (fmSt h na)
      (.retV (.int kv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
          (.seqn #[]) ([] :: frEnv2 f)
          (.seq [.returnStmt] ([] :: frEnv2 f)
            (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
                   fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨f + 2⟩)) [] []]
            [.int kv .uint64] (.seqn #[]) ([] :: frEnv2 f)
            (.seq [.returnStmt] ([] :: frEnv2 f)
              (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
                     fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀)))),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hst : storeTarget (fmSt h na) (.chain (.addr (.base ⟨f + 2⟩)) [] [])
      (.int kv .uint64)
      = .ok { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c kv) } :=
    storeTarget_addr hres (by
      show normalizeValueForTy (fmSt h na) tU (.int kv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hkv])
  have hC := stepFnIter_one (stepFn_store_step
    (σ := fmSt h na)
    (σ' := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c kv) })
    (r := .chain (.addr (.base ⟨f + 2⟩)) [] []) (val := .int kv .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := ([] :: frEnv2 f))
    (k := .seq [.returnStmt] ([] :: frEnv2 f)
      (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
             fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀)))
    (ch := ch) hst)
  have hD1 := stepFnIter_one (stepFn_storeK_nil
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c kv) })
    (body := .seqn #[]) (env := ([] :: frEnv2 f))
    (k := .seq [.returnStmt] ([] :: frEnv2 f)
      (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
             fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀)))
    (ch := ch))
  have hD2 := stepFnIter_one (stepFn_seqn_splice
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c kv) })
    (ss := #[]) (env := ([] :: frEnv2 f))
    (rest := [.returnStmt])
    (k := .seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
                fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀))
    (ch := ch))
  have hD3 : stepFnIter 4
      { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c kv) }
      (.next (.seq ((#[] : Array Stmt).toList ++ [.returnStmt]) ([] :: frEnv2 f)
        (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn,
               fmRetSeqn] (frEnv2 f) (frameK tv envC f rest K₀)))) ch
      = .ok (.returning (frameK tv envC f rest K₀),
          { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c kv) }, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hA1 hA2) hA3) hv) hB) hC)
      hD1) hD2) hD3

/-- The `.ref` evaluation step (env-only; the mirror of `stepFn_var`).

GAP-WITNESS (see docs/gallery-campaign-log/g1.md § unit G1.7 fibmemo,
promotion ledger): the kit has `stepFn_var` but no `.ref` mirror. -/
theorem fm_ref_step {σ : ExecState} {x : String} {env : LocalEnv}
    {l : Loc} {k : Cont} {ch : Choices}
    (henv : LocalEnv.lookup env x = some l) :
    stepFn σ (.evalE (.ref x) env k) ch = .ok (.retV (.addr l) k, σ, ch) := by
  simp only [stepFn, henv, pure, Except.pure]

/-- The frame-exit head step: `.returning` at the frame reads the
pinned result and opens the caller-target spine. -/
theorem fm_frame_exit_step {σ : ExecState} {tv : String} {envC : LocalEnv}
    {f : Nat} {rest : List Stmt} {K₀ : Cont} {rv : Int} {ch : Choices}
    (hres : Heap.lookup σ.heap (.base ⟨f + 2⟩) = some (u64c rv)) :
    stepFn σ (.returning (frameK tv envC f rest K₀)) ch
      = .ok (.evalE (.ref tv) envC
          (.tgtOpK (.chain []) [] [] [] [] .vals [] [.int rv .uint64]
            (.seqn #[]) envC (.seq rest envC K₀)), σ, ch) := by
  simp only [stepFn, frameK, loadMany, loadLoc, hres, Bind.bind,
    Except.bind, pure, Except.pure]

/-- S2b — the frame exit: read the result, store it into the caller's
target cell, resume the caller. 6 steps. -/
theorem fm_seg2b (h : Heap) (na f aT : Nat) (rv oldT : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hres : Heap.lookup h (.base ⟨f + 2⟩) = some (u64c rv))
    (haT : Heap.lookup h (.base ⟨aT⟩) = some (u64c oldT))
    (henvC : LocalEnv.lookup envC tv = some (.base ⟨aT⟩))
    (hrv : IntKind.normalize .uint64 rv = rv) :
    stepFnIter 6 (fmSt h na) (.returning (frameK tv envC f rest K₀)) ch
      = .ok (.next (.seq rest envC K₀),
          fmSt (h.set (.base ⟨aT⟩) (u64c rv)) na, ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have h1 := stepFnIter_one (fm_frame_exit_step (σ := fmSt h na)
    (tv := tv) (envC := envC) (f := f) (rest := rest) (K₀ := K₀)
    (rv := rv) (ch := ch) hres)
  have h2 := stepFnIter_one (fm_ref_step (σ := fmSt h na) (x := tv)
    (env := envC) (l := .base ⟨aT⟩)
    (k := .tgtOpK (.chain []) [] [] [] [] .vals [] [.int rv .uint64]
      (.seqn #[]) envC (.seq rest envC K₀)) (ch := ch) henvC)
  have h3 : stepFnIter 1 (fmSt h na)
      (.retV (.addr (.base ⟨aT⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [] [.int rv .uint64]
          (.seqn #[]) envC (.seq rest envC K₀))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨aT⟩)) [] []]
            [.int rv .uint64] (.seqn #[]) envC (.seq rest envC K₀)),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hst : storeTarget (fmSt h na) (.chain (.addr (.base ⟨aT⟩)) [] [])
      (.int rv .uint64)
      = .ok { fmSt h na with heap := Heap.set h (.base ⟨aT⟩) (u64c rv) } :=
    storeTarget_addr haT (by
      show normalizeValueForTy (fmSt h na) tU (.int rv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hrv])
  have h4 := stepFnIter_one (stepFn_store_step
    (σ := fmSt h na)
    (σ' := { fmSt h na with heap := Heap.set h (.base ⟨aT⟩) (u64c rv) })
    (r := .chain (.addr (.base ⟨aT⟩)) [] []) (val := .int rv .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := envC)
    (k := .seq rest envC K₀) (ch := ch) hst)
  have h5 := stepFnIter_one (stepFn_storeK_nil
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨aT⟩) (u64c rv) })
    (body := .seqn #[]) (env := envC) (k := .seq rest envC K₀) (ch := ch))
  have h6 := stepFnIter_one (stepFn_seqn_splice
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨aT⟩) (u64c rv) })
    (ss := #[]) (env := envC) (rest := rest) (k := K₀) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6

/-- `Heap.set` skips a mismatching head cell. -/
theorem set_cons_ne {l needle : Loc} {c₀ c : HeapCell} {rest : Heap}
    (hne : (l == needle) = false) :
    Heap.set ((l, c₀) :: rest) needle c = (l, c₀) :: Heap.set rest needle c := by
  simp [Heap.set, hne]

/-- The three frame cells of a call at base `f` with argument `kv`,
result cell at `rv`. -/
def frameCells (f : Nat) (bM : Nat) (kv rv : Int) : Heap :=
  [(.base ⟨f⟩, u64c kv), (.base ⟨f + 1⟩, mapHc bM), (.base ⟨f + 2⟩, u64c rv)]

/-- **The BASE call span** (`k ≤ 1`): 32 steps from the call's last
argument delivery to the caller's resumption; the caller's target cell
receives `k` (which IS `fibW k`), the memo is untouched, and the
frame's three cells go dead. -/
theorem fmCall_base (h : Heap) (na bM aT : Nat) (k : Nat) (oldT : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hk1 : k ≤ 1)
    (haT : Heap.lookup h (.base ⟨aT⟩) = some (u64c oldT))
    (hfr : FreshFrom h na) (_haTlt : aT < na)
    (henvC : LocalEnv.lookup envC tv = some (.base ⟨aT⟩)) :
    stepFnIter 32 (fmSt h na)
        (.retV (mapHv bM)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref tv])]
            [.int (k : Int) .uint64] [] envC (.seq rest envC K₀))) ch
      = .ok (.next (.seq rest envC K₀),
          fmSt ((h.set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
              ++ frameCells na bM (k : Int) (k : Int)) (na + 3), ch) := by
  have hk64 : k < 2 ^ 64 := by omega
  show stepFnIter (1 + 8 + 17 + 6) _ _ _ = _
  -- 1: the frame entry
  have hEnter := stepFnIter_one (stepFn_call_enter
    (σ := fmSt h na) (fid := ⟨"fibMemo"⟩) (v := mapHv bM)
    (vals := [.int (k : Int) .uint64])
    (plans := [(.chain [], [.ref tv])]) (env := envC)
    (k := .seq rest envC K₀) (ch := ch)
    (fm_enterFrame h na k bM hk64 hfr))
  -- the heap with the three entry cells appended
  have hlk_n : Heap.lookup (h ++ frameCells na bM (k : Int) 0) (.base ⟨na⟩)
      = some (u64c (k : Int)) := by
    rw [lookup_append_right (hfr na (by omega))]
    simp [frameCells, Heap.lookup]
  have hlk_res : Heap.lookup (h ++ frameCells na bM (k : Int) 0) (.base ⟨na + 2⟩)
      = some (u64c 0) := by
    rw [lookup_append_right (hfr (na + 2) (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
    simp [Heap.lookup]
  -- 2: the guard, TRUE
  have hS1 := fm_seg1 (h ++ frameCells na bM (k : Int) 0) (na + 3) na (k : Int)
    tv envC rest K₀ ch hlk_n
  rw [show (decide ((k : Int) < 2)) = true from by
    simp only [decide_eq_true_eq]
    exact_mod_cast (by omega : k < 2)] at hS1
  -- 3: the base branch
  have hS2a := fm_seg2a (h ++ frameCells na bM (k : Int) 0) (na + 3) na (k : Int) 0
    tv envC rest K₀ ch hlk_n hlk_res (unorm_nat_of_lt hk64)
  -- clean the S2a result heap: the set stays in the frame cells
  have hset1 : (h ++ frameCells na bM (k : Int) 0).set (.base ⟨na + 2⟩)
        (u64c (k : Int))
      = h ++ frameCells na bM (k : Int) (k : Int) := by
    rw [set_append_right (hfr (na + 2) (by omega)), frameCells, frameCells,
      set_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      set_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2)),
      set_singleton_self]
  rw [hset1] at hS2a
  -- 4: the frame exit
  have hlk_res' : Heap.lookup (h ++ frameCells na bM (k : Int) (k : Int))
      (.base ⟨na + 2⟩) = some (u64c (k : Int)) := by
    rw [lookup_append_right (hfr (na + 2) (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
    simp [Heap.lookup]
  have hlk_aT : Heap.lookup (h ++ frameCells na bM (k : Int) (k : Int))
      (.base ⟨aT⟩) = some (u64c oldT) := lookup_append_left haT
  have hS2b := fm_seg2b (h ++ frameCells na bM (k : Int) (k : Int)) (na + 3)
    na aT (k : Int) oldT tv envC rest K₀ ch hlk_res' hlk_aT henvC
    (unorm_nat_of_lt hk64)
  have hset2 : (h ++ frameCells na bM (k : Int) (k : Int)).set (.base ⟨aT⟩)
        (u64c (k : Int))
      = (h.set (.base ⟨aT⟩) (u64c (k : Int))) ++ frameCells na bM (k : Int) (k : Int) :=
    set_append_left haT
  rw [hset2] at hS2b
  have hfw : ((fibW k : Nat) : Int) = (k : Int) := by
    rw [fibW_small hk1]
  rw [hfw]
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hEnter hS1) hS2a) hS2b

/-! ## The lookup block -/

/-- The main-path continuation after the lookup block. -/
def kMain (f : Nat) (KT : Cont) : Cont :=
  .seq [fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (frEnv2 f) KT

/-- The lookup block's env: `v`/`ok` declared over a pushed scope. -/
def frEnvL (f : Nat) : LocalEnv :=
  [("ok", .base ⟨f + 4⟩), ("v", .base ⟨f + 3⟩)] :: frEnv2 f

/-- The `ok`-if continuation. -/
def kOkIf (f : Nat) (KT : Cont) : Cont :=
  .seq [fmOkIf] (frEnvL f) (kMain f KT)

/-- S3a — guard FALSE → `v`/`ok` allocated, the `mapLookup` statement
head. 11 steps; allocates `f+3` (uint64 zero) and `f+4` (bool false). -/
theorem fm_seg3a (h : Heap) (f : Nat)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hfr : FreshFrom h (f + 3)) :
    stepFnIter 11 (fmSt h (f + 3))
        (.retV (.bool false) (kGuardIf f (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n")
              tU tU) (frEnvL f)
            (kOkIf f (frameK tv envC f rest K₀)),
          fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0), (.base ⟨f + 4⟩, bc false)])
            (f + 5), ch) := by
  show stepFnIter (1 + 1 + 3 + 1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have h1 : stepFnIter 1 (fmSt h (f + 3))
      (.retV (.bool false) (kGuardIf f (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.seqn #[]) (frEnv2 f)
          (.seq [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
            (frEnv2 f) (frameK tv envC f rest K₀)),
        fmSt h (f + 3), ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h (f + 3))
    (ss := #[]) (env := frEnv2 f)
    (rest := [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn])
    (k := frameK tv envC f rest K₀) (ch := ch))
  have h3 : stepFnIter 3 (fmSt h (f + 3))
      (.next (.seq ((#[] : Array Stmt).toList
          ++ [fmLkBlock, fmC0Seqn, fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn])
        (frEnv2 f) (frameK tv envC f rest K₀))) ch
      = .ok (.exec fmLkSeq ([] :: frEnv2 f)
          (.seq [fmOkIf] ([] :: frEnv2 f) (kMain f (frameK tv envC f rest K₀))),
        fmSt h (f + 3), ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h (f + 3))
    (ss := #[.initialization { id := "v", typ := tU },
             .initialization { id := "ok", typ := .bool },
             .mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU])
    (env := [] :: frEnv2 f) (rest := [fmOkIf])
    (k := kMain f (frameK tv envC f rest K₀)) (ch := ch))
  have h5 : stepFnIter 1 (fmSt h (f + 3))
      (.next (.seq ((#[.initialization { id := "v", typ := tU },
             .initialization { id := "ok", typ := .bool },
             .mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU]
            : Array Stmt).toList ++ [fmOkIf])
        ([] :: frEnv2 f) (kMain f (frameK tv envC f rest K₀)))) ch
      = .ok (.exec (.initialization { id := "v", typ := tU }) ([] :: frEnv2 f)
          (.seq [.initialization { id := "ok", typ := .bool },
                 .mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU,
                 fmOkIf]
            ([] :: frEnv2 f) (kMain f (frameK tv envC f rest K₀))),
        fmSt h (f + 3), ch) := by
    with_unfolding_all rfl
  have h6 := stepFnIter_one (stepFn_init_seq (σ := fmSt h (f + 3))
    (p := { id := "v", typ := tU })
    (rest := [.initialization { id := "ok", typ := .bool },
              .mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU,
              fmOkIf])
    (env := [] :: frEnv2 f) (k := kMain f (frameK tv envC f rest K₀))
    (ch := ch) (v := .int 0 .uint64) (by with_unfolding_all rfl))
  rw [show (fmSt h (f + 3)).nextAddr = f + 3 from rfl,
    show Heap.set (fmSt h (f + 3)).heap (.base ⟨f + 3⟩) ⟨some tU, .int 0 .uint64⟩
      = h ++ [(.base ⟨f + 3⟩, u64c 0)] from set_fresh (hfr (f + 3) (by omega))] at h6
  have h7 : stepFnIter 1
      (fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0)]) (f + 3 + 1))
      (.next (.seq [.initialization { id := "ok", typ := .bool },
                 .mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU,
                 fmOkIf]
        (LocalEnv.declare ([] :: frEnv2 f) "v" (.base ⟨f + 3⟩))
        (kMain f (frameK tv envC f rest K₀)))) ch
      = .ok (.exec (.initialization { id := "ok", typ := .bool })
          (LocalEnv.declare ([] :: frEnv2 f) "v" (.base ⟨f + 3⟩))
          (.seq [.mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU,
                 fmOkIf]
            (LocalEnv.declare ([] :: frEnv2 f) "v" (.base ⟨f + 3⟩))
            (kMain f (frameK tv envC f rest K₀))),
        fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0)]) (f + 3 + 1), ch) := by
    with_unfolding_all rfl
  have h8 := stepFnIter_one (stepFn_init_seq
    (σ := fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0)]) (f + 3 + 1))
    (p := { id := "ok", typ := .bool })
    (rest := [.mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n") tU tU,
              fmOkIf])
    (env := LocalEnv.declare ([] :: frEnv2 f) "v" (.base ⟨f + 3⟩))
    (k := kMain f (frameK tv envC f rest K₀))
    (ch := ch) (v := .bool false) (by with_unfolding_all rfl))
  rw [show (fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0)]) (f + 3 + 1)).nextAddr = f + 4 from rfl,
    show Heap.set (fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0)]) (f + 3 + 1)).heap
        (.base ⟨f + 4⟩) ⟨some .bool, .bool false⟩
      = h ++ [(.base ⟨f + 3⟩, u64c 0), (.base ⟨f + 4⟩, bc false)] from by
    rw [show (fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0)]) (f + 3 + 1)).heap
        = h ++ [(.base ⟨f + 3⟩, u64c 0)] from rfl,
      set_fresh (by
        rw [lookup_append_right (hfr (f + 4) (by omega))]
        exact lookup_cons_ne (base_beq_false (by omega : f + 3 ≠ f + 4)))]
    simp] at h8
  have h9 : stepFnIter 1
      (fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0), (.base ⟨f + 4⟩, bc false)])
        (f + 3 + 1 + 1))
      (.next (.seq [.mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n")
                tU tU, fmOkIf]
        (LocalEnv.declare (LocalEnv.declare ([] :: frEnv2 f) "v" (.base ⟨f + 3⟩))
          "ok" (.base ⟨f + 4⟩))
        (kMain f (frameK tv envC f rest K₀)))) ch
      = .ok (.exec (.mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n")
              tU tU) (frEnvL f)
            (kOkIf f (frameK tv envC f rest K₀)),
          fmSt (h ++ [(.base ⟨f + 3⟩, u64c 0), (.base ⟨f + 4⟩, bc false)])
            (f + 3 + 1 + 1), ch) := by
    with_unfolding_all rfl
  have := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7) h8) h9
  simpa using this

/-- The mapLookup rhs spine at the lookup block's placement. -/
def rhsLk (f : Nat) (KT : Cont) (done : List GoValue) (pend : List Expr) : Cont :=
  .rhsK (.mapLookup tU tU)
    [.chain (.addr (.base ⟨f + 3⟩)) [] [], .chain (.addr (.base ⟨f + 4⟩)) [] []]
    done pend (.seqn #[]) (frEnvL f) (kOkIf f KT)

/-- S3b — the `mapLookup` statement head → the key delivered at the
comma-ok drain. 8 steps; reads `memo` at `f+1` and `n` at `f`. -/
theorem fm_seg3b (h : Heap) (na f bM : Nat) (kv : Int) (KT : Cont)
    (ch : Choices)
    (hmem : Heap.lookup h (.base ⟨f + 1⟩) = some (mapHc bM))
    (hn : Heap.lookup h (.base ⟨f⟩) = some (u64c kv)) :
    stepFnIter 8 (fmSt h na)
        (.exec (.mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n")
            tU tU) (frEnvL f) (kOkIf f KT)) ch
      = .ok (.retV (.int kv .uint64) (rhsLk f KT [mapHv bM] []),
          fmSt h na, ch) := by
  show stepFnIter (5 + 1 + 1 + 1) _ _ _ = _
  have hA : stepFnIter 5 (fmSt h na)
      (.exec (.mapLookup (.var "v") (.var "ok") (.var "memo") (.var "n")
          tU tU) (frEnvL f) (kOkIf f KT)) ch
      = .ok (.evalE (.var "memo") (frEnvL f) (rhsLk f KT [] [.var "n"]),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hv1 := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "memo") (env := frEnvL f) (a := ⟨f + 1⟩)
    (k := rhsLk f KT [] [.var "n"]) (ch := ch) (c := mapHc bM) rfl hmem)
  have hB : stepFnIter 1 (fmSt h na)
      (.retV (mapHv bM) (rhsLk f KT [] [.var "n"])) ch
      = .ok (.evalE (.var "n") (frEnvL f) (rhsLk f KT [mapHv bM] []),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hv2 := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "n") (env := frEnvL f) (a := ⟨f⟩)
    (k := rhsLk f KT [mapHv bM] []) (ch := ch) (c := u64c kv) rfl hn)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hv1) hB) hv2

/-- The comma-ok drain, MISS: the key is absent, `v` gets the zero
value and `ok` gets `false` (gap-witness: the kit has no
`mapLookupValue` fact — recorded as a kit candidate). -/
theorem fm_lookup_drain_miss {σ : ExecState} {f bM : Nat} {kv : Int}
    {M : List (Int × Nat)} {KT : Cont} {ch : Choices}
    (hmap : Heap.lookup σ.heap (.base ⟨bM⟩) = some (mapDc M))
    (hkv : IntKind.normalize .uint64 kv = kv)
    (hmiss : idxOf? M kv = none) :
    stepFn σ (.retV (.int kv .uint64) (rhsLk f KT [mapHv bM] [])) ch
      = .ok (.next (.storeK
            [.chain (.addr (.base ⟨f + 3⟩)) [] [],
             .chain (.addr (.base ⟨f + 4⟩)) [] []]
            [.int 0 .uint64, .bool false]
            (.seqn #[]) (frEnvL f) (kOkIf f KT)), σ, ch) := by
  simp only [stepFn, rhsLk, applyRhsOp, valueAsMap, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, Bind.bind,
    Except.bind, pure, Except.pure]
  rw [show normalizeValueForTy σ tU (.int kv .uint64) = .ok (.int kv .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hkv]]
  simp only [mapLookupValue, mapEntries, loadLoc, hmap, Bind.bind, Except.bind,
    pure, Except.pure]
  rw [mapEntryIndex?_toEntries σ M kv false]
  simp only [hmiss]
  with_unfolding_all rfl

/-- The comma-ok drain, HIT at entry `i` holding wrapped value `w`.

GAP-WITNESS (see docs/gallery-campaign-log/g1.md § unit G1.7 fibmemo,
promotion ledger): `MapMem` carries `applyStrictOp_mapGet` for the
EXPRESSION form only — the comma-ok drain has no kit form. -/
theorem fm_lookup_drain_hit {σ : ExecState} {f bM : Nat} {kv : Int}
    {M : List (Int × Nat)} {i w : Nat} {KT : Cont} {ch : Choices}
    (hmap : Heap.lookup σ.heap (.base ⟨bM⟩) = some (mapDc M))
    (hkv : IntKind.normalize .uint64 kv = kv)
    (hidx : idxOf? M kv = some i)
    (hget : (toEntries M)[i]? = some (.int kv .uint64, .int (w : Int) .uint64)) :
    stepFn σ (.retV (.int kv .uint64) (rhsLk f KT [mapHv bM] [])) ch
      = .ok (.next (.storeK
            [.chain (.addr (.base ⟨f + 3⟩)) [] [],
             .chain (.addr (.base ⟨f + 4⟩)) [] []]
            [.int (w : Int) .uint64, .bool true]
            (.seqn #[]) (frEnvL f) (kOkIf f KT)), σ, ch) := by
  simp only [stepFn, rhsLk, applyRhsOp, valueAsMap, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, Bind.bind,
    Except.bind, pure, Except.pure]
  rw [show normalizeValueForTy σ tU (.int kv .uint64) = .ok (.int kv .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hkv]]
  simp only [mapLookupValue, mapEntries, loadLoc, hmap, Bind.bind, Except.bind,
    pure, Except.pure]
  rw [mapEntryIndex?_toEntries σ M kv false]
  simp only [hidx, hget]

/-- S3c — the two comma-ok stores land in the `v`/`ok` cells. 2
steps. -/
theorem fm_seg3c (h : Heap) (na f : Nat) (dv : Int) (okb : Bool)
    (KT : Cont) (ch : Choices)
    (hv : Heap.lookup h (.base ⟨f + 3⟩) = some (u64c 0))
    (hok : Heap.lookup (h.set (.base ⟨f + 3⟩) (u64c dv)) (.base ⟨f + 4⟩)
      = some (bc false))
    (hdv : IntKind.normalize .uint64 dv = dv) :
    stepFnIter 2 (fmSt h na)
        (.next (.storeK
          [.chain (.addr (.base ⟨f + 3⟩)) [] [],
           .chain (.addr (.base ⟨f + 4⟩)) [] []]
          [.int dv .uint64, .bool okb]
          (.seqn #[]) (frEnvL f) (kOkIf f KT))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (frEnvL f) (kOkIf f KT)),
          fmSt ((h.set (.base ⟨f + 3⟩) (u64c dv)).set (.base ⟨f + 4⟩) (bc okb))
            na, ch) := by
  show stepFnIter (1 + 1) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_store_step (σ := fmSt h na)
    (σ' := { fmSt h na with heap := h.set (.base ⟨f + 3⟩) (u64c dv) })
    (r := .chain (.addr (.base ⟨f + 3⟩)) [] []) (val := .int dv .uint64)
    (rs := [.chain (.addr (.base ⟨f + 4⟩)) [] []]) (vs := [.bool okb])
    (body := .seqn #[]) (env := frEnvL f) (k := kOkIf f KT) (ch := ch)
    (storeTarget_addr hv (by
      show normalizeValueForTy (fmSt h na) tU (.int dv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hdv])))
  have h2 := stepFnIter_one (stepFn_store_step
    (σ := { fmSt h na with heap := h.set (.base ⟨f + 3⟩) (u64c dv) })
    (σ' := { fmSt h na with
      heap := (h.set (.base ⟨f + 3⟩) (u64c dv)).set (.base ⟨f + 4⟩) (bc okb) })
    (r := .chain (.addr (.base ⟨f + 4⟩)) [] []) (val := .bool okb)
    (rs := []) (vs := []) (body := .seqn #[]) (env := frEnvL f)
    (k := kOkIf f KT) (ch := ch)
    (storeTarget_addr hok (by
      show normalizeValueForTy _ .bool (.bool okb) = _
      with_unfolding_all rfl)))
  exact stepFnIter_chain h1 h2

/-- S3d — drained comma-ok stores → the `ok` test's delivery. 5 steps;
reads `ok` at `f+4`. -/
theorem fm_seg3d (h : Heap) (na f : Nat) (okb : Bool) (KT : Cont)
    (ch : Choices)
    (hok : Heap.lookup h (.base ⟨f + 4⟩) = some (bc okb)) :
    stepFnIter 5 (fmSt h na)
        (.next (.storeK [] [] (.seqn #[]) (frEnvL f) (kOkIf f KT))) ch
      = .ok (.retV (.bool okb)
            (.ifK fmHitZero (.seqn #[]) (frEnvL f)
              (.seq [] (frEnvL f) (kMain f KT))),
          fmSt h na, ch) := by
  show stepFnIter (1 + 1 + 2 + 1) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_storeK_nil (σ := fmSt h na)
    (body := .seqn #[]) (env := frEnvL f) (k := kOkIf f KT) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[]) (env := frEnvL f) (rest := [fmOkIf]) (k := kMain f KT)
    (ch := ch))
  have h3 : stepFnIter 2 (fmSt h na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [fmOkIf]) (frEnvL f)
        (kMain f KT))) ch
      = .ok (.evalE (.var "ok") (frEnvL f)
          (.ifK fmHitZero (.seqn #[]) (frEnvL f)
            (.seq [] (frEnvL f) (kMain f KT))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "ok") (env := frEnvL f) (a := ⟨f + 4⟩)
    (k := .ifK fmHitZero (.seqn #[]) (frEnvL f)
      (.seq [] (frEnvL f) (kMain f KT)))
    (ch := ch) (c := bc okb) rfl hok)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4

/-- S4 — `ok` TRUE → `$res0 := v`, return, drain to the frame. 18
steps; reads `v` at `f+3`, writes `$res0` at `f+2`. -/
theorem fm_seg4 (h : Heap) (na f : Nat) (dv old0 : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hv : Heap.lookup h (.base ⟨f + 3⟩) = some (u64c dv))
    (hres : Heap.lookup h (.base ⟨f + 2⟩) = some (u64c old0))
    (hdv : IntKind.normalize .uint64 dv = dv) :
    stepFnIter 18 (fmSt h na)
        (.retV (.bool true)
          (.ifK fmHitZero (.seqn #[]) (frEnvL f)
            (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))) ch
      = .ok (.returning (frameK tv envC f rest K₀),
          fmSt (h.set (.base ⟨f + 2⟩) (u64c dv)) na, ch) := by
  show stepFnIter (3 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 5) _ _ _ = _
  have hA1 : stepFnIter 3 (fmSt h na)
      (.retV (.bool true)
        (.ifK fmHitZero (.seqn #[]) (frEnvL f)
          (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))) ch
      = .ok (.exec (.seqn #[.assign (.var "$res0") (.var "v"), .returnStmt])
            ([] :: frEnvL f)
            (.seq [] ([] :: frEnvL f)
              (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀)))),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hA2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[.assign (.var "$res0") (.var "v"), .returnStmt])
    (env := ([] :: frEnvL f)) (rest := [])
    (k := .seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀)))
    (ch := ch))
  have hA3 : stepFnIter 4 (fmSt h na)
      (.next (.seq ((#[.assign (.var "$res0") (.var "v"),
              .returnStmt] : Array Stmt).toList ++ [])
        ([] :: frEnvL f)
        (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))) ch
      = .ok (.evalE (.var "v") ([] :: frEnvL f)
          (.rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
            (.seqn #[]) ([] :: frEnvL f)
            (.seq [.returnStmt] ([] :: frEnvL f)
              (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have hval := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "v") (env := ([] :: frEnvL f)) (a := ⟨f + 3⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
      (.seqn #[]) ([] :: frEnvL f)
      (.seq [.returnStmt] ([] :: frEnvL f)
        (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀)))))
    (ch := ch) (c := u64c dv) rfl hv)
  have hB : stepFnIter 1 (fmSt h na)
      (.retV (.int dv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
          (.seqn #[]) ([] :: frEnvL f)
          (.seq [.returnStmt] ([] :: frEnvL f)
            (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀)))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨f + 2⟩)) [] []]
            [.int dv .uint64] (.seqn #[]) ([] :: frEnvL f)
            (.seq [.returnStmt] ([] :: frEnvL f)
              (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hC := stepFnIter_one (stepFn_store_step
    (σ := fmSt h na)
    (σ' := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c dv) })
    (r := .chain (.addr (.base ⟨f + 2⟩)) [] []) (val := .int dv .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := ([] :: frEnvL f))
    (k := .seq [.returnStmt] ([] :: frEnvL f)
      (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))
    (ch := ch)
    (storeTarget_addr hres (by
      show normalizeValueForTy (fmSt h na) tU (.int dv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hdv])))
  have hD1 := stepFnIter_one (stepFn_storeK_nil
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c dv) })
    (body := .seqn #[]) (env := ([] :: frEnvL f))
    (k := .seq [.returnStmt] ([] :: frEnvL f)
      (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))
    (ch := ch))
  have hD2 := stepFnIter_one (stepFn_seqn_splice
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c dv) })
    (ss := #[]) (env := ([] :: frEnvL f))
    (rest := [.returnStmt])
    (k := .seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀)))
    (ch := ch))
  have hD3 : stepFnIter 5
      { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c dv) }
      (.next (.seq ((#[] : Array Stmt).toList ++ [.returnStmt]) ([] :: frEnvL f)
        (.seq [] (frEnvL f) (kMain f (frameK tv envC f rest K₀))))) ch
      = .ok (.returning (frameK tv envC f rest K₀),
          { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c dv) }, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hA1 hA2) hA3) hval) hB) hC)
      hD1) hD2) hD3

theorem lookup_cons_self {l : Loc} {c : HeapCell} {rest : Heap} :
    Heap.lookup ((l, c) :: rest) l = some c := by
  simp [Heap.lookup]

theorem set_cons_self {l : Loc} {c c' : HeapCell} {rest : Heap} :
    Heap.set ((l, c) :: rest) l c' = (l, c') :: rest := by
  simp [Heap.set]

/-- The five dead cells a HIT frame leaves behind. -/
def hitCells (f bM : Nat) (kv rv : Int) : Heap :=
  [(.base ⟨f⟩, u64c kv), (.base ⟨f + 1⟩, mapHc bM), (.base ⟨f + 2⟩, u64c rv),
   (.base ⟨f + 3⟩, u64c rv), (.base ⟨f + 4⟩, bc true)]

/-- **The HIT call span** (`2 ≤ k ≤ j`, memo `mtbl j`): 60 steps; the
caller's target cell receives `fibW k` from the table, the memo is
untouched, five frame cells go dead. -/
theorem fmCall_hit (h : Heap) (na bM aT : Nat) (k j : Nat) (oldT : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hk2 : 2 ≤ k) (hkj : k ≤ j) (hk64 : k < 2 ^ 64)
    (hbM : Heap.lookup h (.base ⟨bM⟩) = some (mapDc (mtbl j)))
    (haT : Heap.lookup h (.base ⟨aT⟩) = some (u64c oldT))
    (hfr : FreshFrom h na) (_hbMlt : bM < na) (haTlt : aT < na)
    (henvC : LocalEnv.lookup envC tv = some (.base ⟨aT⟩)) :
    stepFnIter 60 (fmSt h na)
        (.retV (mapHv bM)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref tv])]
            [.int (k : Int) .uint64] [] envC (.seq rest envC K₀))) ch
      = .ok (.next (.seq rest envC K₀),
          fmSt ((h.set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
              ++ hitCells na bM (k : Int) ((fibW k : Nat) : Int)) (na + 5), ch) := by
  show stepFnIter (1 + 8 + 11 + 8 + 1 + 2 + 5 + 18 + 6) _ _ _ = _
  have hEnter := stepFnIter_one (stepFn_call_enter
    (σ := fmSt h na) (fid := ⟨"fibMemo"⟩) (v := mapHv bM)
    (vals := [.int (k : Int) .uint64])
    (plans := [(.chain [], [.ref tv])]) (env := envC)
    (k := .seq rest envC K₀) (ch := ch)
    (fm_enterFrame h na k bM hk64 hfr))
  -- (h ++ frameCells na bM (k : Int) 0) facts
  have hfr₁ : FreshFrom (h ++ frameCells na bM (k : Int) 0) (na + 3) := by
    intro x hx
    rw [lookup_append_right (hfr x (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x))]
    rfl
  have hn₁ : Heap.lookup (h ++ frameCells na bM (k : Int) 0) (.base ⟨na⟩) = some (u64c (k : Int)) := by
    rw [lookup_append_right (hfr na (by omega)), frameCells]
    exact lookup_cons_self
  have hS1 := fm_seg1 (h ++ frameCells na bM (k : Int) 0) (na + 3) na (k : Int) tv envC rest K₀ ch hn₁
  rw [show (decide ((k : Int) < 2)) = false from by
    simp only [decide_eq_false_iff_not]
    intro hc
    have hlt : k < 2 := by exact_mod_cast hc
    omega] at hS1
  have hS3a := fm_seg3a (h ++ frameCells na bM (k : Int) 0) na tv envC rest K₀ ch hfr₁
  -- ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) facts
  have hmem₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (.base ⟨na + 1⟩) = some (mapHc bM) := by
    refine lookup_append_left ?_
    rw [lookup_append_right (hfr (na + 1) (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    exact lookup_cons_self
  have hn₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (.base ⟨na⟩) = some (u64c (k : Int)) := by
    
    exact lookup_append_left hn₁
  have hS3b := fm_seg3b ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (na + 5) na bM (k : Int)
    (frameK tv envC na rest K₀) ch hmem₂ hn₂
  have hmap₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (.base ⟨bM⟩) = some (mapDc (mtbl j)) := by
    exact lookup_append_left (lookup_append_left hbM)
  obtain ⟨hidx, _⟩ := idxOf?_mtbl_some hk2 hkj
  have hget := toEntries_mtbl_get hk2 hkj
  have hDrain := stepFnIter_one (fm_lookup_drain_hit
    (σ := fmSt ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (na + 5)) (f := na) (bM := bM) (kv := (k : Int))
    (M := mtbl j) (i := k - 2) (w := fibW k)
    (KT := frameK tv envC na rest K₀) (ch := ch)
    hmap₂ (unorm_nat_of_lt hk64) hidx hget)
  have hv₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (.base ⟨na + 3⟩) = some (u64c 0) := by
    rw [lookup_append_right (hfr₁ (na + 3) (by omega))]
    exact lookup_cons_self
  have hok₂ : Heap.lookup (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int)))
      (.base ⟨na + 4⟩) = some (bc false) := by
    rw [lookup_set_other (by omega : na + 3 ≠ na + 4),
      lookup_append_right (hfr₁ (na + 4) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
    exact lookup_cons_self
  have hS3c := fm_seg3c ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (na + 5) na ((fibW k : Nat) : Int) true
    (frameK tv envC na rest K₀) ch hv₂ hok₂
    (unorm_nat_of_lt (fibW_lt k))
  -- ((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)) facts
  have hok₃ : Heap.lookup ((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)) (.base ⟨na + 4⟩) = some (bc true) := by
    exact lookup_set_self
  have hS3d := fm_seg3d ((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)) (na + 5) na true (frameK tv envC na rest K₀) ch hok₃
  have hv₃ : Heap.lookup ((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)) (.base ⟨na + 3⟩)
      = some (u64c ((fibW k : Nat) : Int)) := by
    rw [lookup_set_other (by omega : na + 4 ≠ na + 3)]
    exact lookup_set_self
  have hres₃ : Heap.lookup ((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)) (.base ⟨na + 2⟩) = some (u64c 0) := by
    rw [lookup_set_other (by omega : na + 4 ≠ na + 2),
      lookup_set_other (by omega : na + 3 ≠ na + 2)]
    refine .trans (lookup_append_left ?_) rfl
    rw [lookup_append_right (hfr (na + 2) (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
    exact lookup_cons_self
  have hS4 := fm_seg4 ((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)) (na + 5) na ((fibW k : Nat) : Int) 0
    tv envC rest K₀ ch hv₃ hres₃ (unorm_nat_of_lt (fibW_lt k))
  -- (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)).set (.base ⟨na + 2⟩) (u64c ((fibW k : Nat) : Int))) facts
  have hres₄ : Heap.lookup (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)).set (.base ⟨na + 2⟩) (u64c ((fibW k : Nat) : Int))) (.base ⟨na + 2⟩)
      = some (u64c ((fibW k : Nat) : Int)) := by
    exact lookup_set_self
  have haT₄ : Heap.lookup (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)).set (.base ⟨na + 2⟩) (u64c ((fibW k : Nat) : Int))) (.base ⟨aT⟩) = some (u64c oldT) := by
    rw [lookup_set_other (by omega : na + 2 ≠ aT),
      lookup_set_other (by omega : na + 4 ≠ aT),
      lookup_set_other (by omega : na + 3 ≠ aT)]
    exact lookup_append_left (lookup_append_left haT)
  have hS2b := fm_seg2b (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)).set (.base ⟨na + 2⟩) (u64c ((fibW k : Nat) : Int))) (na + 5) na aT ((fibW k : Nat) : Int) oldT
    tv envC rest K₀ ch hres₄ haT₄ henvC (unorm_nat_of_lt (fibW_lt k))
  -- assemble, then rewrite the final heap into the sandwich shape
  have hrun := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hEnter hS1) hS3a) hS3b) hDrain)
      hS3c) hS3d) hS4) hS2b
  have hshape : (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set (.base ⟨na + 3⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨na + 4⟩) (bc true)).set (.base ⟨na + 2⟩) (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int))
      = (h.set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
        ++ hitCells na bM (k : Int) ((fibW k : Nat) : Int) := by
    
    rw [show h ++ frameCells na bM (k : Int) 0
          ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]
        = h ++ (frameCells na bM (k : Int) 0
          ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) from by
      simp [List.append_assoc]]
    rw [set_append_right (hfr (na + 3) (by omega)),
      set_append_right (hfr (na + 4) (by omega)),
      set_append_right (hfr (na + 2) (by omega)),
      set_append_left haT]
    congr 1
    show Heap.set (Heap.set (Heap.set (frameCells na bM (k : Int) 0
        ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) _ _) _ _) _ _
      = hitCells na bM (k : Int) ((fibW k : Nat) : Int)
    rw [frameCells, hitCells]
    rw [show [(.base ⟨na⟩, u64c (k : Int)), (.base ⟨na + 1⟩, mapHc bM),
          (.base ⟨na + 2⟩, u64c 0)]
          ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]
        = [(.base ⟨na⟩, u64c (k : Int)), (.base ⟨na + 1⟩, mapHc bM),
           (.base ⟨na + 2⟩, u64c 0), (.base ⟨na + 3⟩, u64c 0),
           (.base ⟨na + 4⟩, bc false)] from rfl]
    rw [set_cons_ne (base_beq_false (by omega : na ≠ na + 3)),
      set_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 3)),
      set_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 3)),
      set_cons_self,
      set_cons_ne (base_beq_false (by omega : na ≠ na + 4)),
      set_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 4)),
      set_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 4)),
      set_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4)),
      set_cons_self,
      set_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      set_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2)),
      set_cons_self]
  rw [hshape] at hrun
  exact hrun

/-! ## The miss path -/

/-- The caller env after `$c0` is declared at `a0`. -/
def uEnvC0 (f a0 : Nat) : LocalEnv := [("$c0", .base ⟨a0⟩)] :: frEnv f
/-- … and after `$c1` at `a1`. -/
def uEnvC1 (f a0 a1 : Nat) : LocalEnv :=
  [("$c1", .base ⟨a1⟩), ("$c0", .base ⟨a0⟩)] :: frEnv f
/-- … and after `r` at `a2`. -/
def uEnvR (f a0 a1 a2 : Nat) : LocalEnv :=
  [("r", .base ⟨a2⟩), ("$c1", .base ⟨a1⟩), ("$c0", .base ⟨a0⟩)] :: frEnv f

/-- S5 — `ok` FALSE → the main sequence's head. 3 steps. -/
theorem fm_seg5 (h : Heap) (na f : Nat) (KT : Cont) (ch : Choices) :
    stepFnIter 3 (fmSt h na)
        (.retV (.bool false)
          (.ifK fmHitZero (.seqn #[]) (frEnvL f)
            (.seq [] (frEnvL f) (kMain f KT)))) ch
      = .ok (.next (kMain f KT), fmSt h na, ch) := by
  show stepFnIter (1 + 1 + 1) _ _ _ = _
  have h1 : stepFnIter 1 (fmSt h na)
      (.retV (.bool false)
        (.ifK fmHitZero (.seqn #[]) (frEnvL f)
          (.seq [] (frEnvL f) (kMain f KT)))) ch
      = .ok (.exec (.seqn #[]) (frEnvL f) (.seq [] (frEnvL f) (kMain f KT)),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[]) (env := frEnvL f) (rest := []) (k := kMain f KT) (ch := ch))
  have h3 : stepFnIter 1 (fmSt h na)
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (frEnvL f) (kMain f KT)))
      ch
      = .ok (.next (kMain f KT), fmSt h na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- S6 — the `$c0` call's preparation: allocate `$c0` at the current
`na`, evaluate `n − 1` and `memo`. 13 steps. -/
theorem fm_seg6 (h : Heap) (na f bM : Nat) (kv : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hn : Heap.lookup h (.base ⟨f⟩) = some (u64c kv))
    (hmem : Heap.lookup h (.base ⟨f + 1⟩) = some (mapHc bM))
    (hna : Heap.lookup h (.base ⟨na⟩) = none) :
    stepFnIter 13 (fmSt h na)
        (.next (kMain f (frameK tv envC f rest K₀))) ch
      = .ok (.retV (mapHv bM)
            (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c0"])]
              [.int (IntKind.normalize .uint64 (kv - 1)) .uint64] []
              (uEnvC0 f na)
              (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f na)
                (frameK tv envC f rest K₀))),
          fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 3 + 1 + 4 + 1) _ _ _ = _
  have h1 : stepFnIter 1 (fmSt h na)
      (.next (kMain f (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.seqn #[.initialization { id := "$c0", typ := tU },
            .call #[.var "$c0"] ⟨"fibMemo"⟩
              #[.sub (.var "n") (.intLit 1 .uint64), .var "memo"]])
          (frEnv2 f)
          (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (frEnv2 f)
            (frameK tv envC f rest K₀)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[.initialization { id := "$c0", typ := tU },
             .call #[.var "$c0"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 1 .uint64), .var "memo"]])
    (env := frEnv2 f)
    (rest := [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn])
    (k := frameK tv envC f rest K₀) (ch := ch))
  have h3 : stepFnIter 1 (fmSt h na)
      (.next (.seq ((#[.initialization { id := "$c0", typ := tU },
             .call #[.var "$c0"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 1 .uint64), .var "memo"]]
          : Array Stmt).toList
          ++ [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn])
        (frEnv2 f) (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.initialization { id := "$c0", typ := tU }) (frEnv2 f)
          (.seq [.call #[.var "$c0"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 1 .uint64), .var "memo"],
             fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
            (frEnv2 f) (frameK tv envC f rest K₀)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_init_seq (σ := fmSt h na)
    (p := { id := "$c0", typ := tU })
    (rest := [.call #[.var "$c0"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 1 .uint64), .var "memo"],
             fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn])
    (env := frEnv2 f) (k := frameK tv envC f rest K₀)
    (ch := ch) (v := .int 0 .uint64) (by with_unfolding_all rfl))
  rw [show (fmSt h na).nextAddr = na from rfl,
    show Heap.set (fmSt h na).heap (.base ⟨na⟩) ⟨some tU, .int 0 .uint64⟩
      = h ++ [(Loc.base ⟨na⟩, u64c 0)] from set_fresh hna] at h4
  have h5 : stepFnIter 3 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.next (.seq [.call #[.var "$c0"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 1 .uint64), .var "memo"],
             fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
        (LocalEnv.declare (frEnv2 f) "$c0" (.base ⟨na⟩))
        (frameK tv envC f rest K₀))) ch
      = .ok (.evalE (.var "n") (uEnvC0 f na)
          (.strictK .sub [] [.intLit 1 .uint64] (uEnvC0 f na)
            (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c0"])] [] [.var "memo"]
              (uEnvC0 f na)
              (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f na)
                (frameK tv envC f rest K₀)))),
        fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hnv : Heap.lookup (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨f⟩)
      = some (u64c kv) := lookup_append_left hn
  have h6 := stepFnIter_one (stepFn_var
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
    (x := "n") (env := uEnvC0 f na) (a := ⟨f⟩)
    (k := .strictK .sub [] [.intLit 1 .uint64] (uEnvC0 f na)
      (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c0"])] [] [.var "memo"]
        (uEnvC0 f na)
        (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f na)
          (frameK tv envC f rest K₀))))
    (ch := ch) (c := u64c kv) rfl hnv)
  have h7 : stepFnIter 4 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.retV (.int kv .uint64)
        (.strictK .sub [] [.intLit 1 .uint64] (uEnvC0 f na)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c0"])] [] [.var "memo"]
            (uEnvC0 f na)
            (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f na)
              (frameK tv envC f rest K₀))))) ch
      = .ok (.evalE (.var "memo") (uEnvC0 f na)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c0"])]
            [.int (IntKind.normalize .uint64 (kv - 1)) .uint64] []
            (uEnvC0 f na)
            (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f na)
              (frameK tv envC f rest K₀))),
        fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hmv : Heap.lookup (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨f + 1⟩)
      = some (mapHc bM) := lookup_append_left hmem
  have h8 := stepFnIter_one (stepFn_var
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
    (x := "memo") (env := uEnvC0 f na) (a := ⟨f + 1⟩)
    (k := .callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c0"])]
      [.int (IntKind.normalize .uint64 (kv - 1)) .uint64] []
      (uEnvC0 f na)
      (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f na)
        (frameK tv envC f rest K₀)))
    (ch := ch) (c := mapHc bM) rfl hmv)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7) h8


/-- S7 — the `$c1` call's preparation (mirror of S6 at `n − 2`). 13 steps. -/
theorem fm_seg7 (h : Heap) (na f bM a0 : Nat) (kv : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hn : Heap.lookup h (.base ⟨f⟩) = some (u64c kv))
    (hmem : Heap.lookup h (.base ⟨f + 1⟩) = some (mapHc bM))
    (hna : Heap.lookup h (.base ⟨na⟩) = none) :
    stepFnIter 13 (fmSt h na)
        (.next (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f a0)
          (frameK tv envC f rest K₀))) ch
      = .ok (.retV (mapHv bM)
            (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c1"])]
              [.int (IntKind.normalize .uint64 (kv - 2)) .uint64] []
              (uEnvC1 f a0 na)
              (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na)
                (frameK tv envC f rest K₀))),
          fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 3 + 1 + 4 + 1) _ _ _ = _
  have h1 : stepFnIter 1 (fmSt h na)
      (.next (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f a0)
        (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.seqn #[.initialization { id := "$c1", typ := tU },
            .call #[.var "$c1"] ⟨"fibMemo"⟩
              #[.sub (.var "n") (.intLit 2 .uint64), .var "memo"]])
          (uEnvC0 f a0)
          (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f a0)
            (frameK tv envC f rest K₀)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[.initialization { id := "$c1", typ := tU },
             .call #[.var "$c1"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 2 .uint64), .var "memo"]])
    (env := uEnvC0 f a0)
    (rest := [fmRSeqn, fmMapAsgn, fmRetSeqn])
    (k := frameK tv envC f rest K₀) (ch := ch))
  have h3 : stepFnIter 1 (fmSt h na)
      (.next (.seq ((#[.initialization { id := "$c1", typ := tU },
             .call #[.var "$c1"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 2 .uint64), .var "memo"]]
          : Array Stmt).toList
          ++ [fmRSeqn, fmMapAsgn, fmRetSeqn])
        (uEnvC0 f a0) (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.initialization { id := "$c1", typ := tU }) (uEnvC0 f a0)
          (.seq [.call #[.var "$c1"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 2 .uint64), .var "memo"],
             fmRSeqn, fmMapAsgn, fmRetSeqn]
            (uEnvC0 f a0) (frameK tv envC f rest K₀)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_init_seq (σ := fmSt h na)
    (p := { id := "$c1", typ := tU })
    (rest := [.call #[.var "$c1"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 2 .uint64), .var "memo"],
             fmRSeqn, fmMapAsgn, fmRetSeqn])
    (env := uEnvC0 f a0) (k := frameK tv envC f rest K₀)
    (ch := ch) (v := .int 0 .uint64) (by with_unfolding_all rfl))
  rw [show (fmSt h na).nextAddr = na from rfl,
    show Heap.set (fmSt h na).heap (.base ⟨na⟩) ⟨some tU, .int 0 .uint64⟩
      = h ++ [(Loc.base ⟨na⟩, u64c 0)] from set_fresh hna] at h4
  have h5 : stepFnIter 3 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.next (.seq [.call #[.var "$c1"] ⟨"fibMemo"⟩
               #[.sub (.var "n") (.intLit 2 .uint64), .var "memo"],
             fmRSeqn, fmMapAsgn, fmRetSeqn]
        (LocalEnv.declare (uEnvC0 f a0) "$c1" (.base ⟨na⟩))
        (frameK tv envC f rest K₀))) ch
      = .ok (.evalE (.var "n") (uEnvC1 f a0 na)
          (.strictK .sub [] [.intLit 2 .uint64] (uEnvC1 f a0 na)
            (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c1"])] [] [.var "memo"]
              (uEnvC1 f a0 na)
              (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na)
                (frameK tv envC f rest K₀)))),
        fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hnv : Heap.lookup (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨f⟩)
      = some (u64c kv) := lookup_append_left hn
  have h6 := stepFnIter_one (stepFn_var
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
    (x := "n") (env := uEnvC0 f na) (a := ⟨f⟩)
    (k := .strictK .sub [] [.intLit 2 .uint64] (uEnvC1 f a0 na)
      (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c1"])] [] [.var "memo"]
        (uEnvC1 f a0 na)
        (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na)
          (frameK tv envC f rest K₀))))
    (ch := ch) (c := u64c kv) rfl hnv)
  have h7 : stepFnIter 4 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.retV (.int kv .uint64)
        (.strictK .sub [] [.intLit 2 .uint64] (uEnvC1 f a0 na)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c1"])] [] [.var "memo"]
            (uEnvC1 f a0 na)
            (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na)
              (frameK tv envC f rest K₀))))) ch
      = .ok (.evalE (.var "memo") (uEnvC1 f a0 na)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c1"])]
            [.int (IntKind.normalize .uint64 (kv - 2)) .uint64] []
            (uEnvC1 f a0 na)
            (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na)
              (frameK tv envC f rest K₀))),
        fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hmv : Heap.lookup (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨f + 1⟩)
      = some (mapHc bM) := lookup_append_left hmem
  have h8 := stepFnIter_one (stepFn_var
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
    (x := "memo") (env := uEnvC0 f na) (a := ⟨f + 1⟩)
    (k := .callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c1"])]
      [.int (IntKind.normalize .uint64 (kv - 2)) .uint64] []
      (uEnvC1 f a0 na)
      (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na)
        (frameK tv envC f rest K₀)))
    (ch := ch) (c := mapHc bM) rfl hmv)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7) h8

-- `unorm_idem` (uint64 normalize idempotence) — DELETED (WP arc s1
-- lift 1, discharging the C4 resolution recorded in the long docstring
-- that lived here): `intKind_normalize_idem` was lifted OUT of
-- `HeapBridge` into the Iris-free `GoLean.SliceMem`, exactly as this
-- site's promotion-ledger item asked, so this closure consumes the
-- kind-generic kit form directly and stays Iris-free. The full C4
-- ruling text (with its round-3/round-4 corrections) remains on record
-- in `docs/2026-08-16_wp-library-design.md` §OPERATOR CROSS-CORRECTION
-- NOTE (a) and `docs/gallery-campaign-log/g1.md` §Unit G1.7.

/-- S8 — `r := $c0 + $c1`: allocate `r` at `na`, read both results,
apply the wrapped addition, store. 17 steps. -/
theorem fm_seg8 (h : Heap) (na f a0 a1 : Nat) (c0v c1v : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hc0 : Heap.lookup h (.base ⟨a0⟩) = some (u64c c0v))
    (hc1 : Heap.lookup h (.base ⟨a1⟩) = some (u64c c1v))
    (hna : Heap.lookup h (.base ⟨na⟩) = none) :
    stepFnIter 17 (fmSt h na)
        (.next (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 a1)
          (frameK tv envC f rest K₀))) ch
      = .ok (.next (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
            (frameK tv envC f rest K₀)),
          fmSt (h ++ [(Loc.base ⟨na⟩,
              u64c (IntKind.normalize .uint64 (c0v + c1v)))]) (na + 1), ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 5 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have h1 : stepFnIter 1 (fmSt h na)
      (.next (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 a1)
        (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.seqn #[.initialization { id := "r", typ := tU },
            .assign (.var "r") (.add (.var "$c0") (.var "$c1"))])
          (uEnvC1 f a0 a1)
          (.seq [fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 a1)
            (frameK tv envC f rest K₀)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[.initialization { id := "r", typ := tU },
             .assign (.var "r") (.add (.var "$c0") (.var "$c1"))])
    (env := uEnvC1 f a0 a1) (rest := [fmMapAsgn, fmRetSeqn])
    (k := frameK tv envC f rest K₀) (ch := ch))
  have h3 : stepFnIter 1 (fmSt h na)
      (.next (.seq ((#[.initialization { id := "r", typ := tU },
             .assign (.var "r") (.add (.var "$c0") (.var "$c1"))]
          : Array Stmt).toList ++ [fmMapAsgn, fmRetSeqn])
        (uEnvC1 f a0 a1) (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.initialization { id := "r", typ := tU }) (uEnvC1 f a0 a1)
          (.seq [.assign (.var "r") (.add (.var "$c0") (.var "$c1")),
             fmMapAsgn, fmRetSeqn]
            (uEnvC1 f a0 a1) (frameK tv envC f rest K₀)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_init_seq (σ := fmSt h na)
    (p := { id := "r", typ := tU })
    (rest := [.assign (.var "r") (.add (.var "$c0") (.var "$c1")),
             fmMapAsgn, fmRetSeqn])
    (env := uEnvC1 f a0 a1) (k := frameK tv envC f rest K₀)
    (ch := ch) (v := .int 0 .uint64) (by with_unfolding_all rfl))
  rw [show (fmSt h na).nextAddr = na from rfl,
    show Heap.set (fmSt h na).heap (.base ⟨na⟩) ⟨some tU, .int 0 .uint64⟩
      = h ++ [(Loc.base ⟨na⟩, u64c 0)] from set_fresh hna] at h4
  have h5 : stepFnIter 5 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.next (.seq [.assign (.var "r") (.add (.var "$c0") (.var "$c1")),
             fmMapAsgn, fmRetSeqn]
        (LocalEnv.declare (uEnvC1 f a0 a1) "r" (.base ⟨na⟩))
        (frameK tv envC f rest K₀))) ch
      = .ok (.evalE (.var "$c0") (uEnvR f a0 a1 na)
          (.strictK .add [] [.var "$c1"] (uEnvR f a0 a1 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (uEnvR f a0 a1 na)
              (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
                (frameK tv envC f rest K₀)))),
        fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hc0' : Heap.lookup (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨a0⟩)
      = some (u64c c0v) := lookup_append_left hc0
  have h6 := stepFnIter_one (stepFn_var
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
    (x := "$c0") (env := uEnvR f a0 a1 na) (a := ⟨a0⟩)
    (k := .strictK .add [] [.var "$c1"] (uEnvR f a0 a1 na)
      (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
        (.seqn #[]) (uEnvR f a0 a1 na)
        (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
          (frameK tv envC f rest K₀))))
    (ch := ch) (c := u64c c0v) rfl hc0')
  have h7 : stepFnIter 1 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.retV (.int c0v .uint64)
        (.strictK .add [] [.var "$c1"] (uEnvR f a0 a1 na)
          (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
            (.seqn #[]) (uEnvR f a0 a1 na)
            (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
              (frameK tv envC f rest K₀))))) ch
      = .ok (.evalE (.var "$c1") (uEnvR f a0 a1 na)
          (.strictK .add [.int c0v .uint64] [] (uEnvR f a0 a1 na)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (uEnvR f a0 a1 na)
              (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
                (frameK tv envC f rest K₀)))),
        fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hc1' : Heap.lookup (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨a1⟩)
      = some (u64c c1v) := lookup_append_left hc1
  have h8 := stepFnIter_one (stepFn_var
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
    (x := "$c1") (env := uEnvR f a0 a1 na) (a := ⟨a1⟩)
    (k := .strictK .add [.int c0v .uint64] [] (uEnvR f a0 a1 na)
      (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
        (.seqn #[]) (uEnvR f a0 a1 na)
        (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
          (frameK tv envC f rest K₀))))
    (ch := ch) (c := u64c c1v) rfl hc1')
  have h9 : stepFnIter 1 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.retV (.int c1v .uint64)
        (.strictK .add [.int c0v .uint64] [] (uEnvR f a0 a1 na)
          (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
            (.seqn #[]) (uEnvR f a0 a1 na)
            (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
              (frameK tv envC f rest K₀))))) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (c0v + c1v)) .uint64)
          (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
            (.seqn #[]) (uEnvR f a0 a1 na)
            (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
              (frameK tv envC f rest K₀))),
        fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have h10 : stepFnIter 1 (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.retV (.int (IntKind.normalize .uint64 (c0v + c1v)) .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (uEnvR f a0 a1 na)
          (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
            (frameK tv envC f rest K₀)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.int (IntKind.normalize .uint64 (c0v + c1v)) .uint64]
            (.seqn #[]) (uEnvR f a0 a1 na)
            (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
              (frameK tv envC f rest K₀))),
          fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have hlkr : Heap.lookup (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨na⟩)
      = some (u64c 0) := by
    rw [lookup_append_right hna]
    exact lookup_cons_self
  have hstr : storeTarget (fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
      (.chain (.addr (.base ⟨na⟩)) [] [])
      (.int (IntKind.normalize .uint64 (c0v + c1v)) .uint64)
      = .ok { fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1) with
          heap := Heap.set (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨na⟩)
            (u64c (IntKind.normalize .uint64 (c0v + c1v))) } :=
    storeTarget_addr hlkr (by
      show normalizeValueForTy _ tU
        (.int (IntKind.normalize .uint64 (c0v + c1v)) .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        intKind_normalize_idem])
  have h11 := stepFnIter_one (stepFn_store_step
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1))
    (σ' := { fmSt (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (na + 1) with
      heap := Heap.set (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨na⟩)
        (u64c (IntKind.normalize .uint64 (c0v + c1v))) })
    (r := .chain (.addr (.base ⟨na⟩)) [] [])
    (val := .int (IntKind.normalize .uint64 (c0v + c1v)) .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := uEnvR f a0 a1 na)
    (k := .seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
      (frameK tv envC f rest K₀))
    (ch := ch) hstr)
  rw [show Heap.set (h ++ [(Loc.base ⟨na⟩, u64c 0)]) (.base ⟨na⟩)
        (u64c (IntKind.normalize .uint64 (c0v + c1v)))
      = h ++ [(Loc.base ⟨na⟩, u64c (IntKind.normalize .uint64 (c0v + c1v)))]
    from by
      rw [set_append_right hna, set_singleton_self]] at h11
  have h12 := stepFnIter_one (stepFn_storeK_nil
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩,
        u64c (IntKind.normalize .uint64 (c0v + c1v)))]) (na + 1))
    (body := .seqn #[]) (env := uEnvR f a0 a1 na)
    (k := .seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 na)
      (frameK tv envC f rest K₀)) (ch := ch))
  have h13 := stepFnIter_one (stepFn_seqn_splice
    (σ := fmSt (h ++ [(Loc.base ⟨na⟩,
        u64c (IntKind.normalize .uint64 (c0v + c1v)))]) (na + 1))
    (ss := #[]) (env := uEnvR f a0 a1 na)
    (rest := [fmMapAsgn, fmRetSeqn])
    (k := frameK tv envC f rest K₀) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3)
          h4) h5) h6) h7) h8) h9) h10) h11) h12) h13

/-- S9 — `memo[n] = r`: read the three operands, apply the map
insert. 8 steps; the map data cell at `bM` gains the entry. -/
theorem fm_seg9 (h : Heap) (na f bM a0 a1 a2 : Nat) (kv rv : Int)
    (M : List (Int × Nat)) (v : Nat)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hmem : Heap.lookup h (.base ⟨f + 1⟩) = some (mapHc bM))
    (hn : Heap.lookup h (.base ⟨f⟩) = some (u64c kv))
    (hr : Heap.lookup h (.base ⟨a2⟩) = some (u64c rv))
    (hmap : Heap.lookup h (.base ⟨bM⟩) = some (mapDc M))
    (hkv : IntKind.normalize .uint64 kv = kv)
    (hrv : rv = (v : Int)) (hv64 : v < 2 ^ 64) :
    stepFnIter 8 (fmSt h na)
        (.next (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 a2)
          (frameK tv envC f rest K₀))) ch
      = .ok (.next (.seq [fmRetSeqn] (uEnvR f a0 a1 a2)
            (frameK tv envC f rest K₀)),
          fmSt (Heap.set h (.base ⟨bM⟩) (mapDc (setk M kv v))) na, ch) := by
  show stepFnIter (2 + 1 + 1 + 1 + 1 + 1 + 1) _ _ _ = _
  have h1 : stepFnIter 2 (fmSt h na)
      (.next (.seq [fmMapAsgn, fmRetSeqn] (uEnvR f a0 a1 a2)
        (frameK tv envC f rest K₀))) ch
      = .ok (.evalE (.var "memo") (uEnvR f a0 a1 a2)
          (.stmtOpK (.mapAssign tU tU) 0 []
            [.var "n", .var "r"] (uEnvR f a0 a1 a2)
            (.seq [fmRetSeqn] (uEnvR f a0 a1 a2)
              (frameK tv envC f rest K₀))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "memo") (env := uEnvR f a0 a1 a2) (a := ⟨f + 1⟩)
    (k := .stmtOpK (.mapAssign tU tU) 0 []
      [.var "n", .var "r"] (uEnvR f a0 a1 a2)
      (.seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀)))
    (ch := ch) (c := mapHc bM) rfl hmem)
  have h3 : stepFnIter 1 (fmSt h na)
      (.retV (mapHv bM)
        (.stmtOpK (.mapAssign tU tU) 0 []
          [.var "n", .var "r"] (uEnvR f a0 a1 a2)
          (.seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀)))) ch
      = .ok (.evalE (.var "n") (uEnvR f a0 a1 a2)
          (.stmtOpK (.mapAssign tU tU) 0 [mapHv bM]
            [.var "r"] (uEnvR f a0 a1 a2)
            (.seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "n") (env := uEnvR f a0 a1 a2) (a := ⟨f⟩)
    (k := .stmtOpK (.mapAssign tU tU) 0 [mapHv bM]
      [.var "r"] (uEnvR f a0 a1 a2)
      (.seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀)))
    (ch := ch) (c := u64c kv) rfl hn)
  have h5 : stepFnIter 1 (fmSt h na)
      (.retV (.int kv .uint64)
        (.stmtOpK (.mapAssign tU tU) 0 [mapHv bM]
          [.var "r"] (uEnvR f a0 a1 a2)
          (.seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀)))) ch
      = .ok (.evalE (.var "r") (uEnvR f a0 a1 a2)
          (.stmtOpK (.mapAssign tU tU) 0 [.int kv .uint64, mapHv bM]
            [] (uEnvR f a0 a1 a2)
            (.seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h6 := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "r") (env := uEnvR f a0 a1 a2) (a := ⟨a2⟩)
    (k := .stmtOpK (.mapAssign tU tU) 0 [.int kv .uint64, mapHv bM]
      [] (uEnvR f a0 a1 a2)
      (.seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀)))
    (ch := ch) (c := u64c rv) rfl hr)
  have hasg : mapAssignValue (fmSt h na) tU tU (mapHv bM) (.int kv .uint64)
      (.int rv .uint64)
      = .ok { fmSt h na with
          heap := Heap.set h (.base ⟨bM⟩) (mapDc (setk M kv v)) } := by
    subst hrv
    exact mapAssignValue_toEntries hmap hkv (unorm_nat_of_lt hv64)
  have h7 := stepFnIter_one (stepFn_mapAssign_apply (σ := fmSt h na)
    (σ' := { fmSt h na with
      heap := Heap.set h (.base ⟨bM⟩) (mapDc (setk M kv v)) })
    (kt := tU) (vt := tU) (b := mapHv bM) (kv := .int kv .uint64)
    (vv := .int rv .uint64) (env := uEnvR f a0 a1 a2)
    (k := .seq [fmRetSeqn] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀))
    (ch := ch) hasg)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4)
      h5) h6) h7

/-- S10 — `$res0 := r`, return, drain to the frame. 14 steps. -/
theorem fm_seg10 (h : Heap) (na f a0 a1 a2 : Nat) (rv old0 : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hr : Heap.lookup h (.base ⟨a2⟩) = some (u64c rv))
    (hres : Heap.lookup h (.base ⟨f + 2⟩) = some (u64c old0))
    (hrv : IntKind.normalize .uint64 rv = rv) :
    stepFnIter 14 (fmSt h na)
        (.next (.seq [fmRetSeqn] (uEnvR f a0 a1 a2)
          (frameK tv envC f rest K₀))) ch
      = .ok (.returning (frameK tv envC f rest K₀),
          fmSt (h.set (.base ⟨f + 2⟩) (u64c rv)) na, ch) := by
  show stepFnIter (1 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 3) _ _ _ = _
  have h1 : stepFnIter 1 (fmSt h na)
      (.next (.seq [fmRetSeqn] (uEnvR f a0 a1 a2)
        (frameK tv envC f rest K₀))) ch
      = .ok (.exec (.seqn #[.assign (.var "$res0") (.var "r"), .returnStmt])
          (uEnvR f a0 a1 a2)
          (.seq [] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := fmSt h na)
    (ss := #[.assign (.var "$res0") (.var "r"), .returnStmt])
    (env := uEnvR f a0 a1 a2) (rest := [])
    (k := frameK tv envC f rest K₀) (ch := ch))
  have h3 : stepFnIter 4 (fmSt h na)
      (.next (.seq ((#[.assign (.var "$res0") (.var "r"),
            .returnStmt] : Array Stmt).toList ++ [])
        (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀))) ch
      = .ok (.evalE (.var "r") (uEnvR f a0 a1 a2)
          (.rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
            (.seqn #[]) (uEnvR f a0 a1 a2)
            (.seq [.returnStmt] (uEnvR f a0 a1 a2)
              (frameK tv envC f rest K₀))),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "r") (env := uEnvR f a0 a1 a2) (a := ⟨a2⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
      (.seqn #[]) (uEnvR f a0 a1 a2)
      (.seq [.returnStmt] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀)))
    (ch := ch) (c := u64c rv) rfl hr)
  have h5 : stepFnIter 1 (fmSt h na)
      (.retV (.int rv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨f + 2⟩)) [] []] [] []
          (.seqn #[]) (uEnvR f a0 a1 a2)
          (.seq [.returnStmt] (uEnvR f a0 a1 a2)
            (frameK tv envC f rest K₀)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨f + 2⟩)) [] []]
            [.int rv .uint64] (.seqn #[]) (uEnvR f a0 a1 a2)
            (.seq [.returnStmt] (uEnvR f a0 a1 a2)
              (frameK tv envC f rest K₀))),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have h6 := stepFnIter_one (stepFn_store_step (σ := fmSt h na)
    (σ' := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c rv) })
    (r := .chain (.addr (.base ⟨f + 2⟩)) [] []) (val := .int rv .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := uEnvR f a0 a1 a2)
    (k := .seq [.returnStmt] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀))
    (ch := ch)
    (storeTarget_addr hres (by
      show normalizeValueForTy (fmSt h na) tU (.int rv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hrv])))
  have h7 := stepFnIter_one (stepFn_storeK_nil
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c rv) })
    (body := .seqn #[]) (env := uEnvR f a0 a1 a2)
    (k := .seq [.returnStmt] (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀))
    (ch := ch))
  have h8 := stepFnIter_one (stepFn_seqn_splice
    (σ := { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c rv) })
    (ss := #[]) (env := uEnvR f a0 a1 a2) (rest := [.returnStmt])
    (k := frameK tv envC f rest K₀) (ch := ch))
  have h9 : stepFnIter 3
      { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c rv) }
      (.next (.seq ((#[] : Array Stmt).toList ++ [.returnStmt])
        (uEnvR f a0 a1 a2) (frameK tv envC f rest K₀))) ch
      = .ok (.returning (frameK tv envC f rest K₀),
          { fmSt h na with heap := Heap.set h (.base ⟨f + 2⟩) (u64c rv) },
          ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7)
      h8) h9

/-- Setting a cell to its current value is the identity. -/
theorem set_self_of_lookup {h : Heap} {l : Loc} {c : HeapCell}
    (hl : Heap.lookup h l = some c) : Heap.set h l c = h := by
  induction h with
  | nil => cases hl
  | cons p rest ih =>
      obtain ⟨k, c₀⟩ := p
      simp only [Heap.lookup] at hl
      cases hb : (k == l) with
      | true =>
          simp only [hb, if_true] at hl
          have hc : c₀ = c := by simpa using hl
          simp [Heap.set, hb, hc]
      | false =>
          rw [hb] at hl
          simp only [Bool.false_eq_true, if_false] at hl
          simp [Heap.set, hb, ih hl]

/-- **The BUILD tail** — shared by every `fmCall_build` case: from the
`$c1` sequence head with `$c0` already holding `fibW (k−1)` and the
memo at `mtbl (k−1)`, through the second (quick) call, the wrapped
addition, the memo insert and the frame exit. ≤ 118 steps. -/
theorem fmBuild_tail (g : Heap) (na₁ f bM aT a0 : Nat) (k : Nat) (oldT : Int)
    (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
    (ch : Choices)
    (hk2 : 2 ≤ k) (hk64 : k < 2 ^ 64)
    (hgn : Heap.lookup g (.base ⟨f⟩) = some (u64c (k : Int)))
    (hgm : Heap.lookup g (.base ⟨f + 1⟩) = some (mapHc bM))
    (hgres : Heap.lookup g (.base ⟨f + 2⟩) = some (u64c 0))
    (hgbM : Heap.lookup g (.base ⟨bM⟩) = some (mapDc (mtbl (k - 1))))
    (hga0 : Heap.lookup g (.base ⟨a0⟩) = some (u64c ((fibW (k - 1) : Nat) : Int)))
    (hgaT : Heap.lookup g (.base ⟨aT⟩) = some (u64c oldT))
    (hfr : FreshFrom g na₁)
    (hbMf : bM < f) (haTf : aT < f) (hfa0 : f + 2 < a0) (ha0lt : a0 < na₁)
    (henvC : LocalEnv.lookup envC tv = some (.base ⟨aT⟩)) :
    ∃ (F : Nat) (junkT : Heap) (na₂ : Nat),
      F ≤ 118 ∧ na₁ + 4 ≤ na₂ ∧
      stepFnIter F (fmSt g na₁)
        (.next (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC0 f a0)
          (frameK tv envC f rest K₀))) ch
      = .ok (.next (.seq rest envC K₀),
          fmSt ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
              (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩)
              (u64c ((fibW k : Nat) : Int))) ++ junkT) na₂, ch)
      ∧ FreshFrom ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
          (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩)
          (u64c ((fibW k : Nat) : Int))) ++ junkT) na₂ := by
  -- the map data cell and the caller's target cell are distinct
  -- (different contents)
  have hbMaT : bM ≠ aT := by
    intro he
    rw [he] at hgbM
    rw [hgbM] at hgaT
    simp [mapDc, u64c] at hgaT
  -- S7: allocate `$c1` at na₁, deliver the (k−2) argument
  have hS7 := fm_seg7 g na₁ f bM a0 (k : Int) tv envC rest K₀ ch hgn hgm
    (hfr na₁ (by omega))
  have harg2 : IntKind.normalize .uint64 ((k : Int) - 2)
      = ((k - 2 : Nat) : Int) := by
    rw [show (k : Int) - 2 = ((k - 2 : Nat) : Int) from by omega]
    exact unorm_nat_of_lt (by omega)
  rw [harg2] at hS7
  -- shared facts about g ++ [(na₁, u64c 0)]
  have hfr' : FreshFrom (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]) (na₁ + 1) := by
    intro x hx
    rw [lookup_append_right (hfr x (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na₁ ≠ x))]
    rfl
  have haT' : Heap.lookup (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]) (.base ⟨na₁⟩)
      = some (u64c 0) := by
    rw [lookup_append_right (hfr na₁ (by omega))]
    exact lookup_cons_self
  have henv1 : LocalEnv.lookup (uEnvC1 f a0 na₁) "$c1"
      = some (Loc.base ⟨na₁⟩) := rfl
  -- dispatch the second call
  have hcall2 : ∃ (F₂ : Nat) (C : Heap) (na₂ : Nat),
      F₂ ≤ 60 ∧ na₁ + 1 + 3 ≤ na₂ ∧
      stepFnIter F₂ (fmSt (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]) (na₁ + 1))
        (.retV (mapHv bM)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c1"])]
            [.int ((k - 2 : Nat) : Int) .uint64] [] (uEnvC1 f a0 na₁)
            (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na₁)
              (frameK tv envC f rest K₀)))) ch
      = .ok (.next (.seq [fmRSeqn, fmMapAsgn, fmRetSeqn] (uEnvC1 f a0 na₁)
            (frameK tv envC f rest K₀)),
          fmSt ((g ++ [(Loc.base ⟨na₁⟩,
              u64c ((fibW (k - 2) : Nat) : Int))]) ++ C) na₂, ch)
      ∧ FreshFrom ((g ++ [(Loc.base ⟨na₁⟩,
          u64c ((fibW (k - 2) : Nat) : Int))]) ++ C) na₂ := by
    by_cases hks : k - 2 ≤ 1
    · -- base sub-call
      have hb := fmCall_base (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]) (na₁ + 1) bM na₁
        (k - 2) 0 "$c1" (uEnvC1 f a0 na₁)
        [fmRSeqn, fmMapAsgn, fmRetSeqn] (frameK tv envC f rest K₀) ch
        hks haT' hfr' (by omega) henv1
      refine ⟨32, frameCells (na₁ + 1) bM ((k - 2 : Nat) : Int)
        ((k - 2 : Nat) : Int), na₁ + 1 + 3, by omega, by omega, ?_, ?_⟩
      · rw [show (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]).set (.base ⟨na₁⟩)
              (u64c ((fibW (k - 2) : Nat) : Int))
            = g ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] from by
          rw [set_append_right (hfr na₁ (by omega)), set_singleton_self]] at hb
        rw [show ((fibW (k - 2) : Nat) : Int) = ((k - 2 : Nat) : Int) from by
          rw [fibW_small hks]] at hb ⊢
        exact hb
      · rw [show ((fibW (k - 2) : Nat) : Int) = ((k - 2 : Nat) : Int) from by
          rw [fibW_small hks]]
        intro x hx
        rw [lookup_append_right (by
            rw [lookup_append_right (hfr x (by omega))]
            exact lookup_cons_ne (base_beq_false (by omega : na₁ ≠ x))),
          frameCells,
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 + 1 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 + 2 ≠ x))]
        rfl
    · -- hit sub-call at ceiling k−1
      have hks2 : 2 ≤ k - 2 := by omega
      have hbM' : Heap.lookup (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]) (.base ⟨bM⟩)
          = some (mapDc (mtbl (k - 1))) := lookup_append_left hgbM
      have hh := fmCall_hit (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]) (na₁ + 1) bM na₁
        (k - 2) (k - 1) 0 "$c1" (uEnvC1 f a0 na₁)
        [fmRSeqn, fmMapAsgn, fmRetSeqn] (frameK tv envC f rest K₀) ch
        hks2 (by omega) (by omega) hbM' haT' hfr' (by omega) (by omega) henv1
      refine ⟨60, hitCells (na₁ + 1) bM ((k - 2 : Nat) : Int)
        ((fibW (k - 2) : Nat) : Int), na₁ + 1 + 5, by omega, by omega, ?_, ?_⟩
      · rw [show (g ++ [(Loc.base ⟨na₁⟩, u64c 0)]).set (.base ⟨na₁⟩)
              (u64c ((fibW (k - 2) : Nat) : Int))
            = g ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] from by
          rw [set_append_right (hfr na₁ (by omega)), set_singleton_self]] at hh
        exact hh
      · intro x hx
        rw [lookup_append_right (by
            rw [lookup_append_right (hfr x (by omega))]
            exact lookup_cons_ne (base_beq_false (by omega : na₁ ≠ x))),
          hitCells,
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 + 1 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 + 2 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 + 3 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na₁ + 1 + 4 ≠ x))]
        rfl
  obtain ⟨F₂, C, na₂, hF₂, hna₂, hrun₂, hfr₂⟩ := hcall2
  -- name the post-call-2 heap
  have hg2n : Heap.lookup ((g ++ [(Loc.base ⟨na₁⟩,
      u64c ((fibW (k - 2) : Nat) : Int))]) ++ C) (.base ⟨f⟩)
      = some (u64c (k : Int)) :=
    lookup_append_left (lookup_append_left hgn)
  have hg2m : Heap.lookup ((g ++ [(Loc.base ⟨na₁⟩,
      u64c ((fibW (k - 2) : Nat) : Int))]) ++ C) (.base ⟨f + 1⟩)
      = some (mapHc bM) :=
    lookup_append_left (lookup_append_left hgm)
  have hg2c0 : Heap.lookup ((g ++ [(Loc.base ⟨na₁⟩,
      u64c ((fibW (k - 2) : Nat) : Int))]) ++ C) (.base ⟨a0⟩)
      = some (u64c ((fibW (k - 1) : Nat) : Int)) :=
    lookup_append_left (lookup_append_left hga0)
  have hg2c1 : Heap.lookup ((g ++ [(Loc.base ⟨na₁⟩,
      u64c ((fibW (k - 2) : Nat) : Int))]) ++ C) (.base ⟨na₁⟩)
      = some (u64c ((fibW (k - 2) : Nat) : Int)) := by
    refine lookup_append_left ?_
    rw [lookup_append_right (hfr na₁ (by omega))]
    exact lookup_cons_self
  -- S8: r := $c0 + $c1
  have hS8 := fm_seg8 ((g ++ [(Loc.base ⟨na₁⟩,
      u64c ((fibW (k - 2) : Nat) : Int))]) ++ C) na₂ f a0 na₁
    ((fibW (k - 1) : Nat) : Int) ((fibW (k - 2) : Nat) : Int)
    tv envC rest K₀ ch hg2c0 hg2c1 (hfr₂ na₂ (by omega))
  have hsum : IntKind.normalize .uint64
      (((fibW (k - 1) : Nat) : Int) + ((fibW (k - 2) : Nat) : Int))
      = ((fibW k : Nat) : Int) := by
    rw [unorm_add_nat, ← fibW_rec hk2]
  rw [hsum] at hS8
  -- S9: memo[n] = r
  have hg3bM : Heap.lookup (((g ++ [(Loc.base ⟨na₁⟩,
      u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (.base ⟨bM⟩)
      = some (mapDc (mtbl (k - 1))) :=
    lookup_append_left (lookup_append_left (lookup_append_left hgbM))
  have hS9 := fm_seg9 (((g ++ [(Loc.base ⟨na₁⟩,
      u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (na₂ + 1)
    f bM a0 na₁ na₂ (k : Int) ((fibW k : Nat) : Int) (mtbl (k - 1)) (fibW k)
    tv envC rest K₀ ch
    (lookup_append_left hg2m)
    (lookup_append_left hg2n)
    (by
      rw [lookup_append_right (hfr₂ na₂ (by omega))]
      exact lookup_cons_self)
    hg3bM (unorm_nat_of_lt hk64) rfl (fibW_lt k)
  rw [setk_mtbl hk2] at hS9
  -- push the bM set into g
  have hshape₁ : Heap.set (((g ++ [(Loc.base ⟨na₁⟩,
        u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
        ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))])
      (.base ⟨bM⟩) (mapDc (mtbl k))
      = ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
          ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
          ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) := by
    rw [set_append_left (lookup_append_left (lookup_append_left hgbM)),
      set_append_left (lookup_append_left hgbM),
      set_append_left hgbM]
  rw [hshape₁] at hS9
  -- fresh-from for the set-g prefix
  have hfrG : ∀ x : Nat, na₂ ≤ x →
      Heap.lookup (((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
        ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
        (.base ⟨x⟩) = none := by
    intro x hx
    have h0 := hfr₂ x (by omega)
    rw [show ((g ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
        = (g ++ ([(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C))
      from by simp [List.append_assoc]] at h0
    rw [show (((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
          ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
        = ((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
          ++ ([(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C))
      from by simp [List.append_assoc]]
    cases hgx : Heap.lookup g (.base ⟨x⟩) with
    | some c =>
        exfalso
        have := lookup_append_left (h₂ := [(Loc.base ⟨na₁⟩,
          u64c ((fibW (k - 2) : Nat) : Int))] ++ C) hgx
        rw [this] at h0
        cases h0
    | none =>
        rw [lookup_append_right (by
          rw [lookup_set_other (by omega : bM ≠ x)]
          exact hgx)]
        rw [lookup_append_right hgx] at h0
        exact h0
  -- S10 on the set-g heap
  have hres10 : Heap.lookup ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
      ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (.base ⟨f + 2⟩)
      = some (u64c 0) := by
    refine lookup_append_left (lookup_append_left (lookup_append_left ?_))
    rw [lookup_set_other (by omega : bM ≠ f + 2)]
    exact hgres
  have hr10 : Heap.lookup ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
      ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (.base ⟨na₂⟩)
      = some (u64c ((fibW k : Nat) : Int)) := by
    rw [lookup_append_right (hfrG na₂ (by omega))]
    exact lookup_cons_self
  have hS10 := fm_seg10 ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
      ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (na₂ + 1)
    f a0 na₁ na₂ ((fibW k : Nat) : Int) 0
    tv envC rest K₀ ch hr10 hres10 (unorm_nat_of_lt (fibW_lt k))
  -- push the f+2 set into g as well
  have hshape₂ : Heap.set ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
        ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
        ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))])
      (.base ⟨f + 2⟩) (u64c ((fibW k : Nat) : Int))
      = (((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
          (u64c ((fibW k : Nat) : Int)))
          ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
          ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) := by
    have hin : Heap.lookup (g.set (.base ⟨bM⟩) (mapDc (mtbl k))) (.base ⟨f + 2⟩)
        = some (u64c 0) := by
      rw [lookup_set_other (by omega : bM ≠ f + 2)]
      exact hgres
    rw [set_append_left (lookup_append_left (lookup_append_left hin)),
      set_append_left (lookup_append_left hin),
      set_append_left hin]
  rw [hshape₂] at hS10
  -- the frame exit
  have hres2b : Heap.lookup (((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set
      (.base ⟨f + 2⟩) (u64c ((fibW k : Nat) : Int)))
      ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (.base ⟨f + 2⟩)
      = some (u64c ((fibW k : Nat) : Int)) := by
    refine lookup_append_left (lookup_append_left (lookup_append_left ?_))
    exact lookup_set_self
  have haT2b : Heap.lookup (((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set
      (.base ⟨f + 2⟩) (u64c ((fibW k : Nat) : Int)))
      ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (.base ⟨aT⟩)
      = some (u64c oldT) := by
    refine lookup_append_left (lookup_append_left (lookup_append_left ?_))
    rw [lookup_set_other (by omega : f + 2 ≠ aT),
      lookup_set_other hbMaT]
    exact hgaT
  have hS2b := fm_seg2b (((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set
      (.base ⟨f + 2⟩) (u64c ((fibW k : Nat) : Int)))
      ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) (na₂ + 1)
    f aT ((fibW k : Nat) : Int) oldT tv envC rest K₀ ch hres2b haT2b henvC
    (unorm_nat_of_lt (fibW_lt k))
  -- push the aT set into g
  have hshape₃ : Heap.set (((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set
        (.base ⟨f + 2⟩) (u64c ((fibW k : Nat) : Int)))
        ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
        ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))])
      (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int))
      = ((((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
          (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩)
          (u64c ((fibW k : Nat) : Int)))
          ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
          ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]) := by
    have hin : Heap.lookup ((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set
        (.base ⟨f + 2⟩) (u64c ((fibW k : Nat) : Int))) (.base ⟨aT⟩)
        = some (u64c oldT) := by
      rw [lookup_set_other (by omega : f + 2 ≠ aT),
        lookup_set_other hbMaT]
      exact hgaT
    rw [set_append_left (lookup_append_left (lookup_append_left hin)),
      set_append_left (lookup_append_left hin),
      set_append_left hin]
  rw [hshape₃] at hS2b
  -- assemble
  refine ⟨13 + F₂ + 17 + 8 + 14 + 6,
    ([(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C)
      ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))],
    na₂ + 1, by omega, by omega, ?_, ?_⟩
  · have hrun := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hS7 hrun₂) hS8) hS9) hS10) hS2b
    rw [show ((((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
          (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩)
          (u64c ((fibW k : Nat) : Int)))
          ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
          ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))])
        = (((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
          (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩)
          (u64c ((fibW k : Nat) : Int)))
          ++ (([(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C)
            ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))])
      from by simp [List.append_assoc]] at hrun
    exact hrun
  · intro x hx
    have h0 := hfrG x (by omega)
    rw [show (((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
          ++ [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))]) ++ C)
        = ((g.set (.base ⟨bM⟩) (mapDc (mtbl k)))
          ++ ([(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C))
      from by simp [List.append_assoc]] at h0
    rw [show ((((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
          (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩)
          (u64c ((fibW k : Nat) : Int)))
          ++ (([(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C)
            ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]))
        = (((g.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨f + 2⟩)
          (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩)
          (u64c ((fibW k : Nat) : Int)))
          ++ ([(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C)
          ++ [(Loc.base ⟨na₂⟩, u64c ((fibW k : Nat) : Int))]
      from by simp [List.append_assoc]]
    cases hgx : Heap.lookup (g.set (.base ⟨bM⟩) (mapDc (mtbl k))) (.base ⟨x⟩) with
    | some c =>
        exfalso
        have := lookup_append_left
          (h₂ := [(Loc.base ⟨na₁⟩, u64c ((fibW (k - 2) : Nat) : Int))] ++ C) hgx
        rw [this] at h0
        cases h0
    | none =>
        rw [lookup_append_right (by
          rw [lookup_append_right (by
            rw [lookup_set_other (by omega : aT ≠ x),
              lookup_set_other (by omega : f + 2 ≠ x)]
            exact hgx)]
          rw [lookup_append_right hgx] at h0
          exact h0)]
        rw [lookup_cons_ne (base_beq_false (by omega : na₂ ≠ x))]
        rfl
/-- Consecutive sets at the same key collapse. -/
theorem set_set {h : Heap} {l : Loc} {c₁ c₂ : HeapCell} :
    Heap.set (Heap.set h l c₁) l c₂ = Heap.set h l c₂ := by
  induction h with
  | nil => simp [Heap.set]
  | cons p rest ih =>
      obtain ⟨k, c₀⟩ := p
      cases hb : (k == l) with
      | true => simp [Heap.set, hb]
      | false => simp [Heap.set, hb, ih]

/-- Sets at distinct keys commute when the first key is PRESENT
(assoc-list heaps do not commute two absent-key appends). -/
theorem set_comm {h : Heap} {l₁ l₂ : Loc} {c₁ c₂ d₁ : HeapCell}
    (hne : l₁ ≠ l₂) (hp : Heap.lookup h l₁ = some d₁) :
    Heap.set (Heap.set h l₁ c₁) l₂ c₂ = Heap.set (Heap.set h l₂ c₂) l₁ c₁ := by
  induction h with
  | nil => cases hp
  | cons pr rest ih =>
      obtain ⟨kk, c₀⟩ := pr
      by_cases h1 : (kk == l₁) = true
      · have h2 : (kk == l₂) = false := by
          have hk : kk = l₁ := by simpa using h1
          subst hk
          simpa using hne
        simp [Heap.set, h1, h2]
      · simp only [Bool.not_eq_true] at h1
        by_cases h2 : (kk == l₂) = true
        · simp [Heap.set, h1, h2]
        · simp only [Bool.not_eq_true] at h2
          have hp' : Heap.lookup rest l₁ = some d₁ := by
            simpa [Heap.lookup, h1] using hp
          simp [Heap.set, h1, h2, ih hp']

/-- **The BUILD call span** (`1 ≤ j < k`, memo `mtbl j`): the memoized
recursion computes and stores every key up to `k`; the caller's target
cell receives `fibW k`, the memo becomes `mtbl k`. Strong induction on
`k` — the continuation-stack-parametric induction this unit exists
for. Fuel: `≤ 170·k + 32`. -/
theorem fmCall_build : ∀ (k : Nat), 2 ≤ k → k < 2 ^ 64 →
    ∀ (j : Nat) (h : Heap) (na bM aT : Nat) (oldT : Int)
      (tv : String) (envC : LocalEnv) (rest : List Stmt) (K₀ : Cont)
      (ch : Choices),
    1 ≤ j → j < k →
    Heap.lookup h (.base ⟨bM⟩) = some (mapDc (mtbl j)) →
    Heap.lookup h (.base ⟨aT⟩) = some (u64c oldT) →
    FreshFrom h na → bM < na → aT < na →
    LocalEnv.lookup envC tv = some (.base ⟨aT⟩) →
    ∃ (F : Nat) (junk : Heap) (na' : Nat),
      F ≤ 170 * k + 32 ∧ na + 8 ≤ na' ∧
      stepFnIter F (fmSt h na)
        (.retV (mapHv bM)
          (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref tv])]
            [.int (k : Int) .uint64] [] envC (.seq rest envC K₀))) ch
      = .ok (.next (.seq rest envC K₀),
          fmSt (((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩)
              (u64c ((fibW k : Nat) : Int))) ++ junk) na', ch)
      ∧ FreshFrom (((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩)
          (u64c ((fibW k : Nat) : Int))) ++ junk) na' := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
  intro hk2 hk64 j h na bM aT oldT tv envC rest K₀ ch hj1 hjk hbM haT hfr
    hbMlt haTlt henvC
  -- === the shared miss prefix: 39 steps to `.next (kMain na KT)` ===
  have hEnter := stepFnIter_one (stepFn_call_enter
    (σ := fmSt h na) (fid := ⟨"fibMemo"⟩) (v := mapHv bM)
    (vals := [.int (k : Int) .uint64])
    (plans := [(.chain [], [.ref tv])]) (env := envC)
    (k := .seq rest envC K₀) (ch := ch)
    (fm_enterFrame h na k bM hk64 hfr))
  have hfr₁ : FreshFrom (h ++ frameCells na bM (k : Int) 0) (na + 3) := by
    intro x hx
    rw [lookup_append_right (hfr x (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x))]
    rfl
  have hn₁ : Heap.lookup (h ++ frameCells na bM (k : Int) 0) (.base ⟨na⟩)
      = some (u64c (k : Int)) := by
    rw [lookup_append_right (hfr na (by omega)), frameCells]
    exact lookup_cons_self
  have hS1 := fm_seg1 (h ++ frameCells na bM (k : Int) 0) (na + 3) na (k : Int)
    tv envC rest K₀ ch hn₁
  rw [show (decide ((k : Int) < 2)) = false from by
    simp only [decide_eq_false_iff_not]
    intro hc
    have hlt : k < 2 := by exact_mod_cast hc
    omega] at hS1
  have hS3a := fm_seg3a (h ++ frameCells na bM (k : Int) 0) na tv envC rest K₀
    ch hfr₁
  have hmem₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
      (.base ⟨na + 1⟩) = some (mapHc bM) := by
    refine lookup_append_left ?_
    rw [lookup_append_right (hfr (na + 1) (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    exact lookup_cons_self
  have hn₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
      (.base ⟨na⟩) = some (u64c (k : Int)) := lookup_append_left hn₁
  have hS3b := fm_seg3b ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
    (na + 5) na bM (k : Int) (frameK tv envC na rest K₀) ch hmem₂ hn₂
  have hmap₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
      (.base ⟨bM⟩) = some (mapDc (mtbl j)) :=
    lookup_append_left (lookup_append_left hbM)
  have hDrain := stepFnIter_one (fm_lookup_drain_miss
    (σ := fmSt ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (na + 5))
    (f := na) (bM := bM) (kv := (k : Int)) (M := mtbl j)
    (KT := frameK tv envC na rest K₀) (ch := ch)
    hmap₂ (unorm_nat_of_lt hk64) (idxOf?_mtbl_none hjk))
  have hv₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
      (.base ⟨na + 3⟩) = some (u64c 0) := by
    rw [lookup_append_right (hfr₁ (na + 3) (by omega))]
    exact lookup_cons_self
  have hok₂ : Heap.lookup (((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set
      (.base ⟨na + 3⟩) (u64c 0)) (.base ⟨na + 4⟩) = some (bc false) := by
    rw [lookup_set_other (by omega : na + 3 ≠ na + 4),
      lookup_append_right (hfr₁ (na + 4) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
    exact lookup_cons_self
  have hS3c := fm_seg3c ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
    (na + 5) na 0 false (frameK tv envC na rest K₀) ch hv₂ hok₂
    (by with_unfolding_all rfl)
  -- the S3c sets are no-ops
  have hnoop : (((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]).set
      (.base ⟨na + 3⟩) (u64c 0)).set (.base ⟨na + 4⟩) (bc false)
      = ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) := by
    rw [set_self_of_lookup hv₂, set_self_of_lookup (by
      rw [lookup_append_right (hfr₁ (na + 4) (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
      exact lookup_cons_self)]
  rw [hnoop] at hS3c
  have hS3d := fm_seg3d ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
    (na + 5) na false (frameK tv envC na rest K₀) ch (by
      rw [lookup_append_right (hfr₁ (na + 4) (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
      exact lookup_cons_self)
  have hS5 := fm_seg5 ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
    (na + 5) na (frameK tv envC na rest K₀) ch
  -- S6 (the H2 shorthand is spelled out; frame base f = na)
  have hn₅ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
      (.base ⟨na⟩) = some (u64c (k : Int)) := hn₂
  have hfr₂' : FreshFrom ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
      (na + 5) := by
    intro x hx
    rw [lookup_append_right (hfr₁ x (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x))]
    rfl
  have hS6 := fm_seg6 ((h ++ frameCells na bM (k : Int) 0)
      ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
    (na + 5) na bM (k : Int) tv envC rest K₀ ch hn₅ hmem₂
    (hfr₂' (na + 5) (by omega))
  have harg1 : IntKind.normalize .uint64 ((k : Int) - 1)
      = ((k - 1 : Nat) : Int) := by
    rw [show (k : Int) - 1 = ((k - 1 : Nat) : Int) from by omega]
    exact unorm_nat_of_lt (by omega)
  rw [harg1] at hS6
  -- the 39+13 step prefix
  have hPre := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain hEnter hS1) hS3a) hS3b) hDrain)
      hS3c) hS3d) hS5) hS6
  -- === call 1: the unified post-state ===
  have hfr₆ : FreshFrom (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (na + 6) := by
    intro x hx
    rw [lookup_append_right (hfr₂' x (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ x))]
    rfl
  have hbM₆ : Heap.lookup (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (.base ⟨bM⟩) = some (mapDc (mtbl j)) :=
    lookup_append_left hmap₂
  have ha5₆ : Heap.lookup (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (.base ⟨na + 5⟩) = some (u64c 0) := by
    rw [lookup_append_right (hfr₂' (na + 5) (by omega))]
    exact lookup_cons_self
  have henv₆ : LocalEnv.lookup (uEnvC0 na (na + 5)) "$c0"
      = some (Loc.base ⟨na + 5⟩) := rfl
  obtain ⟨F₁, D, na₁, hF₁, hna₁, hrun₁, hfrHP⟩ :
      ∃ (F₁ : Nat) (D : Heap) (na₁ : Nat),
        F₁ ≤ 170 * (k - 1) + 32 ∧ na + 7 ≤ na₁ ∧
        stepFnIter F₁ (fmSt (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (na + 6))
          (.retV (mapHv bM)
            (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c0"])]
              [.int ((k - 1 : Nat) : Int) .uint64] [] (uEnvC0 na (na + 5))
              (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
                (uEnvC0 na (na + 5)) (frameK tv envC na rest K₀)))) ch
        = .ok (.next (.seq [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
              (uEnvC0 na (na + 5)) (frameK tv envC na rest K₀)),
            fmSt ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) na₁, ch)
        ∧ FreshFrom ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) na₁ := by
    by_cases hks : k - 1 ≤ 1
    · -- k = 2: the base sub-call; j = 1 = k − 1
      have hj : j = k - 1 := by omega
      have hself : (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1))) = (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) := by
        rw [← hj]
        exact set_self_of_lookup hbM₆
      have hb := fmCall_base (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (na + 6) bM (na + 5) (k - 1) 0 "$c0"
        (uEnvC0 na (na + 5)) [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
        (frameK tv envC na rest K₀) ch hks ha5₆ hfr₆ (by omega) henv₆
      refine ⟨32, frameCells (na + 6) bM ((k - 1 : Nat) : Int)
        ((k - 1 : Nat) : Int), na + 6 + 3, by omega, by omega, ?_, ?_⟩
      · rw [show (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) = (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int)) from by rw [hself],
          show (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))
            = ((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) from rfl]
        exact hb
      · rw [show (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) = (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int)) from by rw [hself]]
        intro x hx
        rw [lookup_append_right (by
          rw [lookup_set_other (by omega : na + 5 ≠ x)]
          exact hfr₆ x (by omega)), frameCells,
          lookup_cons_ne (base_beq_false (by omega : na + 6 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na + 6 + 1 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na + 6 + 2 ≠ x))]
        rfl
    · by_cases hjk1 : j = k - 1
      · -- the memo already holds k−1: the hit sub-call
        have hks2 : 2 ≤ k - 1 := by omega
        have hself : (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1))) = (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) := by
          rw [← hjk1]
          exact set_self_of_lookup hbM₆
        have hbM₆' : Heap.lookup (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (.base ⟨bM⟩)
            = some (mapDc (mtbl (k - 1))) := by
          rw [← hjk1]
          exact hbM₆
        have hh := fmCall_hit (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (na + 6) bM (na + 5) (k - 1) (k - 1) 0 "$c0"
          (uEnvC0 na (na + 5)) [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
          (frameK tv envC na rest K₀) ch hks2 (by omega) (by omega)
          hbM₆' ha5₆ hfr₆ (by omega) (by omega) henv₆
        refine ⟨60, hitCells (na + 6) bM ((k - 1 : Nat) : Int)
          ((fibW (k - 1) : Nat) : Int), na + 6 + 5, by omega, by omega, ?_, ?_⟩
        · rw [show (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) = (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int)) from by rw [hself]]
          exact hh
        · rw [show (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) = (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int)) from by rw [hself]]
          intro x hx
          rw [lookup_append_right (by
            rw [lookup_set_other (by omega : na + 5 ≠ x)]
            exact hfr₆ x (by omega)), hitCells,
            lookup_cons_ne (base_beq_false (by omega : na + 6 ≠ x)),
            lookup_cons_ne (base_beq_false (by omega : na + 6 + 1 ≠ x)),
            lookup_cons_ne (base_beq_false (by omega : na + 6 + 2 ≠ x)),
            lookup_cons_ne (base_beq_false (by omega : na + 6 + 3 ≠ x)),
            lookup_cons_ne (base_beq_false (by omega : na + 6 + 4 ≠ x))]
          rfl
      · -- the genuinely recursive sub-call
        have hk3 : 2 ≤ k - 1 := by omega
        obtain ⟨F₁, junk₁, na₁, hF₁, hna₁, hrun₁, hfr₁'⟩ :=
          IH (k - 1) (by omega) hk3 (by omega) j (((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]) (na + 6) bM (na + 5) 0
            "$c0" (uEnvC0 na (na + 5)) [fmC1Seqn, fmRSeqn, fmMapAsgn, fmRetSeqn]
            (frameK tv envC na rest K₀) ch hj1 (by omega) hbM₆ ha5₆ hfr₆
            (by omega) (by omega) henv₆
        exact ⟨F₁, junk₁, na₁, hF₁, by omega, hrun₁, hfr₁'⟩
  have hbMaT : bM ≠ aT := by
    intro he
    rw [he] at hbM
    rw [hbM] at haT
    simp [mapDc, u64c] at haT
  -- tail hypotheses on (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D
  have hHPn : Heap.lookup ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) (.base ⟨na⟩) = some (u64c (k : Int)) := by
    refine lookup_append_left ?_
    rw [lookup_set_other (by omega : na + 5 ≠ na),
      lookup_set_other (by omega : bM ≠ na)]
    exact lookup_append_left hn₂
  have hHPm : Heap.lookup ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) (.base ⟨na + 1⟩) = some (mapHc bM) := by
    refine lookup_append_left ?_
    rw [lookup_set_other (by omega : na + 5 ≠ na + 1),
      lookup_set_other (by omega : bM ≠ na + 1)]
    exact lookup_append_left hmem₂
  have hres₂ : Heap.lookup ((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) (.base ⟨na + 2⟩) = some (u64c 0) := by
    refine lookup_append_left ?_
    rw [lookup_append_right (hfr (na + 2) (by omega)), frameCells,
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
    exact lookup_cons_self
  have hHPres : Heap.lookup ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) (.base ⟨na + 2⟩) = some (u64c 0) := by
    refine lookup_append_left ?_
    rw [lookup_set_other (by omega : na + 5 ≠ na + 2),
      lookup_set_other (by omega : bM ≠ na + 2)]
    exact lookup_append_left hres₂
  have hHPbM : Heap.lookup ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) (.base ⟨bM⟩)
      = some (mapDc (mtbl (k - 1))) := by
    refine lookup_append_left ?_
    rw [lookup_set_other (by omega : na + 5 ≠ bM)]
    exact lookup_set_self
  have hHPa0 : Heap.lookup ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) (.base ⟨na + 5⟩)
      = some (u64c ((fibW (k - 1) : Nat) : Int)) := by
    refine lookup_append_left ?_
    exact lookup_set_self
  have hHPaT : Heap.lookup ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) (.base ⟨aT⟩) = some (u64c oldT) := by
    refine lookup_append_left ?_
    rw [lookup_set_other (by omega : na + 5 ≠ aT),
      lookup_set_other hbMaT]
    exact lookup_append_left (lookup_append_left (lookup_append_left haT))
  -- === the tail ===
  obtain ⟨F₂, junkT, na₂, hF₂, hna₂, hrunT, hfrT⟩ :=
    fmBuild_tail ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D) na₁ na bM aT (na + 5) k oldT tv envC rest K₀ ch
      hk2 hk64 hHPn hHPm hHPres hHPbM hHPa0 hHPaT hfrHP
      (by omega) (by omega) (by omega) (by omega) henvC
  -- === the final heap shape ===
  have hpush : ((((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D).set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨na + 2⟩)
        (u64c ((fibW k : Nat) : Int))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int))
      = (((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
        ++ ([(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))]
            ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false),
                (Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))] ++ D)) := by
    -- step 1: the bM set collapses into the prefix and lands in h
    have hp1 : ((((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) ++ D).set (.base ⟨bM⟩) (mapDc (mtbl k)) = ((((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))]) ++ D := by
      rw [set_append_left (by
        rw [lookup_set_other (by omega : na + 5 ≠ bM)]
        exact lookup_set_self : Heap.lookup (((((h ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, u64c 0)]).set (.base ⟨bM⟩) (mapDc (mtbl (k - 1)))).set (.base ⟨na + 5⟩) (u64c ((fibW (k - 1) : Nat) : Int))) (.base ⟨bM⟩)
          = some (mapDc (mtbl (k - 1))))]
      congr 1
      rw [set_comm (by
          simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
          omega : (Loc.base ⟨na + 5⟩ : Loc) ≠ .base ⟨bM⟩)
        (by
          rw [lookup_set_other (by omega : bM ≠ na + 5)]
          rw [lookup_append_right (hfr₂' (na + 5) (by omega))]
          exact lookup_cons_self), set_set]
      rw [set_append_left (by
          exact lookup_append_left (lookup_append_left hbM)
        : Heap.lookup ((h ++ frameCells na bM (k : Int) 0)
            ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)])
            (.base ⟨bM⟩) = some (mapDc (mtbl j)))]
      rw [set_append_left (lookup_append_left hbM),
        set_append_left hbM]
      rw [set_append_right (by
        rw [lookup_append_right (by
          rw [lookup_append_right (by
            rw [lookup_set_other (by omega : bM ≠ na + 5)]
            exact hfr (na + 5) (by omega))]
          rw [frameCells,
            lookup_cons_ne (base_beq_false (by omega : na ≠ na + 5)),
            lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 5)),
            lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 5))]
          rfl)]
        rw [lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 5)),
          lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 5))]
        rfl), set_singleton_self]
    rw [hp1]
    -- step 2: the na+2 set lands in the frame cells
    have hEna2 : Heap.lookup ((((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))]) (.base ⟨na + 2⟩) = some (u64c 0) := by
      refine lookup_append_left (lookup_append_left ?_)
      rw [lookup_append_right (by
        rw [lookup_set_other (by omega : bM ≠ na + 2)]
        exact hfr (na + 2) (by omega)), frameCells,
        lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
      exact lookup_cons_self
    have hp2 : (((((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ frameCells na bM (k : Int) 0) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))]) ++ D).set (.base ⟨na + 2⟩) (u64c ((fibW k : Nat) : Int)) = ((((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ [(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))]) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))]) ++ D := by
      rw [set_append_left hEna2]
      congr 1
      rw [set_append_left (lookup_append_left (by
        rw [lookup_append_right (by
          rw [lookup_set_other (by omega : bM ≠ na + 2)]
          exact hfr (na + 2) (by omega)), frameCells,
          lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
        exact lookup_cons_self
        : Heap.lookup ((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ frameCells na bM (k : Int) 0) (.base ⟨na + 2⟩)
          = some (u64c 0)))]
      congr 1
      rw [set_append_left (by
        rw [lookup_append_right (by
          rw [lookup_set_other (by omega : bM ≠ na + 2)]
          exact hfr (na + 2) (by omega)), frameCells,
          lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
        exact lookup_cons_self
        : Heap.lookup ((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ frameCells na bM (k : Int) 0) (.base ⟨na + 2⟩)
          = some (u64c 0))]
      congr 1
      rw [set_append_right (by
        rw [lookup_set_other (by omega : bM ≠ na + 2)]
        exact hfr (na + 2) (by omega))]
      congr 1
      rw [frameCells,
        set_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
        set_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2)),
        set_cons_self]
    rw [hp2]
    -- step 3: the aT set lands in h
    have hEaT : Heap.lookup ((((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ [(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))]) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))]) (.base ⟨aT⟩) = some (u64c oldT) := by
      refine lookup_append_left (lookup_append_left (lookup_append_left ?_))
      rw [lookup_set_other hbMaT]
      exact haT
    have hp3 : (((((h.set (.base ⟨bM⟩) (mapDc (mtbl k))) ++ [(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))]) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))]) ++ D).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)) = (((((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int))) ++ [(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))]) ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false)]) ++ [(Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))]) ++ D := by
      rw [set_append_left hEaT]
      congr 1
      have hin : Heap.lookup (h.set (.base ⟨bM⟩) (mapDc (mtbl k))) (.base ⟨aT⟩) = some (u64c oldT) := by
        rw [lookup_set_other hbMaT]
        exact haT
      rw [set_append_left (lookup_append_left (lookup_append_left hin)),
        set_append_left (lookup_append_left hin),
        set_append_left hin]
    rw [hp3]
    simp [List.append_assoc]
  -- === assemble ===
  have hrunFull := stepFnIter_chain (stepFnIter_chain hPre hrun₁) hrunT
  rw [hpush] at hrunFull hfrT
  refine ⟨(1 + 8 + 11 + 8 + 1 + 2 + 5 + 3 + 13) + F₁ + F₂,
    ([(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))] ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false),
        (Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))] ++ D) ++ junkT,
    na₂, by omega, by omega, ?_, ?_⟩
  · rw [show ((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
        ++ (([(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))] ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false),
            (Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))] ++ D) ++ junkT)
        = (((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
          ++ ([(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))] ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false),
              (Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))] ++ D)) ++ junkT from by
      simp [List.append_assoc]]
    exact hrunFull
  · rw [show ((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
        ++ (([(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))] ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false),
            (Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))] ++ D) ++ junkT)
        = (((h.set (.base ⟨bM⟩) (mapDc (mtbl k))).set (.base ⟨aT⟩) (u64c ((fibW k : Nat) : Int)))
          ++ ([(Loc.base ⟨na⟩, u64c (k : Int)), (Loc.base ⟨na + 1⟩, mapHc bM), (Loc.base ⟨na + 2⟩, (u64c ((fibW k : Nat) : Int)))] ++ [(Loc.base ⟨na + 3⟩, u64c 0), (Loc.base ⟨na + 4⟩, bc false),
              (Loc.base ⟨na + 5⟩, (u64c ((fibW (k - 1) : Nat) : Int)))] ++ D)) ++ junkT from by
      simp [List.append_assoc]]
    exact hfrT

end GoLean.Examples.FibMemo
