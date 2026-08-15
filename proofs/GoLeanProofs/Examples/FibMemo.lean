import GoLeanProofs.Examples.FibMemoProgram
import GoLeanProofs.Examples.FibMemo.Rec
import GoLeanProofs.EntryEq
import GoLeanProofs.FuelMeasure

/-!
# FibMemo — recursive Fibonacci over a live memo table (Gallery
Campaign G1, HARD LANE)

THE HEADLINE (`fibmemo_ok`, below) is stated HERE, in the root, so the
aggregator's `import GoLeanProofs.Examples.FibMemo` reaches it by name
(the C-H4/C-H5 shape). The example is the gallery's FIRST RECURSIVE
subject: `fibMemo` calls itself twice under a `map[uint64]uint64` memo
read with the comma-ok form, so the machine run carries a genuine
continuation STACK and a heap that interleaves live frames with the
dead cells of completed sub-calls. The recursion machinery — the
continuation-stack-parametric induction `fmCall_build` and its
base/hit companions — lives in `Examples/FibMemo/Rec.lean`; the
statement-side spec vocabulary (`fibSpec` — imported from the `fib`
example's designated module so the gallery's "Fibonacci" means one
thing — and the wrapped `fibW`) in `Examples/FibMemo/Pure.lean`.

Go source: `Corpus/coverage/exec/examples/fibmemo/main.go` (10 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/fibmemo-lowered.repr`.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `fibmemoHarnessFunc_pin` checks a transcription that is
byte-derived from the lowering (the guardrails wave's shape, kept).
-/

namespace GoLean.Examples.FibMemo

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def fibmemoHarnessFunc : Func :=
{ id := { key := "fibmemo_harness" },
  args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c5", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c5"]
                    { key := "fib" }
                    #[GoLean.GoCore.Expr.var "n"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "$c5"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem fibmemoHarnessFunc_pin :
    findFunctionIn? fibmemoLowered.funcs ⟨"fibmemo_harness"⟩
    = some fibmemoHarnessFunc := rfl

open GoLean.GoCore.Machine GoLean.Surface GoLean.SliceMem GoLean.MapMem
open GoLean.Examples.Fib (fibSpec)

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The subject `fib` wrapper, verbatim, pinned. -/
theorem fibFunc_pin :
    (findFunctionIn? fibmemoLowered.funcs ⟨"fib"⟩).isSome = true := rfl

derive_entry_eq fm_entry_eq fibmemoLowered fibmemoHarnessFunc fmSeed fmC0

/-! ## The entry side (concrete heap; raw segments) -/

/-- fib's frame env. -/
private def fibEnv : LocalEnv :=
  [[("$c3", .base ⟨8⟩), ("memo", .base ⟨7⟩), ("$c2", .base ⟨5⟩)],
   [("$res0", .base ⟨4⟩), ("n", .base ⟨3⟩)]]

/-- the harness env. -/
private def hEnv : LocalEnv :=
  [[("$c5", .base ⟨2⟩)], [("$res0", .base ⟨1⟩), ("n", .base ⟨0⟩)]]

/-- fib's return continuation (the harness frame). -/
private def kFib : Cont :=
  .frame [(.chain [], [.ref "$c5"])] hEnv [.base ⟨4⟩] []
    (.seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]] hEnv
      (.frame [] [] [] [] .stop false)) false

/-- the fib epilogue statement. -/
private abbrev fibEpi : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c3"), .returnStmt]

/-- The concrete 9-cell heap at the `fibMemo(n, memo)` call point
(`nv0` the harness argument cell, `nv3` fib's normalized copy). -/
private def h9 (nv0 nv3 : Int) : Heap :=
  [(Loc.base ⟨0⟩, u64c nv0), (Loc.base ⟨1⟩, u64c 0), (Loc.base ⟨2⟩, u64c 0),
   (Loc.base ⟨3⟩, u64c nv3), (Loc.base ⟨4⟩, u64c 0), (Loc.base ⟨5⟩, mapHc 6),
   (Loc.base ⟨6⟩, mapDc []), (Loc.base ⟨7⟩, mapHc 6), (Loc.base ⟨8⟩, u64c 0)]

/-- E0 — machine entry → the top-level `fibMemo` call's last argument
delivery. 40 steps; everything concrete but the argument value. -/
private theorem fm_seg_entry (n : Nat) (hn : n < 2 ^ 64) (ch : Choices) :
    stepFnIter 40 (fmSeed (n : Int)) fmC0 ch
      = .ok (.retV (mapHv 6)
            (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c3"])]
              [.int (n : Int) .uint64] [] fibEnv (.seq [fibEpi] fibEnv kFib)),
          fmSt (h9 (n : Int) (n : Int)) 9, ch) := by
  have hraw : stepFnIter 40 (fmSeed (n : Int)) fmC0 ch
      = .ok (.retV (mapHv 6)
            (.callArgsK ⟨"fibMemo"⟩ [(.chain [], [.ref "$c3"])]
              [.int (IntKind.normalize .uint64 (n : Int)) .uint64] []
              fibEnv (.seq [fibEpi] fibEnv kFib)),
          fmSt (h9 (n : Int) (IntKind.normalize .uint64 (n : Int))) 9, ch) := by
    with_unfolding_all rfl
  rw [unorm_nat_of_lt hn] at hraw
  exact hraw

/-- Freshness of the 9-cell entry heap. -/
private theorem h9_fresh (nv0 nv3 : Int) : FreshFrom (h9 nv0 nv3) 9 := by
  intro x hx
  simp only [h9]
  rw [
    lookup_cons_ne (base_beq_false (by omega : 0 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 3 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 4 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 5 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 6 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 7 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 8 ≠ x))]
  rfl

/-! ## The tail: fib's epilogue and the harness exit (footprint style) -/

/-- The tail — from the caller's resumption after the top-level call to
the machine terminal. 35 steps; reads `$c3` at 8, threads the result
through `$res0`@4, `$c5`@2 and the harness `$res0`@1. -/
private theorem fm_seg_tail (h : Heap) (na : Nat) (rv : Int)
    (o4 o2 o1 : Int) (ch : Choices)
    (h8 : Heap.lookup h (.base ⟨8⟩) = some (u64c rv))
    (h4 : Heap.lookup h (.base ⟨4⟩) = some (u64c o4))
    (h2 : Heap.lookup (h.set (.base ⟨4⟩) (u64c rv)) (.base ⟨2⟩)
      = some (u64c o2))
    (h1 : Heap.lookup ((h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩)
        (u64c rv)) (.base ⟨1⟩) = some (u64c o1))
    (hrv : IntKind.normalize .uint64 rv = rv) :
    stepFnIter 35 (fmSt h na) (.next (.seq [fibEpi] fibEnv kFib)) ch
      = .ok (.next .stop,
          fmSt (((h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩)
              (u64c rv)).set (.base ⟨1⟩) (u64c rv)) na, ch) := by
  show stepFnIter (2 + 1 + 3 + 1 + 1 + 1 + 5 + 1 + 1 + 1 + 1 + 8 + 1 + 1
    + 1 + 6) _ _ _ = _
  -- pop + splice (concrete env: plain rfl)
  have hA : stepFnIter 2 (fmSt h na) (.next (.seq [fibEpi] fibEnv kFib)) ch
      = .ok (.next (.seq [.assign (.var "$res0") (.var "$c3"), .returnStmt]
            fibEnv kFib),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hB : stepFnIter 1 (fmSt h na)
      (.next (.seq [.assign (.var "$res0") (.var "$c3"), .returnStmt]
        fibEnv kFib)) ch
      = .ok (.exec (.assign (.var "$res0") (.var "$c3")) fibEnv
            (.seq [.returnStmt] fibEnv kFib),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hC : stepFnIter 3 (fmSt h na)
      (.exec (.assign (.var "$res0") (.var "$c3")) fibEnv
        (.seq [.returnStmt] fibEnv kFib)) ch
      = .ok (.evalE (.var "$c3") fibEnv
          (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
            (.seqn #[]) fibEnv (.seq [.returnStmt] fibEnv kFib)),
        fmSt h na, ch) := by
    with_unfolding_all rfl
  have hD := stepFnIter_one (stepFn_var (σ := fmSt h na)
    (x := "$c3") (env := fibEnv) (a := ⟨8⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
      (.seqn #[]) fibEnv (.seq [.returnStmt] fibEnv kFib))
    (ch := ch) (c := u64c rv) rfl h8)
  have hE : stepFnIter 1 (fmSt h na)
      (.retV (.int rv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
          (.seqn #[]) fibEnv (.seq [.returnStmt] fibEnv kFib))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨4⟩)) [] []]
            [.int rv .uint64] (.seqn #[]) fibEnv
            (.seq [.returnStmt] fibEnv kFib)),
          fmSt h na, ch) := by
    with_unfolding_all rfl
  have hF := stepFnIter_one (stepFn_store_step (σ := fmSt h na)
    (σ' := { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) })
    (r := .chain (.addr (.base ⟨4⟩)) [] []) (val := .int rv .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := fibEnv)
    (k := .seq [.returnStmt] fibEnv kFib) (ch := ch)
    (storeTarget_addr h4 (by
      show normalizeValueForTy (fmSt h na) tU (.int rv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        hrv])))
  -- drain to the fib frame, exit-store into `$c5`@2
  have hG : stepFnIter 5
      { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }
      (.next (.storeK [] [] (.seqn #[]) fibEnv
        (.seq [.returnStmt] fibEnv kFib))) ch
      = .ok (.returning kFib,
          { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }, ch) := by
    with_unfolding_all rfl
  have hH : stepFn { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }
      (.returning kFib) ch
      = .ok (.evalE (.ref "$c5") hEnv
          (.tgtOpK (.chain []) [] [] [] [] .vals [] [.int rv .uint64]
            (.seqn #[]) hEnv
            (.seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]]
              hEnv (.frame [] [] [] [] .stop false))),
        { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }, ch) := by
    simp only [stepFn, kFib, loadMany, loadLoc, lookup_set_self,
      Bind.bind, Except.bind, pure, Except.pure]
  have hH' := stepFnIter_one hH
  have hI : stepFnIter 1
      { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }
      (.evalE (.ref "$c5") hEnv
        (.tgtOpK (.chain []) [] [] [] [] .vals [] [.int rv .uint64]
          (.seqn #[]) hEnv
          (.seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]]
            hEnv (.frame [] [] [] [] .stop false)))) ch
      = .ok (.retV (.addr (.base ⟨2⟩))
          (.tgtOpK (.chain []) [] [] [] [] .vals [] [.int rv .uint64]
            (.seqn #[]) hEnv
            (.seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]]
              hEnv (.frame [] [] [] [] .stop false))),
        { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }, ch) := by
    with_unfolding_all rfl
  have hJ : stepFnIter 1
      { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }
      (.retV (.addr (.base ⟨2⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals [] [.int rv .uint64]
          (.seqn #[]) hEnv
          (.seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]]
            hEnv (.frame [] [] [] [] .stop false)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨2⟩)) [] []]
            [.int rv .uint64] (.seqn #[]) hEnv
            (.seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]]
              hEnv (.frame [] [] [] [] .stop false))),
          { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) }, ch) := by
    with_unfolding_all rfl
  have hK := stepFnIter_one (stepFn_store_step
    (σ := { fmSt h na with heap := h.set (.base ⟨4⟩) (u64c rv) })
    (σ' := { fmSt h na with
      heap := (h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩) (u64c rv) })
    (r := .chain (.addr (.base ⟨2⟩)) [] []) (val := .int rv .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := hEnv)
    (k := .seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]]
      hEnv (.frame [] [] [] [] .stop false)) (ch := ch)
    (storeTarget_addr h2 (by
      show normalizeValueForTy _ tU (.int rv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        hrv])))
  -- the harness epilogue: `$res0`@1 := `$c5`
  have hL : stepFnIter 8
      { fmSt h na with
        heap := (h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩) (u64c rv) }
      (.next (.storeK [] [] (.seqn #[]) hEnv
        (.seq [.seqn #[.assign (.var "$res0") (.var "$c5"), .returnStmt]]
          hEnv (.frame [] [] [] [] .stop false)))) ch
      = .ok (.evalE (.var "$c5") hEnv
          (.rhsK .vals [.chain (.addr (.base ⟨1⟩)) [] []] [] []
            (.seqn #[]) hEnv
            (.seq [.returnStmt] hEnv (.frame [] [] [] [] .stop false))),
        { fmSt h na with
          heap := (h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩) (u64c rv) },
        ch) := by
    with_unfolding_all rfl
  have hM := stepFnIter_one (stepFn_var
    (σ := { fmSt h na with
      heap := (h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩) (u64c rv) })
    (x := "$c5") (env := hEnv) (a := ⟨2⟩)
    (k := .rhsK .vals [.chain (.addr (.base ⟨1⟩)) [] []] [] []
      (.seqn #[]) hEnv
      (.seq [.returnStmt] hEnv (.frame [] [] [] [] .stop false)))
    (ch := ch) (c := u64c rv) rfl lookup_set_self)
  have hN : stepFnIter 1
      { fmSt h na with
        heap := (h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩) (u64c rv) }
      (.retV (.int rv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨1⟩)) [] []] [] []
          (.seqn #[]) hEnv
          (.seq [.returnStmt] hEnv (.frame [] [] [] [] .stop false)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨1⟩)) [] []]
            [.int rv .uint64] (.seqn #[]) hEnv
            (.seq [.returnStmt] hEnv (.frame [] [] [] [] .stop false))),
          { fmSt h na with
            heap := (h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩) (u64c rv) },
          ch) := by
    with_unfolding_all rfl
  have hO := stepFnIter_one (stepFn_store_step
    (σ := { fmSt h na with
      heap := (h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩) (u64c rv) })
    (σ' := { fmSt h na with
      heap := ((h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩)
        (u64c rv)).set (.base ⟨1⟩) (u64c rv) })
    (r := .chain (.addr (.base ⟨1⟩)) [] []) (val := .int rv .uint64)
    (rs := []) (vs := []) (body := .seqn #[]) (env := hEnv)
    (k := .seq [.returnStmt] hEnv (.frame [] [] [] [] .stop false))
    (ch := ch)
    (storeTarget_addr h1 (by
      show normalizeValueForTy _ tU (.int rv .uint64) = _
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        hrv])))
  have hP : stepFnIter 6
      { fmSt h na with
        heap := ((h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩)
          (u64c rv)).set (.base ⟨1⟩) (u64c rv) }
      (.next (.storeK [] [] (.seqn #[]) hEnv
        (.seq [.returnStmt] hEnv (.frame [] [] [] [] .stop false)))) ch
      = .ok (.next .stop,
          { fmSt h na with
            heap := ((h.set (.base ⟨4⟩) (u64c rv)).set (.base ⟨2⟩)
              (u64c rv)).set (.base ⟨1⟩) (u64c rv) }, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hB) hC) hD) hE) hF) hG) hH') hI) hJ) hK) hL) hM) hN) hO) hP

/-! ## The end-to-end run and the headline -/

/-- **The run, end to end**: from the machine entry's post-prelude seed
the harness reaches the entry terminal within `170·n + 107` steps, with
`fibW n` in the harness result cell. -/
private theorem fm_runs (n : Nat) (hn : n < 2 ^ 64) (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState), k ≤ 170 * n + 107 ∧
      stepFnIter k (fmSeed (n : Int)) fmC0 ch = .ok (.next .stop, σf, ch)
      ∧ loadMany σf [.base ⟨1⟩]
          = .ok [.int ((fibW n : Nat) : Int) .uint64] := by
  have hE := fm_seg_entry n hn ch
  by_cases hn1 : n ≤ 1
  · -- base: the top-level call is itself a base case
    have hcall := fmCall_base (h9 (n : Int) (n : Int)) 9 6 8 n 0 "$c3" fibEnv
      [fibEpi] kFib ch hn1 (by with_unfolding_all rfl)
      (h9_fresh (n : Int) (n : Int)) (by omega) rfl
    have h8' : Heap.lookup ((h9 (n : Int) (n : Int)).set (.base ⟨8⟩)
        (u64c ((fibW n : Nat) : Int)) ++ frameCells 9 6 (n : Int) (n : Int))
        (.base ⟨8⟩) = some (u64c ((fibW n : Nat) : Int)) :=
      lookup_append_left lookup_set_self
    have h4' : Heap.lookup ((h9 (n : Int) (n : Int)).set (.base ⟨8⟩)
        (u64c ((fibW n : Nat) : Int)) ++ frameCells 9 6 (n : Int) (n : Int))
        (.base ⟨4⟩) = some (u64c 0) := by
      refine lookup_append_left ?_
      rw [lookup_set_other (by omega : 8 ≠ 4)]
      with_unfolding_all rfl
    have h2' : Heap.lookup (((h9 (n : Int) (n : Int)).set (.base ⟨8⟩)
        (u64c ((fibW n : Nat) : Int)) ++ frameCells 9 6 (n : Int) (n : Int)).set
        (.base ⟨4⟩) (u64c ((fibW n : Nat) : Int))) (.base ⟨2⟩)
        = some (u64c 0) := by
      rw [lookup_set_other (by omega : 4 ≠ 2)]
      refine lookup_append_left ?_
      rw [lookup_set_other (by omega : 8 ≠ 2)]
      with_unfolding_all rfl
    have h1' : Heap.lookup ((((h9 (n : Int) (n : Int)).set (.base ⟨8⟩)
        (u64c ((fibW n : Nat) : Int)) ++ frameCells 9 6 (n : Int) (n : Int)).set
        (.base ⟨4⟩) (u64c ((fibW n : Nat) : Int))).set (.base ⟨2⟩)
        (u64c ((fibW n : Nat) : Int))) (.base ⟨1⟩)
        = some (u64c 0) := by
      rw [lookup_set_other (by omega : 2 ≠ 1),
        lookup_set_other (by omega : 4 ≠ 1)]
      refine lookup_append_left ?_
      rw [lookup_set_other (by omega : 8 ≠ 1)]
      with_unfolding_all rfl
    have hT := fm_seg_tail ((h9 (n : Int) (n : Int)).set (.base ⟨8⟩)
        (u64c ((fibW n : Nat) : Int)) ++ frameCells 9 6 (n : Int) (n : Int))
      (9 + 3) ((fibW n : Nat) : Int) 0 0 0 ch h8' h4' h2' h1'
      (unorm_nat_of_lt (fibW_lt n))
    refine ⟨40 + 32 + 35, _, by omega,
      stepFnIter_chain (stepFnIter_chain hE hcall) hT, ?_⟩
    simp only [loadMany, loadLoc, fmSt, lookup_set_self, Bind.bind,
      Except.bind, pure, Except.pure]
  · -- the recursion builds the memo up to n
    have hn2 : 2 ≤ n := by omega
    obtain ⟨F, junk, na', hF, hna', hrun, _⟩ :=
      fmCall_build n hn2 hn 1 (h9 (n : Int) (n : Int)) 9 6 8 0 "$c3" fibEnv
        [fibEpi] kFib ch (by omega) (by omega)
        (by
          rw [mtbl_nil (by omega : (1 : Nat) ≤ 1)]
          with_unfolding_all rfl)
        (by with_unfolding_all rfl)
        (h9_fresh (n : Int) (n : Int)) (by omega) (by omega) rfl
    have h8' : Heap.lookup (((h9 (n : Int) (n : Int)).set (.base ⟨6⟩)
        (mapDc (mtbl n))).set (.base ⟨8⟩) (u64c ((fibW n : Nat) : Int))
        ++ junk) (.base ⟨8⟩) = some (u64c ((fibW n : Nat) : Int)) :=
      lookup_append_left lookup_set_self
    have h4' : Heap.lookup (((h9 (n : Int) (n : Int)).set (.base ⟨6⟩)
        (mapDc (mtbl n))).set (.base ⟨8⟩) (u64c ((fibW n : Nat) : Int))
        ++ junk) (.base ⟨4⟩) = some (u64c 0) := by
      refine lookup_append_left ?_
      rw [lookup_set_other (by omega : 8 ≠ 4),
        lookup_set_other (by omega : 6 ≠ 4)]
      with_unfolding_all rfl
    have h2' : Heap.lookup ((((h9 (n : Int) (n : Int)).set (.base ⟨6⟩)
        (mapDc (mtbl n))).set (.base ⟨8⟩) (u64c ((fibW n : Nat) : Int))
        ++ junk).set (.base ⟨4⟩) (u64c ((fibW n : Nat) : Int))) (.base ⟨2⟩)
        = some (u64c 0) := by
      rw [lookup_set_other (by omega : 4 ≠ 2)]
      refine lookup_append_left ?_
      rw [lookup_set_other (by omega : 8 ≠ 2),
        lookup_set_other (by omega : 6 ≠ 2)]
      with_unfolding_all rfl
    have h1' : Heap.lookup (((((h9 (n : Int) (n : Int)).set (.base ⟨6⟩)
        (mapDc (mtbl n))).set (.base ⟨8⟩) (u64c ((fibW n : Nat) : Int))
        ++ junk).set (.base ⟨4⟩) (u64c ((fibW n : Nat) : Int))).set
        (.base ⟨2⟩) (u64c ((fibW n : Nat) : Int))) (.base ⟨1⟩)
        = some (u64c 0) := by
      rw [lookup_set_other (by omega : 2 ≠ 1),
        lookup_set_other (by omega : 4 ≠ 1)]
      refine lookup_append_left ?_
      rw [lookup_set_other (by omega : 8 ≠ 1),
        lookup_set_other (by omega : 6 ≠ 1)]
      with_unfolding_all rfl
    have hT := fm_seg_tail (((h9 (n : Int) (n : Int)).set (.base ⟨6⟩)
        (mapDc (mtbl n))).set (.base ⟨8⟩) (u64c ((fibW n : Nat) : Int))
        ++ junk) na' ((fibW n : Nat) : Int) 0 0 0 ch h8' h4' h2' h1'
      (unorm_nat_of_lt (fibW_lt n))
    refine ⟨40 + F + 35, _, by omega,
      stepFnIter_chain (stepFnIter_chain hE hrun) hT, ?_⟩
    simp only [loadMany, loadLoc, fmSt, lookup_set_self, Bind.bind,
      Except.bind, pure, Except.pure]

/-- **THE HEADLINE (§11 harness form, S2 SCALAR)**: for every `n` in the
full uint64 domain, running `fibmemo_harness(n)` — the memoized
RECURSION, a live `map[uint64]uint64` memo consulted with the comma-ok
form — through the machine's native function entry completes normally
past ONE fuel bound, at every nondeterminism-choice stream, and returns
exactly `fibSpec n % 2^64`.

Honesty clauses, recorded rather than hidden:

* **The specification is the mathematical Fibonacci function** —
  `fibSpec`, the DESIGNATED statement vocabulary of the existing `fib`
  example, imported so the gallery's "Fibonacci" means one definition.
  The recursion, the memo table and its insertion order are all
  proof-side (`Examples/FibMemo/Rec.lean`) and never appear here.
* **`% 2^64` is machine-integer honesty** (the `fib` example's
  `fib_total` stance): on the full `n < 2^64` domain the uint64
  additions wrap, and the theorem says exactly the wrapped value —
  ONE reduction of the true value, proven equal to the composition of
  the machine's per-step wrappings (`fibW_rec`). For `n ≤ 93` the mod
  is the identity and the returned value IS `fibSpec n`.
* **The memo is load-bearing.** The fuel bound `170·n + 107` is LINEAR
  in `n` — without the memo the recursion would be exponential; the
  proof's induction (`fmCall_build`) tracks the table as exactly
  `{2..k}` and the second recursive call always hits it.
* **The bound is a BOUND, not a measurement**: measured totals are
  `107` (`n ≤ 1`), `249` (`n = 2`), and `170·n − 119` for `n ≥ 3`
  (probe-verified at `n = 3, 4, 5, 10`); `170·n + 107` dominates all
  of them.
* **`∀ ch` is vacuous here and stated anyway.** This harness consumes
  no nondeterminism choice (the memo is only INDEXED, never ranged
  over); the quantifier records that.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds — the
  recursion allocates a fresh frame per call and nothing bounds the
  depth but `n` itself. -/
theorem fibmemo_ok (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibmemoLowered.typeDefs.toList
          fibmemoLowered.funcs fibmemoHarnessFunc
          #[.int (n : Int) .uint64] fibmemoLowered.methods ch
        = .ok { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } := by
  refine ⟨170 * n + 107, fun fuel hfuel ch => ?_⟩
  rw [fm_entry_eq (n : Int) fuel ch, unorm_nat_of_lt hn]
  obtain ⟨k, σf, hk, hrun, hread⟩ := fm_runs n hn ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, runConfig_next_stop]
  simp only [bind, Except.bind, pure, Except.pure, hread]
  rfl

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly
`fibSpec n % 2^64` — derived from `fibmemo_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem fibmemo_readout (n : Nat) (hn : n < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel fibmemoLowered.typeDefs.toList
          fibmemoLowered.funcs fibmemoHarnessFunc
          #[.int (n : Int) .uint64] fibmemoLowered.methods ch
        = .ok r →
      r = { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } :=
  harness_readout_of_total (fibmemo_ok n hn)

end GoLean.Examples.FibMemo
