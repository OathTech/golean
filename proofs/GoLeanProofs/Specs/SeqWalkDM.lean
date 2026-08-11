import GoLeanProofs.LawsDM
import GoLeanProofs.Tactics.GoWalk
import GoLeanProofs.Surface
import GoLeanProofs.SurfaceBridge
import GoLeanProofs.Specs.GoldenQuorumWP

/-!
# The wpDM port witness — the kitchen-sink sequential DM walk
(channel-logic slice 3; design note
`docs/2026-08-11_channel-resource-tier.md` §4)

One single-threaded program on the MEDIATED carrier exercising every
named port of `LawsDM.lean` that has a site in it (the dsp flagship's
sequential surface). **Scope corrected at the S3 audit fix round:**
this said "every named port", and one port had no site — the program
contains no boolean literal, so `wpDM_eval_boolLit` fired nowhere.
Rather than bend the kitchen-sink program around it, that port gets
its own minimal witness at the end of this file
(`wpDM_eval_boolLit_witness`); the claim here is now exactly what the
program does. The walk:
call-frame entry (`wpDM_call_enter_ret1`) → `block` → six
`initialization`s (`wpDM_init`) → `makeChan` (`wpDM_make_chan` —
P-CL1-6's law, first consumer) → `newValue` (`wpDM_new_value`) →
`toInterface` boxing and `typeAssert` unboxing
(`wpDM_strict_apply_pin`) → `assignMany` (the multi-target tgtOp
spine) → deref/add (`wpDM_strict_apply_read`/`_pure`) → frame exit
(`wpDM_frame_return_int`), with the pure glue driven by `go_walk`
over the DM law table.

    func sinkFn() int {
      var ch chan any; ch = make(chan any)
      var p *int;      p = new(40)
      var i any;       i = any(p)
      var t *int;      t = i.(*int)
      var q *int; var w int; q, w = t, 2
      return *q + w        // 42
    }

D1-BOTH per the convention: `seqWalkReadoutC` + the seeded completion
pin `seqWalkTerminatesNormallyC` (kernel certificate,
`#eval`-confirmed first).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface
open Iris.BI

namespace GoLean.Iris

/-- The kitchen-sink function (module docstring). -/
def sinkFn : Func := {
  id := ⟨"sinkFn"⟩,
  args := #[],
  results := #[{ id := "$res0", typ := .int .int }],
  body := .block #[] #[
    .seqn #[.initialization ⟨"ch", .chan .both (.interface ⟨"any"⟩)⟩,
            .makeChan (.var "ch") (.interface ⟨"any"⟩) none],
    .seqn #[.initialization ⟨"p", .pointer .int⟩,
            .newValue (.var "p") (.intLit 40) (some .int)],
    .seqn #[.initialization ⟨"i", .interface ⟨"any"⟩⟩,
            .assign (.var "i")
              (.toInterface (.interface ⟨"any"⟩) (.pointer .int) (.var "p"))],
    .seqn #[.initialization ⟨"t", .pointer .int⟩,
            .assign (.var "t")
              (.typeAssert (.var "i") (.pointer .int)
                (some (.interface ⟨"any"⟩)))],
    .seqn #[.initialization ⟨"q", .pointer .int⟩,
            .initialization ⟨"w", .int .int⟩,
            .assignMany #[.var "q", .var "w"] #[.var "t", .intLit 2]],
    .seqn #[.assign (.var "$res0")
              (.add (.deref (.var "q") .int) (.var "w")),
            .returnStmt]]
}

/-- The driver: write `sinkFn()`'s verdict into the harness cell. -/
abbrev sinkProg : Stmt := .call #[.var "r"] ⟨"sinkFn"⟩ #[]
abbrev sinkEnv : LocalEnv := [[("r", .base ⟨0⟩)]]
abbrev sinkCell0 : HeapCell := ⟨some (.int .int), .int 0 .int⟩
abbrev sinkCell42 : HeapCell := ⟨some (.int .int), .int 42 .int⟩

abbrev sinkPre : HProp := .pointsTo 0 sinkCell0
abbrev sinkPost : HProp := .pointsTo 0 sinkCell42

/-- Channel handles ride through normalization at their declared type. -/
theorem sinkNormChan (σ : ExecState) (fa : Addr) :
    normalizeValueForTy σ (.chan .both (.interface ⟨"any"⟩))
      (.chan ⟨some (.base fa)⟩) = .ok (.chan ⟨some (.base fa)⟩) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

/-- Boxed interface values ride through normalization at `any`. -/
theorem sinkNormIface (σ : ExecState) (v : GoValue) :
    normalizeValueForTy σ (.interface ⟨"any"⟩)
      (.interface (.pointer .int) v) = .ok (.interface (.pointer .int) v) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

/-- Booleans ride through normalization at their declared type
(`wpDM_eval_boolLit`'s witness, below). -/
theorem sinkNormBool (σ : ExecState) (b : Bool) :
    normalizeValueForTy σ .bool (.bool b) = .ok (.bool b) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

/-- Pointers ride through normalization at their declared type. -/
theorem sinkNormPtr (σ : ExecState) (fa : Addr) :
    normalizeValueForTy σ (.pointer .int)
      (.addr (.base fa)) = .ok (.addr (.base fa)) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 6400000 in
/-- **The DM kitchen-sink walk** — the discharge witness for every
LawsDM port (module docstring). -/
theorem wpDM_seq_walk_witness
    (hprog : GoCoreGS.prog GF = #[sinkFn])
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) sinkPre
      ⊢ WP (PoolCfgDM.mk (.exec sinkProg sinkEnv .stop))
        @ Stuckness.MaybeStuck ; ⊤ {{ _v, embed (GF := GF) sinkPost }} := by
  iintro Hr
  simp only [sinkPre, sinkPost, embed]
  -- the call: frame entry, result cell allocated
  iapply (wpDM_call_enter_ret1 (func := sinkFn) (dv := .int 0 .int)
    (hplan := rfl)
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ hm => by
      simp [dynamicDispatch?, methodInfoByFuncId?, hm, hmeths, sinkFn])
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ra ⟨Hres, -⟩
  -- the body: block, first init
  simp only [sinkFn]
  go_walk
  iapply (wpDM_init (v := .chan ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a1 ⟨Hch, -⟩
  -- makeChan
  go_walk
  iapply (wpDM_make_chan (a := a1)
    (oldcell := ⟨some (.chan .both (.interface ⟨"any"⟩)), .chan ⟨none⟩⟩)
    (newcell := fun fa =>
      ⟨some (.chan .both (.interface ⟨"any"⟩)), .chan ⟨some (.base fa)⟩⟩)
    (hstore := fun σ fa _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, sinkNormChan σ fa,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hch]
  · iexact Hch
  iintro %f1 ⟨Hchan, Hch, -⟩
  -- init p, new(40)
  go_walk
  iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a2 ⟨Hp, -⟩
  go_walk
  iapply (wpDM_new_value (a := a2)
    (typ := some (.int .int))
    (oldcell := ⟨some (.pointer .int), .nil⟩)
    (newcell := fun fa => ⟨some (.pointer .int), .addr (.base fa)⟩)
    (hstore := fun σ fa _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, sinkNormPtr σ fa,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hp]
  · iexact Hp
  iintro %f2 ⟨Hval, Hp, -⟩
  -- init i, i = any(p)
  go_walk
  iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a3 ⟨Hi, -⟩
  go_walk
  iapply (wpDM_eval_var (a := a2)
    (cell := ⟨some (.pointer .int), .addr (.base f2)⟩) (hres := by rfl))
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wpDM_strict_apply_pin
    (out := .interface (.pointer .int) (.addr (.base f2)))
    (happly := fun σ _ => by
      simp +decide [applyStrictOp, canonicalDynamicTy, canonicalTy,
        canonicalTyFuel, Ty.mentionsUnsupported, typeResolutionFuel,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  go_walk
  iapply (wpDM_assign_store_loc (a := a3)
    (oldcell := ⟨some (.interface ⟨"any"⟩), .nil⟩)
    (newcell := ⟨some (.interface ⟨"any"⟩),
      .interface (.pointer .int) (.addr (.base f2))⟩)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue,
        sinkNormIface σ (.addr (.base f2)),
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  -- init t, t = i.(*int)
  go_walk
  iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a4 ⟨Ht, -⟩
  go_walk
  iapply (wpDM_eval_var (a := a3)
    (cell := ⟨some (.interface ⟨"any"⟩),
      .interface (.pointer .int) (.addr (.base f2))⟩) (hres := by rfl))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  iapply (wpDM_strict_apply_pin
    (out := .addr (.base f2))
    (happly := fun σ _ => by
      simp +decide [applyStrictOp, typeAssertValue, resolveDefinedAliases,
        resolveDefinedAliasesFuel, canonicalTy, canonicalTyFuel,
        defaultValue, defaultValueFuel, typeResolutionFuel,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  go_walk
  iapply (wpDM_assign_store_loc (a := a4)
    (oldcell := ⟨some (.pointer .int), .nil⟩)
    (newcell := ⟨some (.pointer .int), .addr (.base f2)⟩)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, sinkNormPtr σ f2,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  -- init q, init w, q, w = t, 2
  go_walk
  iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a5 ⟨Hq, -⟩
  go_walk
  iapply (wpDM_init (v := .int 0 .int) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a6 ⟨Hw, -⟩
  go_walk
  iapply (wpDM_eval_var (a := a4)
    (cell := ⟨some (.pointer .int), .addr (.base f2)⟩) (hres := by rfl))
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  go_walk
  iapply (wpDM_assign_store_loc (a := a5)
    (oldcell := ⟨some (.pointer .int), .nil⟩)
    (newcell := ⟨some (.pointer .int), .addr (.base f2)⟩)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, sinkNormPtr σ f2,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hq]
  · iexact Hq
  iintro Hq
  iapply (wpDM_assign_store_loc (a := a6)
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 2 .int⟩)
    (hstore := fun σ _ hlook => storeLoc_int_any hlook 2))
  isplitl [Hw]
  · iexact Hw
  iintro Hw
  -- $res0 = *q + w
  go_walk
  iapply (wpDM_eval_var (a := a5)
    (cell := ⟨some (.pointer .int), .addr (.base f2)⟩) (hres := by rfl))
  isplitl [Hq]
  · iexact Hq
  iintro Hq
  iapply (wpDM_strict_apply_read (a := f2)
    (cell := ⟨some (.int .int), .int 40 (.unbounded "integer")⟩)
    (out := .int 40 (.unbounded "integer"))
    (happly := fun σ _ hlook => by
      simp [applyStrictOp, valueAsLoc, loadLoc, hlook, Bind.bind, Except.bind,
        Pure.pure, Except.pure]))
  isplitl [Hval]
  · iexact Hval
  iintro Hval
  go_walk
  iapply (wpDM_eval_var (a := a6)
    (cell := ⟨some (.int .int), .int 2 .int⟩) (hres := by rfl))
  isplitl [Hw]
  · iexact Hw
  iintro Hw
  iapply (wpDM_strict_apply_pure
    (out := .int 42 .int)
    (happly := fun σ => by rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  go_walk
  iapply (wpDM_assign_store_loc (a := ra)
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 42 .int⟩)
    (hstore := fun σ _ hlook => storeLoc_int_any hlook 42))
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  -- return: unwind, frame exit writes the caller target
  go_walk
  iapply (wpDM_frame_return_int (x := "r") (ta := ⟨0⟩) (ra := ra)
    (kind := .int) (tkind := .int) (m := 42) (w := .int 0 .int)
    (hres := rfl))
  isplitl [Hres]
  · iexact Hres
  isplitl [Hr]
  · iexact Hr
  iintro ⟨Hres, Hr⟩
  iapply (wp_value' (v := ()))
  simp only [show IntKind.int.normalize 42 = 42 from by decide]
  iexact Hr

/-- **`wpDM_eval_boolLit`'s discharge witness** (added at the S3 audit
fix round; design note §11). The kitchen-sink program above has no
boolean literal, so that port had no consumer anywhere — an unwitnessed
law, against the house rule. It is NOT a scaffold to delete: boolean
literals are what the muxer rows' loop guards and `if` tests lower to
(`Expr.boolLit`, measured from the pinned lowering, §9), so the port
has real consumer shapes ahead of it. This is the minimal program
statement that fires it: `b = true` against a declared-`bool` cell,
walked on the DM carrier from the `assign` through the registered
`wpDM_eval_boolLit` step (applied EXPLICITLY via `go_walk_step`, so
the firing is visible in the proof rather than hidden inside the
table-driven glue) to the store — every premise discharged at the
concrete configuration. -/
theorem wpDM_eval_boolLit_witness {s : Stuckness} {E : CoPset}
    {Φ : Unit → IProp GF} {a : Addr} {k : Cont} :
    a.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some .bool, .bool true⟩ : HeapCell) -∗
          WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk
            (.exec (.assign (.var "b") (.boolLit true)) [[("b", .base a)]] k))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hb, Hcont⟩
  go_walk 3
  go_walk_step wpDM_eval_boolLit
  go_walk
  iapply (wpDM_assign_store_loc (a := a)
    (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, sinkNormBool σ true,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  go_walk
  iapply wpDM_seqCont_nil
  iapply Hcont
  iexact Hb

end

/-- **The kitchen-sink `GoTripleC`**: every `.normal` completion leaves
the harness cell at 42 — the verdict routed through make-chan, new,
boxing, unboxing, multi-assign, and both call frames, compositionally. -/
theorem seqWalkTripleC :
    GoTripleC [] #[sinkFn] #[] sinkEnv sinkPre sinkProg sinkPost :=
  goTripleC_of_wpDM (fun hprog hmeths _htypes =>
    wpDM_seq_walk_witness hprog hmeths)

/-- The seeded state for the D1 pair. -/
def sinkSeed : ExecState :=
  { types := [], functions := #[sinkFn], methods := #[],
    heap := [(.base ⟨0⟩, sinkCell0)], nextAddr := 1 }

/-- The run-conditioned first-order readout at the seed: the 42 pin. -/
theorem seqWalkReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel sinkEnv sinkSeed ch sinkProg = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 42 .int) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf sinkSeed.heap) sinkPre := by
    show sat ((∅ : Heaplet).insert 0 sinkCell0) sinkPre
    rfl
  have hsplit := InitialSplit.noFrame (P := sinkPre)
    (hp := sinkSeed.heap) (na := 1)
    (funcs := #[sinkFn]) (env₀ := sinkEnv) (prog := sinkProg)
    hsat (by decide +kernel)
  have hres := seqWalkTripleC _ 1 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨hQ, _hd, hsub, _hF, hsatQ⟩ := hres
  have hget0 : hQ.get? 0 = some sinkCell42 := by
    rw [show hQ = (∅ : Heaplet).insert 0 sinkCell42 from hsatQ,
      heaplet_get?_insert_self]
  have hg := hsub 0 sinkCell42 hget0
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
  exact loadLoc_base_of_lookup hg

/-- The completion half's kernel certificate (`#eval`-confirmed before
`decide`, per doctrine). -/
theorem seqWalkAllStreamsCert :
    allStreamsOkPool
      (fun σf =>
        match loadLoc σf (.base ⟨0⟩) with
        | .ok (.int 42 .int) => true
        | _ => false)
      500 ⟨#[.exec sinkProg sinkEnv .stop], sinkSeed, 0⟩ {} = true := by
  decide +kernel

/-- The seeded completion pin. -/
theorem seqWalkTerminatesNormallyC :
    TerminatesNormallyC sinkEnv sinkSeed sinkProg := by
  refine ⟨500, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool seqWalkAllStreamsCert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

end GoLean.Iris
