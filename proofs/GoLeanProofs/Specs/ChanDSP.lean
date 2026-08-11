import GoLeanProofs.ChanDMRes
import GoLeanProofs.LawsDM
import GoLeanProofs.Tactics.GoWalk
import GoLeanProofs.Specs.SeqWalkDM
import GoLeanProofs.Specs.ImportedGooseActris
import GoLeanProofs.Specs.GooseParityTargets
import GoLeanProofs.Specs.GooseParityChannels

/-!
# THE FLAGSHIP: dsp re-proved compositionally (channel-logic slice 3;
design note `docs/2026-08-11_channel-resource-tier.md` §5 — P-CL2-4
pays)

The dsp row (`DSPExample`, Actris 2.0 prog3; upstream `wp_DSPExample`
Qed at `channel_dsp.v`, pin 43d4efa) re-proved as a COMPOSITIONAL
frame-quantified triple over the PINNED frontend lowering
(`actrisLowered` — staleness-guarded, not a hand transcription), at
the row's established seed convention (`dspDriver`/`dspEnv`/`dspSeed`).
The session: main allocates a cell (`new(40)`), sends the boxed
pointer on `c`; the child writes `*ptr += 2` and signals; main
receives the signal and returns `*ptr` — **42**, upstream
`TestDSPExample`'s expected result and the differential row's pinned
verdict.

The route is the slice-3 stack end to end:

- the RESOURCE TIER (`chanInv`, ChanDMRes): `c`'s protocol carries the
  points-to of the pointed-to cell WITH the boxed pointer
  (`dspΨC`); `signal`'s carries it BACK at 42 (`dspΨS`) — the
  ownership transfer the pure tier provably cannot express (S2 §6
  obstacle 1);
- the REPLY-LEG META TIE (design note §2(a)): both protocols are fixed
  at invariant creation, BEFORE the transferred cell exists — the
  late-chosen address is pinned as gen_heap METADATA on the signal
  channel's own cell (`meta_set` from the `makeChan` law's
  `metaToken`), carried in both messages as persistent `metaInfo`,
  and closed by `meta_agree` at main's receive (upstream ties the two
  legs with iProto's dependent binder instead; deltas in the design
  note §7);
- the PERSISTED handle cells (`pointsTo_persist`, `↦{.discard}`) —
  both threads read `c`/`signal`'s variable cells after the fork
  (upstream's `iPersist "c signal"`, converged independently);
- the wpDM law ports (LawsDM) with `go_walk` driving the pure glue,
  and `goTripleC_of_wpDM` as the exit.

D1-BOTH: `dspCompReadoutC` (run-conditioned first-order readout at the
seed — the 42 pin in `loadLoc` vocabulary) + the completion half,
which this row ALREADY carries: `dspTerminatesNormallyC`
(`Specs/GooseParityChannels.lean`, the fuel-400 kernel certificate
family) — cited, not re-proved. The certificate families stay as
validation; THIS module is the row's compositional headline.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.ImportedGoose GoLean.ImportedGoose.ChannelActris
open Iris.BI

namespace GoLean.Iris

/-! ## `Pos.Countable` for addresses (design note §2(a): the one local
construction the meta tie needs — the pin carries Char/String/List
only; FD9's local-construction latitude, recorded) -/

instance : Pos.Countable Nat where
  encode n := Pos.ofNat n
  decode p := some (p.toNat - 1)
  decode_encode n := by simp [Pos.toNat_ofNat]

instance : Pos.Countable Addr where
  encode a := Pos.ofNat a.id
  decode p := some ⟨p.toNat - 1⟩
  decode_encode a := by simp [Pos.toNat_ofNat]

/-! ## The protocols -/

/-- The invariant namespaces (one per channel) and the meta namespace
(the reply tie's key on the signal cell's metadata space). -/
def dspNc : Namespace := ndot nroot "dspChanC"
def dspNs : Namespace := ndot nroot "dspChanS"
def dspMetaN : Namespace := ndot nroot "dspMeta"

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- `c`'s protocol: the message IS a boxed `*int`, and it CARRIES the
pointed-to cell (at 40) plus the persistent meta knowledge that ties
the session's reply leg to this address. `fs` is the signal channel's
data-cell address — in scope at invariant creation. -/
abbrev dspΨC (fs : Addr) : GoValue → IProp GF := fun v =>
  iprop(∃ x : Addr,
    ⌜v = .interface (.pointer .int) (.addr (.base x))⌝
      ∗ metaInfo (V := HeapCell) (H := GoHeapF) fs.id dspMetaN x
      ∗ x.id ↦ (⟨some (.int .int), .int 40 .int⟩ : HeapCell))

/-- `signal`'s protocol: the payload value is irrelevant (`struct{}{}`);
the RESOURCE is the written-back cell (at 42), tied to the session by
the same meta knowledge. -/
abbrev dspΨS (fs : Addr) : GoValue → IProp GF := fun _ =>
  iprop(∃ x : Addr,
    metaInfo (V := HeapCell) (H := GoHeapF) fs.id dspMetaN x
      ∗ x.id ↦ (⟨some (.int .int), .int 42 .int⟩ : HeapCell))

end

/-! ## Normalization facts (σ-independent; the walk's `hnorm`/`hstore`
raw material, `sinkNorm*`-style) -/

/-- Boxed struct values ride through normalization at `any`. -/
theorem dspNormIfaceStruct (σ : ExecState) :
    normalizeValueForTy σ (.interface ⟨"any"⟩)
      (.interface (.defined ⟨"struct{}"⟩) (.struct ⟨"struct{}"⟩ #[]))
      = .ok (.interface (.defined ⟨"struct{}"⟩) (.struct ⟨"struct{}"⟩ #[])) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

/-- Pointers-to-channel ride through normalization at their declared
type (the child's parameter binding). -/
theorem dspNormPtrChan (σ : ExecState) (loc : Loc) :
    normalizeValueForTy σ
      (.pointer (.chan .both (.interface ⟨"any"⟩))) (.addr loc)
      = .ok (.addr loc) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

/-- Channel handles ride through normalization at the declared channel
type (`sinkNormChan` at an arbitrary handle location). -/
theorem dspNormChan (σ : ExecState) (fa : Addr) :
    normalizeValueForTy σ (.chan .both (.interface ⟨"any"⟩))
      (.chan ⟨some (.base fa)⟩) = .ok (.chan ⟨some (.base fa)⟩) :=
  sinkNormChan σ fa

/-! ## The pinned bodies, transcribed behind `rfl` anchors (fail
closed: a frontend change that moves the lowering breaks these
equations in the same build that trips `check-imported-pins`) -/

abbrev dspChanTy : Ty := .chan .both (.interface ⟨"any"⟩)
abbrev dspPtrChanTy : Ty := .pointer dspChanTy

/-- The child (`DSPExample$lit0`) body, verbatim from the pin. -/
def dspChildBody : Stmt :=
  .block #[] #[
    .seqn #[.initialization ⟨"$c2", .interface ⟨"any"⟩⟩,
            .chanRecv #[.var "$c2"] (.deref (.var "c$cap") dspChanTy)
              (.interface ⟨"any"⟩)],
    .seqn #[.initialization ⟨"ptr", .pointer .int⟩,
            .assign (.var "ptr")
              (.typeAssert (.var "$c2") (.pointer .int)
                (some (.interface ⟨"any"⟩)))],
    .seqn #[.assign (.addr (.var "ptr"))
              (.add (.deref (.var "ptr") .int) (.intLit 2 .int))],
    .chanSend (.deref (.var "signal$cap") dspChanTy)
      (.toInterface (.interface ⟨"any"⟩) (.defined ⟨"struct{}"⟩)
        (.structLit (.defined ⟨"struct{}"⟩) #[]))
      (.interface ⟨"any"⟩)]

theorem dspChildBody_eq : (actrisLowered.funcs[0]?.map Func.body) = some dspChildBody := rfl

/-- The child's frame environment (`bindParams` order — `declare`
prepends) and configuration over the machine-chosen parameter base. -/
abbrev dspChildEnv (pa : Addr) : LocalEnv :=
  [[("signal$cap", .base ⟨pa.id + 1⟩), ("c$cap", .base pa)]]

def dspChildOf (pa : Addr) : Config :=
  .exec dspChildBody (dspChildEnv pa) (.frame [] [] [] [] .stop false)

/-- The handle cells (`c`/`signal` variable cells — persisted after the
fork) and the child's parameter cells (pointers TO those cells). -/
abbrev dspHandleCell (f : Addr) : HeapCell :=
  ⟨some dspChanTy, .chan ⟨some (.base f)⟩⟩
abbrev dspParamCell (h : Addr) : HeapCell :=
  ⟨some dspPtrChanTy, .addr (.base h)⟩

/-- The child env after its one declaration. -/
abbrev dspChildEnv1 (pa acc2 : Addr) : LocalEnv :=
  ((dspChildEnv pa).pushScope).declare "$c2" (.base acc2)

/-- The child continuation at its receive. -/
abbrev dspChildKRecv (pa acc2 : Addr) : Cont :=
  .seq [.seqn #[.initialization ⟨"ptr", .pointer .int⟩,
                .assign (.var "ptr")
                  (.typeAssert (.var "$c2") (.pointer .int)
                    (some (.interface ⟨"any"⟩)))],
        .seqn #[.assign (.addr (.var "ptr"))
                  (.add (.deref (.var "ptr") .int) (.intLit 2 .int))],
        .chanSend (.deref (.var "signal$cap") dspChanTy)
          (.toInterface (.interface ⟨"any"⟩) (.defined ⟨"struct{}"⟩)
            (.structLit (.defined ⟨"struct{}"⟩) #[]))
          (.interface ⟨"any"⟩)]
    (dspChildEnv1 pa acc2) (.frame [] [] [] [] .stop false)

/-- The child's delivery entry (σ-independent — the established
`deliverCfg` idiom). -/
abbrev dspChildDeliver (pa acc2 : Addr) (v : GoValue) : Config :=
  .evalE (.ref "$c2") (dspChildEnv1 pa acc2)
    (.tgtOpK (.chain []) [] [] [] [] .vals [] [v] (.seqn #[])
      (dspChildEnv1 pa acc2) (dspChildKRecv pa acc2))

theorem dspChildDel (pa acc2 : Addr) (σ : ExecState) (v : GoValue) :
    resumeRecvDelivery σ v true [.var "$c2"] (dspChildEnv1 pa acc2)
      (dspChildKRecv pa acc2)
      = .ok (dspChildDeliver pa acc2 v, σ) := rfl

/-! ## The child walk -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 6400000 in
/-- The child AFTER its receive delivered the boxed pointer to `x`
(carrying `x ↦ 40` and the meta tie): store the box, unbox, write 42
through the pointer, and signal — PAYING the written-back cell into
`signal`'s protocol. Shared by the park and immediate-drain branches. -/
private theorem dsp_child_after_recv
    (htypes : GoCoreGS.types GF = actrisLowered.typeDefs.toList)
    (fs as_ pa acc2 x : Addr) :
    Iris.inv dspNs (chanInv fs 0 (dspΨS fs))
      ∗ as_.id ↦{.discard} dspHandleCell fs
      ∗ (pa.id + 1) ↦ dspParamCell as_
      ∗ acc2.id ↦ (⟨some (.interface ⟨"any"⟩), .nil⟩ : HeapCell)
      ∗ metaInfo (V := HeapCell) (H := GoHeapF) fs.id dspMetaN x
      ∗ x.id ↦ (⟨some (.int .int), .int 40 .int⟩ : HeapCell)
      ⊢ WP (PoolCfgDM.mk (dspChildDeliver pa acc2
            (.interface (.pointer .int) (.addr (.base x)))))
          @ Stuckness.MaybeStuck ; ⊤ {{ fun _ => iprop(True) }} := by
  iintro ⟨#His, Has, Hp2, Hc2, Hmeta, Hx⟩
  simp only [dspChildDeliver, dspChildKRecv, dspChildEnv1, dspChildEnv]
  -- the delivery frame: store the boxed value into $c2's cell
  go_walk
  iapply (wpDM_assign_store_loc (a := acc2)
    (oldcell := ⟨some (.interface ⟨"any"⟩), .nil⟩)
    (newcell := ⟨some (.interface ⟨"any"⟩),
      .interface (.pointer .int) (.addr (.base x))⟩)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue,
        sinkNormIface σ (.addr (.base x)),
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hc2]
  · iexact Hc2
  iintro Hc2
  -- init ptr; ptr = $c2.(*int)
  go_walk
  iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %acp ⟨Hptr, -⟩
  go_walk
  iapply (wpDM_eval_var (a := acc2)
    (cell := ⟨some (.interface ⟨"any"⟩),
      .interface (.pointer .int) (.addr (.base x))⟩) (hres := by rfl))
  isplitl [Hc2]
  · iexact Hc2
  iintro Hc2
  iapply (wpDM_strict_apply_pin
    (out := .addr (.base x))
    (happly := fun σ _ => by
      simp +decide [applyStrictOp, typeAssertValue, resolveDefinedAliases,
        resolveDefinedAliasesFuel, canonicalTy, canonicalTyFuel,
        defaultValue, defaultValueFuel, typeResolutionFuel,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  go_walk
  iapply (wpDM_assign_store_loc (a := acp)
    (oldcell := ⟨some (.pointer .int), .nil⟩)
    (newcell := ⟨some (.pointer .int), .addr (.base x)⟩)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, sinkNormPtr σ x,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hptr]
  · iexact Hptr
  iintro Hptr
  -- *ptr = *ptr + 2
  go_walk
  iapply (wpDM_eval_var (a := acp)
    (cell := ⟨some (.pointer .int), .addr (.base x)⟩) (hres := by rfl))
  isplitl [Hptr]
  · iexact Hptr
  iintro Hptr
  go_walk
  iapply (wpDM_eval_var (a := acp)
    (cell := ⟨some (.pointer .int), .addr (.base x)⟩) (hres := by rfl))
  isplitl [Hptr]
  · iexact Hptr
  iintro Hptr
  iapply (wpDM_strict_apply_read (a := x)
    (cell := ⟨some (.int .int), .int 40 .int⟩)
    (out := .int 40 .int)
    (happly := fun σ _ hlook => by
      simp [applyStrictOp, valueAsLoc, loadLoc, hlook, Bind.bind, Except.bind,
        Pure.pure, Except.pure]))
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  go_walk
  iapply (wpDM_assign_store_loc (a := x)
    (oldcell := ⟨some (.int .int), .int 40 .int⟩)
    (newcell := ⟨some (.int .int), .int (IntKind.int.normalize 42) .int⟩)
    (hstore := fun σ _ hlook => storeLoc_int_any hlook 42))
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  simp only [show IntKind.int.normalize 42 = 42 from by decide]
  -- signal <- struct{}{}: deref the param, box, SEND paying x ↦ 42
  go_walk
  iapply (wpDM_eval_var (a := ⟨pa.id + 1⟩)
    (cell := dspParamCell as_) (hres := by rfl))
  isplitl [Hp2]
  · iexact Hp2
  iintro Hp2
  iapply (wpDM_strict_apply_read (a := as_) (dq := .discard)
    (cell := dspHandleCell fs)
    (out := .chan ⟨some (.base fs)⟩)
    (happly := fun σ _ hlook => by
      simp [applyStrictOp, valueAsLoc, loadLoc, hlook, Bind.bind, Except.bind,
        Pure.pure, Except.pure]))
  isplitl [Has]
  · iexact Has
  iintro Has
  go_walk
  iapply (wpDM_eval_strict_nullary_pin
    (hplan := rfl)
    (v := .struct ⟨"struct{}"⟩ #[])
    (happly := fun σ ht => by
      simp [applyStrictOp, buildStructValue, buildStructValueFuel,
        buildStructFields, resolveDefinedAliases, resolveDefinedAliasesFuel,
        typeResolutionFuel, ht, htypes, actrisLowered, TypeEnv.lookup,
        Functor.map, Except.map, Bind.bind, Except.bind,
        Pure.pure, Except.pure]))
  iapply (wpDM_strict_apply_pin
    (out := .interface (.defined ⟨"struct{}"⟩) (.struct ⟨"struct{}"⟩ #[]))
    (happly := fun σ ht => by
      simp +decide [applyStrictOp, canonicalDynamicTy, canonicalTy,
        canonicalTyFuel, typeResolutionFuel, resolveDefinedAliasesFuel,
        ht, htypes, actrisLowered, Ty.mentionsUnsupported, TypeEnv.lookup,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  -- THE SEND APPLY on signal, paying the written-back cell
  iapply (wpDM_send_inv (a := fs) (cap := 0) (Ψ := dspΨS fs)
    (v' := .interface (.defined ⟨"struct{}"⟩) (.struct ⟨"struct{}"⟩ #[]))
    (hN := CoPset.subseteq_top)
    (hnorm := fun σ _ => dspNormIfaceStruct σ))
  isplitl []
  · iexact His
  isplitl [Hmeta Hx]
  · iexists x
    isplitl [Hmeta]
    · iexact Hmeta
    · iexact Hx
  iintro %c₂ Hc₂
  icases Hc₂ with (⟨%hc₂, HΨ⟩ | %hc₂)
  · -- parked: the deposit completes it
    subst hc₂
    iapply (wpDM_blocked_send_inv (a := fs) (cap := 0) (Ψ := dspΨS fs)
      (hN := CoPset.subseteq_top))
    isplitl []
    · iexact His
    isplitl [HΨ]
    · iexact HΨ
    go_walk
    iapply (wp_value' (v := ()))
    itrivial
  · -- pushed
    subst hc₂
    go_walk
    iapply (wp_value' (v := ()))
    itrivial

set_option maxHeartbeats 6400000 in
/-- **The child walk** — from the spawn entry through the receive
(both branches) into `dsp_child_after_recv`. -/
private theorem dsp_child_walk
    (htypes : GoCoreGS.types GF = actrisLowered.typeDefs.toList)
    (fc fs ac as_ pa : Addr) :
    Iris.inv dspNc (chanInv fc 0 (dspΨC fs))
      ∗ Iris.inv dspNs (chanInv fs 0 (dspΨS fs))
      ∗ ac.id ↦{.discard} dspHandleCell fc
      ∗ as_.id ↦{.discard} dspHandleCell fs
      ∗ pa.id ↦ dspParamCell ac
      ∗ (pa.id + 1) ↦ dspParamCell as_
      ⊢ WP (PoolCfgDM.mk (dspChildOf pa)) @ Stuckness.MaybeStuck ; ⊤
          {{ fun _ => iprop(True) }} := by
  iintro ⟨#Hic, #His, Hac, Has, Hp1, Hp2⟩
  simp only [dspChildOf, dspChildBody]
  go_walk
  iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %acc2 ⟨Hc2, -⟩
  go_walk
  iapply (wpDM_eval_var (a := pa) (cell := dspParamCell ac) (hres := by rfl))
  isplitl [Hp1]
  · iexact Hp1
  iintro Hp1
  iapply (wpDM_strict_apply_read (a := ac) (dq := .discard)
    (cell := dspHandleCell fc)
    (out := .chan ⟨some (.base fc)⟩)
    (happly := fun σ _ hlook => by
      simp [applyStrictOp, valueAsLoc, loadLoc, hlook, Bind.bind, Except.bind,
        Pure.pure, Except.pure]))
  isplitl [Hac]
  · iexact Hac
  iintro Hac
  -- THE RECEIVE APPLY on c: the boxed pointer arrives WITH its resources
  iapply (wpDM_recv_inv (a := fc) (cap := 0) (Ψ := dspΨC fs)
    (targets := [.var "$c2"]) (elem := .interface ⟨"any"⟩)
    (hN := CoPset.subseteq_top)
    (deliverCfg := dspChildDeliver pa acc2)
    (hdel := dspChildDel pa acc2))
  isplitl []
  · iexact Hic
  iintro %c₂ Hc₂
  icases Hc₂ with (%hc₂ | ⟨%v, %hc₂, HΨ⟩)
  · -- parked receiver: the drain delivers
    subst hc₂
    iapply (wpDM_blocked_recv_inv (a := fc) (cap := 0) (Ψ := dspΨC fs)
      (targets := [.var "$c2"]) (elem := .interface ⟨"any"⟩)
      (hN := CoPset.subseteq_top)
      (deliverCfg := dspChildDeliver pa acc2)
      (hdel := dspChildDel pa acc2))
    isplitl []
    · iexact Hic
    iintro %c₃ Hc₃
    icases Hc₃ with ⟨%v, %hc₃, HΨ⟩
    subst hc₃
    icases HΨ with ⟨%x, %hv, Hmeta, Hx⟩
    subst hv
    iapply (dsp_child_after_recv htypes fs as_ pa acc2 x)
    isplitl []
    · iexact His
    isplitl [Has]
    · iexact Has
    isplitl [Hp2]
    · iexact Hp2
    isplitl [Hc2]
    · iexact Hc2
    isplitl [Hmeta]
    · iexact Hmeta
    · iexact Hx
  · -- immediate drain
    subst hc₂
    icases HΨ with ⟨%x, %hv, Hmeta, Hx⟩
    subst hv
    iapply (dsp_child_after_recv htypes fs as_ pa acc2 x)
    isplitl []
    · iexact His
    isplitl [Has]
    · iexact Has
    isplitl [Hp2]
    · iexact Hp2
    isplitl [Hc2]
    · iexact Hc2
    isplitl [Hmeta]
    · iexact Hmeta
    · iexact Hx

end

/-! ## The main thread: bodies, environments, continuations -/

/-- Persisted (discarded-fraction) points-to is persistent — the
`ghost_map_elem` instance seen through the `pointsTo` definition. -/
instance {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
    {l : Nat} {v : HeapCell} :
    Persistent (PROP := IProp GF) (l ↦{DFrac.discard} v) :=
  inferInstanceAs (Persistent (_ ↪◯MAP[l]{.discard} _))

/-- `DSPExample`, verbatim from the pin (`rfl`-anchored below). -/
def dspMainFn : Func :=
  { id := ⟨"DSPExample"⟩,
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := .block #[] #[
      .seqn #[.initialization ⟨"$c0", dspChanTy⟩,
              .makeChan (.var "$c0") (.interface ⟨"any"⟩) none],
      .seqn #[.initialization ⟨"$c1", dspChanTy⟩,
              .makeChan (.var "$c1") (.interface ⟨"any"⟩) none],
      .seqn #[.initialization ⟨"c", dspChanTy⟩,
              .initialization ⟨"signal", dspChanTy⟩,
              .assignMany #[.var "c", .var "signal"]
                #[.var "$c0", .var "$c1"]],
        .goStmt (.funcVal ⟨"DSPExample$lit0"⟩ #[.ref "c", .ref "signal"]) #[],
      .seqn #[.initialization ⟨"$c3", .pointer .int⟩,
              .newValue (.var "$c3") (.intLit 40 .int) (some (.int .int))],
      .seqn #[.initialization ⟨"ptr", .pointer .int⟩,
              .assign (.var "ptr") (.var "$c3")],
      .chanSend (.var "c")
        (.toInterface (.interface ⟨"any"⟩) (.pointer .int) (.var "ptr"))
        (.interface ⟨"any"⟩),
      .seqn #[.chanRecv #[] (.var "signal") (.interface ⟨"any"⟩)],
      .seqn #[.assign (.var "$res0") (.deref (.var "ptr") .int),
              .returnStmt]],
    variadic := false,
    wrapper := false }

/-- `goleanDSPExample`, verbatim from the pin. -/
def dspGoleanFn : Func :=
  { id := ⟨"goleanDSPExample"⟩,
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := .block #[] #[
      .seqn #[.initialization ⟨"$c4", .int .int⟩,
              .call #[.var "$c4"] ⟨"DSPExample"⟩ #[]],
      .seqn #[.assign (.var "$res0") (.var "$c4"),
              .returnStmt]],
    variadic := false,
    wrapper := false }

theorem dspMainFn_eq : actrisLowered.funcs[1]? = some dspMainFn := rfl
theorem dspGoleanFn_eq : actrisLowered.funcs[2]? = some dspGoleanFn := rfl

/-- goleanDSPExample's env at its call statement, and the frame/seq
continuations around DSPExample's frame. -/
abbrev dspEnvG (ra0 ac4 : Addr) : LocalEnv :=
  (LocalEnv.pushScope [[("$res0", .base ra0)]]).declare "$c4" (.base ac4)

abbrev dspKFrameG (ra0 : Addr) : Cont :=
  .frame [(.chain [], [.ref "r"])] dspEnv [.base ra0] [] .stop false

abbrev dspS2g : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c4"), .returnStmt]

abbrev dspKG (ra0 ac4 : Addr) : Cont :=
  .seq [dspS2g] (dspEnvG ra0 ac4) (dspKFrameG ra0)

abbrev dspKD (ra0 ac4 ra1 : Addr) : Cont :=
  .frame [(.chain [], [.ref "$c4"])] (dspEnvG ra0 ac4) [.base ra1] []
    (dspKG ra0 ac4) false

/-- DSPExample's env after all six declarations. -/
abbrev dspEnvM (ra1 a0 a1 ac as3 a3 ap : Addr) : LocalEnv :=
  ((((((LocalEnv.pushScope [[("$res0", .base ra1)]]).declare
    "$c0" (.base a0)).declare "$c1" (.base a1)).declare
    "c" (.base ac)).declare "signal" (.base as3)).declare
    "$c3" (.base a3)).declare "ptr" (.base ap)

abbrev dspS9 : Stmt :=
  .seqn #[.assign (.var "$res0") (.deref (.var "ptr") .int), .returnStmt]

/-- Main's continuation at its receive on `signal`. -/
abbrev dspKRecvM (ra0 ac4 ra1 a0 a1 ac as3 a3 ap : Addr) : Cont :=
  .seq [dspS9] (dspEnvM ra1 a0 a1 ac as3 a3 ap) (dspKD ra0 ac4 ra1)

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 6400000 in
/-- Main AFTER the signal receive delivered (and `meta_agree` closed
the tie — this lemma takes the re-owned cell at MAIN's `x` directly):
`$res0 = *ptr`, return through both frames, `r = 42`. -/
private theorem dsp_main_final (ra0 ac4 ra1 a0 a1 ac as3 a3 ap x : Addr) :
    ap.id ↦ (⟨some (.pointer .int), .addr (.base x)⟩ : HeapCell)
      ∗ x.id ↦ (⟨some (.int .int), .int 42 .int⟩ : HeapCell)
      ∗ ra1.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ ac4.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ ra0.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (0 : Nat) ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ⊢ WP (PoolCfgDM.mk (.next (dspKRecvM ra0 ac4 ra1 a0 a1 ac as3 a3 ap)))
          @ Stuckness.MaybeStuck ; ⊤
          {{ _v, iprop((0 : Nat) ↦ (⟨some (.int .int), .int 42 .int⟩ : HeapCell)) }} := by
  iintro ⟨Hptr, Hx, Hres1, Hc4, Hres0, Hr⟩
  go_walk
  iapply (wpDM_eval_var (a := ap)
    (cell := ⟨some (.pointer .int), .addr (.base x)⟩) (hres := by rfl))
  isplitl [Hptr]
  · iexact Hptr
  iintro Hptr
  iapply (wpDM_strict_apply_read (a := x)
    (cell := ⟨some (.int .int), .int 42 .int⟩)
    (out := .int 42 .int)
    (happly := fun σ _ hlook => by
      simp [applyStrictOp, valueAsLoc, loadLoc, hlook, Bind.bind, Except.bind,
        Pure.pure, Except.pure]))
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  go_walk
  iapply (wpDM_assign_store_loc (a := ra1)
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (IntKind.int.normalize 42) .int⟩)
    (hstore := fun σ _ hlook => storeLoc_int_any hlook 42))
  isplitl [Hres1]
  · iexact Hres1
  iintro Hres1
  simp only [show IntKind.int.normalize 42 = 42 from by decide]
  go_walk
  iapply (wpDM_frame_return_int (x := "$c4") (ta := ac4) (ra := ra1)
    (kind := .int) (tkind := .int) (m := 42) (w := .int 0 .int)
    (hres := by rfl))
  isplitl [Hres1]
  · iexact Hres1
  isplitl [Hc4]
  · iexact Hc4
  iintro ⟨Hres1, Hc4⟩
  simp only [show IntKind.int.normalize 42 = 42 from by decide]
  go_walk
  iapply (wpDM_eval_var (a := ac4)
    (cell := ⟨some (.int .int), .int 42 .int⟩) (hres := by rfl))
  isplitl [Hc4]
  · iexact Hc4
  iintro Hc4
  go_walk
  iapply (wpDM_assign_store_loc (a := ra0)
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (IntKind.int.normalize 42) .int⟩)
    (hstore := fun σ _ hlook => storeLoc_int_any hlook 42))
  isplitl [Hres0]
  · iexact Hres0
  iintro Hres0
  simp only [show IntKind.int.normalize 42 = 42 from by decide]
  go_walk
  iapply (wpDM_frame_return_int (x := "r") (ta := ⟨0⟩) (ra := ra0)
    (kind := .int) (tkind := .int) (m := 42) (w := .int 0 .int)
    (hres := by rfl))
  isplitl [Hres0]
  · iexact Hres0
  isplitl [Hr]
  · iexact Hr
  iintro ⟨Hres0, Hr⟩
  iapply (wp_value' (v := ()))
  simp only [show IntKind.int.normalize 42 = 42 from by decide]
  iexact Hr

set_option maxHeartbeats 6400000 in
/-- Main AFTER its send on `c` completed: receive on `signal`
(re-acquiring the written-back cell through the protocol and the meta
tie), then `dsp_main_final`. Shared by the park and push branches. -/
private theorem dsp_main_after_send
    (fs ra0 ac4 ra1 a0 a1 ac as3 a3 ap x : Addr) :
    Iris.inv dspNs (chanInv fs 0 (dspΨS fs))
      ∗ as3.id ↦{.discard} dspHandleCell fs
      ∗ metaInfo (V := HeapCell) (H := GoHeapF) fs.id dspMetaN x
      ∗ ap.id ↦ (⟨some (.pointer .int), .addr (.base x)⟩ : HeapCell)
      ∗ ra1.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ ac4.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ ra0.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (0 : Nat) ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ⊢ WP (PoolCfgDM.mk (.next (.seq
            [.seqn #[.chanRecv #[] (.var "signal") (.interface ⟨"any"⟩)], dspS9]
            (dspEnvM ra1 a0 a1 ac as3 a3 ap) (dspKD ra0 ac4 ra1))))
          @ Stuckness.MaybeStuck ; ⊤
          {{ _v, iprop((0 : Nat) ↦ (⟨some (.int .int), .int 42 .int⟩ : HeapCell)) }} := by
  iintro ⟨#His, #Has3, #Hmeta, Hptr, Hres1, Hc4, Hres0, Hr⟩
  go_walk
  iapply (wpDM_eval_var (a := as3) (cell := dspHandleCell fs) (hres := by rfl))
  isplitl []
  · iexact Has3
  iintro -
  -- THE RECEIVE APPLY on signal
  iapply (wpDM_recv_inv (a := fs) (cap := 0) (Ψ := dspΨS fs)
    (targets := []) (elem := .interface ⟨"any"⟩)
    (hN := CoPset.subseteq_top)
    (deliverCfg := fun _ => .next (dspKRecvM ra0 ac4 ra1 a0 a1 ac as3 a3 ap))
    (hdel := fun σ v => rfl))
  isplitl []
  · iexact His
  iintro %c₂ Hc₂
  icases Hc₂ with (%hc₂ | ⟨%v, %hc₂, HΨ⟩)
  · -- parked receiver
    subst hc₂
    iapply (wpDM_blocked_recv_inv (a := fs) (cap := 0) (Ψ := dspΨS fs)
      (targets := []) (elem := .interface ⟨"any"⟩)
      (hN := CoPset.subseteq_top)
      (deliverCfg := fun _ => .next (dspKRecvM ra0 ac4 ra1 a0 a1 ac as3 a3 ap))
      (hdel := fun σ v => rfl))
    isplitl []
    · iexact His
    iintro %c₃ Hc₃
    icases Hc₃ with ⟨%v, %hc₃, HΨ⟩
    subst hc₃
    icases HΨ with ⟨%x', Hmeta', Hx⟩
    ihave %heq : ⌜x' = x⌝ $$ [Hmeta' Hmeta]
    · iapply meta_agree $$ Hmeta' Hmeta
    subst heq
    iapply (dsp_main_final ra0 ac4 ra1 a0 a1 ac as3 a3 ap x')
    isplitl [Hptr]
    · iexact Hptr
    isplitl [Hx]
    · iexact Hx
    isplitl [Hres1]
    · iexact Hres1
    isplitl [Hc4]
    · iexact Hc4
    isplitl [Hres0]
    · iexact Hres0
    · iexact Hr
  · -- immediate drain
    subst hc₂
    icases HΨ with ⟨%x', Hmeta', Hx⟩
    ihave %heq : ⌜x' = x⌝ $$ [Hmeta' Hmeta]
    · iapply meta_agree $$ Hmeta' Hmeta
    subst heq
    iapply (dsp_main_final ra0 ac4 ra1 a0 a1 ac as3 a3 ap x')
    isplitl [Hptr]
    · iexact Hptr
    isplitl [Hx]
    · iexact Hx
    isplitl [Hres1]
    · iexact Hres1
    isplitl [Hc4]
    · iexact Hc4
    isplitl [Hres0]
    · iexact Hres0
    · iexact Hr

end


section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 12800000 in
/-- **The DM-carrier walk of the dsp row** — driver → both frames →
the session (fork, send with the outbound resources, receive with the
reply resources, the meta tie) → 42 into the harness cell. The
discharge witness for the whole slice-3 stack on the PINNED lowering. -/
theorem wpDM_dsp_witness
    (hprog : GoCoreGS.prog GF = actrisLowered.funcs)
    (hmeths : GoCoreGS.methods GF = actrisLowered.methods)
    (htypes : GoCoreGS.types GF = actrisLowered.typeDefs.toList) :
    embed (GF := GF) importedCell0
      ⊢ WP (PoolCfgDM.mk (.exec dspDriver dspEnv .stop))
        @ Stuckness.MaybeStuck ; ⊤ {{ _v, embed (GF := GF) (importedCellV 42) }} := by
  iintro Hr
  simp only [importedCell0, importedCellV, embed]
  -- the driver call: goleanDSPExample's frame
  iapply (wpDM_call_enter_ret1 (func := dspGoleanFn) (dv := .int 0 .int)
    (hplan := rfl)
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ hm => by
      simp [dynamicDispatch?, methodInfoByFuncId?, hm, hmeths,
        actrisLowered, dspGoleanFn])
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ra0 ⟨Hres0, -⟩
  simp only [dspGoleanFn]
  go_walk
  iapply (wpDM_init (v := .int 0 .int) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ac4 ⟨Hc4, -⟩
  go_walk
  -- DSPExample's frame
  iapply (wpDM_call_enter_ret1 (func := dspMainFn) (dv := .int 0 .int)
    (hplan := rfl)
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ hm => by
      simp [dynamicDispatch?, methodInfoByFuncId?, hm, hmeths,
        actrisLowered, dspMainFn])
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ra1 ⟨Hres1, -⟩
  simp only [dspMainFn]
  go_walk
  -- $c0 = make(chan any)
  iapply (wpDM_init (v := .chan ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a0 ⟨Ha0, -⟩
  go_walk
  iapply (wpDM_make_chan (a := a0)
    (oldcell := ⟨some dspChanTy, .chan ⟨none⟩⟩)
    (newcell := dspHandleCell)
    (hstore := fun σ fa _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, dspNormChan σ fa,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Ha0]
  · iexact Ha0
  iintro %fc ⟨Hfc, Ha0, -⟩
  -- $c1 = make(chan any) — KEEP the signal cell's metaToken (the tie)
  go_walk
  iapply (wpDM_init (v := .chan ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %a1 ⟨Ha1, -⟩
  go_walk
  iapply (wpDM_make_chan (a := a1)
    (oldcell := ⟨some dspChanTy, .chan ⟨none⟩⟩)
    (newcell := dspHandleCell)
    (hstore := fun σ fa _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, dspNormChan σ fa,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Ha1]
  · iexact Ha1
  iintro %fs ⟨Hfs, Ha1, Htoks⟩
  -- c, signal = $c0, $c1
  go_walk
  iapply (wpDM_init (v := .chan ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ac ⟨Hac, -⟩
  go_walk
  iapply (wpDM_init (v := .chan ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %as3 ⟨Has3, -⟩
  go_walk
  iapply (wpDM_eval_var (a := a0) (cell := dspHandleCell fc) (hres := by rfl))
  isplitl [Ha0]
  · iexact Ha0
  iintro Ha0
  go_walk
  iapply (wpDM_eval_var (a := a1) (cell := dspHandleCell fs) (hres := by rfl))
  isplitl [Ha1]
  · iexact Ha1
  iintro Ha1
  go_walk
  iapply (wpDM_assign_store_loc (a := ac)
    (oldcell := ⟨some dspChanTy, .chan ⟨none⟩⟩)
    (newcell := dspHandleCell fc)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, dspNormChan σ fc,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hac]
  · iexact Hac
  iintro Hac
  iapply (wpDM_assign_store_loc (a := as3)
    (oldcell := ⟨some dspChanTy, .chan ⟨none⟩⟩)
    (newcell := dspHandleCell fs)
    (hstore := fun σ _ hlook => by
      simp [storeLoc, hlook, coerceStoredValue, dspNormChan σ fs,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Has3]
  · iexact Has3
  iintro Has3
  -- the ghost moves: both invariants allocated, both handles persisted
  iapply fupd_wp
  imod inv_alloc dspNc ⊤ (chanInv (GF := GF) fc 0 (dspΨC fs)) $$ [Hfc]
    with Hinvc
  · inext
    iexists (#[] : Array GoValue)
    isplitr [Hfc]
    · simp only [Array.toList_empty]
      iapply (BigSepL.bigSepL_nil (Φ := fun _ v => dspΨC (GF := GF) fs v)).2
      itrivial
    · iexact Hfc
  imod inv_alloc dspNs ⊤ (chanInv (GF := GF) fs 0 (dspΨS fs)) $$ [Hfs]
    with Hinvs
  · inext
    iexists (#[] : Array GoValue)
    isplitr [Hfs]
    · simp only [Array.toList_empty]
      iapply (BigSepL.bigSepL_nil (Φ := fun _ v => dspΨS (GF := GF) fs v)).2
      itrivial
    · iexact Hfs
  imod (pointsTo_persist) $$ Hac with Hac
  imod (pointsTo_persist) $$ Has3 with Has3
  icases Hinvc with #Hinvc
  icases Hinvs with #Hinvs
  icases Hac with #Hac
  icases Has3 with #Has3
  imodintro
  -- the fork: the child gets the param cells and the shared knowledge
  go_walk
  iapply (wpDM_fork_alloc₂ dspChildOf
    (pcell₁ := dspParamCell ac) (pcell₂ := dspParamCell as3) (hsp := rfl)
    (hspawn := by
      intro σ hf hm ht
      simp +decide [spawnStep, enterFrame, findFunctionIn?,
        dynamicDispatch?, bindParams, allocDecls, pinResultLocs,
        methodInfoByFuncId?, hf, hm, hprog, hmeths, actrisLowered,
        dspChildOf, dspChildBody, LocalEnv.declare, dspNormPtrChan,
        allocMany, ExecState.alloc, ExecState.freshLoc,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl []
  · -- THE CHILD
    inext
    iintro %pa ⟨Hp1, Hp2⟩
    iapply (dsp_child_walk htypes fc fs ac as3 pa)
    isplitl []
    · iexact Hinvc
    isplitl []
    · iexact Hinvs
    isplitl []
    · iexact Hac
    isplitl []
    · iexact Has3
    isplitl [Hp1]
    · iexact Hp1
    · iexact Hp2
  · -- THE PARENT
    inext
    iapply wpDM_spawned_strip
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro -
    -- $c3 = new(40)
    go_walk
    iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
    iintro %a3 ⟨Ha3, -⟩
    go_walk
    iapply (wpDM_new_value (a := a3)
      (typ := some (.int .int))
      (oldcell := ⟨some (.pointer .int), .nil⟩)
      (newcell := fun fa => ⟨some (.pointer .int), .addr (.base fa)⟩)
      (hstore := fun σ fa _ hlook => by
        simp [storeLoc, hlook, coerceStoredValue, sinkNormPtr σ fa,
          Bind.bind, Except.bind, Pure.pure, Except.pure]))
    isplitl [Ha3]
    · iexact Ha3
    iintro %fx ⟨Hx, Ha3, -⟩
    -- THE META SET: pin the fresh address on the signal cell's metadata
    iapply fupd_wp
    imod (meta_set (N := dspMetaN) (⟨fx.id⟩ : Addr) CoPset.subseteq_top)
      $$ Htoks with Hmeta
    icases Hmeta with #Hmeta
    imodintro
    -- ptr = $c3
    go_walk
    iapply (wpDM_init (v := .nil) (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
    iintro %ap ⟨Hap, -⟩
    go_walk
    iapply (wpDM_eval_var (a := a3)
      (cell := ⟨some (.pointer .int), .addr (.base fx)⟩) (hres := by rfl))
    isplitl [Ha3]
    · iexact Ha3
    iintro Ha3
    go_walk
    iapply (wpDM_assign_store_loc (a := ap)
      (oldcell := ⟨some (.pointer .int), .nil⟩)
      (newcell := ⟨some (.pointer .int), .addr (.base fx)⟩)
      (hstore := fun σ _ hlook => by
        simp [storeLoc, hlook, coerceStoredValue, sinkNormPtr σ fx,
          Bind.bind, Except.bind, Pure.pure, Except.pure]))
    isplitl [Hap]
    · iexact Hap
    iintro Hap
    -- c <- any(ptr)
    go_walk
    iapply (wpDM_eval_var (a := ac) (cell := dspHandleCell fc)
      (hres := by rfl))
    isplitl []
    · iexact Hac
    iintro -
    go_walk
    iapply (wpDM_eval_var (a := ap)
      (cell := ⟨some (.pointer .int), .addr (.base fx)⟩) (hres := by rfl))
    isplitl [Hap]
    · iexact Hap
    iintro Hap
    iapply (wpDM_strict_apply_pin
      (out := .interface (.pointer .int) (.addr (.base fx)))
      (happly := fun σ _ => by
        simp +decide [applyStrictOp, canonicalDynamicTy, canonicalTy,
          canonicalTyFuel, Ty.mentionsUnsupported, typeResolutionFuel,
          Bind.bind, Except.bind, Pure.pure, Except.pure]))
    -- THE SEND APPLY on c: the pointer leaves WITH its cell and the tie
    iapply (wpDM_send_inv (a := fc) (cap := 0) (Ψ := dspΨC fs)
      (v' := .interface (.pointer .int) (.addr (.base fx)))
      (hN := CoPset.subseteq_top)
      (hnorm := fun σ _ => sinkNormIface σ (.addr (.base fx))))
    isplitl []
    · iexact Hinvc
    isplitl [Hmeta Hx]
    · iexists fx
      isplitr [Hmeta Hx]
      · ipureintro
        rfl
      isplitl []
      · iexact Hmeta
      · iexact Hx
    iintro %c₂ Hc₂
    icases Hc₂ with (⟨%hc₂, HΨ⟩ | %hc₂)
    · -- parked sender: the deposit completes it
      subst hc₂
      iapply (wpDM_blocked_send_inv (a := fc) (cap := 0) (Ψ := dspΨC fs)
        (hN := CoPset.subseteq_top))
      isplitl []
      · iexact Hinvc
      isplitl [HΨ]
      · iexact HΨ
      iapply (dsp_main_after_send fs ra0 ac4 ra1 a0 a1 ac as3 a3 ap fx)
      isplitl []
      · iexact Hinvs
      isplitl []
      · iexact Has3
      isplitl []
      · iexact Hmeta
      isplitl [Hap]
      · iexact Hap
      isplitl [Hres1]
      · iexact Hres1
      isplitl [Hc4]
      · iexact Hc4
      isplitl [Hres0]
      · iexact Hres0
      · iexact Hr
    · -- immediate push
      subst hc₂
      iapply (dsp_main_after_send fs ra0 ac4 ra1 a0 a1 ac as3 a3 ap fx)
      isplitl []
      · iexact Hinvs
      isplitl []
      · iexact Has3
      isplitl []
      · iexact Hmeta
      isplitl [Hap]
      · iexact Hap
      isplitl [Hres1]
      · iexact Hres1
      isplitl [Hc4]
      · iexact Hc4
      isplitl [Hres0]
      · iexact Hres0
      · iexact Hr

end

/-- **THE FLAGSHIP TRIPLE** — the dsp row as a compositional
frame-quantified `GoTripleC` over the pinned lowering: every `.normal`
completion from ANY admissible seeded heap leaves the harness cell at
**42** (upstream `TestDSPExample`'s expected result), proved laws →
wpDM → resource tier → meta tie → exit, never by execution. -/
theorem dspCompTripleC :
    GoTripleC actrisLowered.typeDefs.toList actrisLowered.funcs
      actrisLowered.methods dspEnv importedCell0 dspDriver
      (importedCellV 42) :=
  goTripleC_of_wpDM (fun hprog hmeths htypes =>
    wpDM_dsp_witness hprog hmeths htypes)

/-- The run-conditioned first-order readout at the row's seed
(`dspSeed`) — **the 42 pin in `loadLoc` vocabulary**. The completion
half of the D1 pair is the row's standing `dspTerminatesNormallyC`
(`Specs/GooseParityChannels.lean`). -/
theorem dspCompReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel dspEnv dspSeed ch dspDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 42 .int) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf dspSeed.heap) importedCell0 := by
    show sat ((∅ : Heaplet).insert 0 intCell0) importedCell0
    rfl
  have hsplit := InitialSplit.noFrame (P := importedCell0)
    (hp := dspSeed.heap) (na := 1)
    (funcs := actrisLowered.funcs) (env₀ := dspEnv) (prog := dspDriver)
    hsat (by decide +kernel)
  have hres := dspCompTripleC _ 1 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨hQ, _hd, hsub, _hF, hsatQ⟩ := hres
  have hget0 : hQ.get? 0 = some ⟨some (.int .int), .int 42 .int⟩ := by
    rw [show hQ = (∅ : Heaplet).insert 0 ⟨some (.int .int), .int 42 .int⟩
      from hsatQ, heaplet_get?_insert_self]
  have hg := hsub 0 _ hget0
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
  exact loadLoc_base_of_lookup hg


/-- The completion half of the D1 pair — the row's STANDING seeded
completion pin (`Specs/GooseParityChannels.lean`, the fuel-400 kernel
certificate family), restated here so the pair lives beside the
triple. Same program, same seed; the certificate is not re-proved. -/
theorem dspCompTerminatesNormallyC :
    TerminatesNormallyC dspEnv dspSeed dspDriver :=
  ImportedGoose.ChannelActris.dspTerminatesNormallyC

end GoLean.Iris
