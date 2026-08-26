import GoLeanProofs.Sym.TableExt
import GoLeanProofs.SliceMem

/-!
# The append-spill transport (A4-U10 deliverable 1)

**LINEAGE: symbolic-execution path-condition splitting at a
nondeterministic-choice site — the same classic as
`stepFn_pick_transport` (choice-point transport in the
symbolic-execution-by-conservative-extension frame, design
`2026-08-22_campaign-arc4-sym-extension-design.md` §4(ii)) — realized
over the SliceMem Group-4 spill machinery
(`applyStmtOp_append1_spill`'s walk, WP arc s2 item 3) instead of the
map-pick step.**

The appendSlice SPILL is the machine's second choice-consumption site
(`ChoiceSite.appendSpill`): a reallocating one-element append consumes
one capacity choice of width `appendSpillWidth` and allocates a fresh
backing cell whose declared type `.array newCap elem` carries the
REALIZED capacity. The mirror quits `.q3Choice` at exactly the apply
configuration (`applyStmtOp'`, Mirror.lean), so a window ends AT the
spill and this transport crosses it in one machine step, exactly as
`stepFn_pick_transport` crosses a map pick.

The §4(ii) collapse at this site: the realized capacity
`appendRealizedCap cap (len+1) extra` depends on the consumed choice,
so the choice-dependent artifacts (the backing CELL — value AND
declared type — and the slice handle written to the target) enter the
post fixture as VALUATION atoms (`Valuation.cells` — whose docstring
names the append-backing declared type as the design case — and
`Valuation.vals`), and ONE post-window literal serves every consumed
choice; the handler's prefix-derived valuation absorbs the spill.

Shapes covered: ONE appended element (`#[w]` visible in the elems
operand), any old-slice handle (nil base included — `r.msgs` at init
is the nil slice; the SliceMem lemma pins a `some` base). All three
motivating sites (handleHeartbeat + handleAppendEntries `r.msgs`
appends, becomeLeader's appendEntry path) are one-element appends; a
multi-element variant is future work on its first consumer.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower
  appendRealizedCap_upper)

/-- `validateSlice` succeeds at a `some`-base handle with `len ≤ cap`
(the SliceMem fact is `private`; re-proved here for the Option-base
walk). -/
theorem validateSlice_some_ok {b : Loc} {off len cap : Nat}
    (hcap : len ≤ cap) :
    validateSlice ⟨some b, off, len, cap⟩ = .ok () := by
  simp [validateSlice, Nat.not_lt.mpr hcap]

/-- **The spill apply at the SINGLE realized capacity** (the SliceMem
Group-4 walk, generalized to an Option-base old handle — the nil
outbox — and conditioned at exactly the realized capacity rather than
capacity-generically; `nt` is ignored by the appendSlice arm and stays
free). -/
theorem applyStmtOp_append1_spill_at {σ σ₂ : ExecState} {elem : Ty}
    {nt : Nat} {tloc : Loc} {sb : Option Loc} {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {old : Array GoValue} {bk : GoValue}
    {ch ch' : Choices} {extra : Nat}
    (hfull : cap < len + 1) (hec : elen ≤ ecap)
    (hvalidO : validateSlice ⟨sb, off, len, cap⟩ = .ok ())
    (hvisE : sliceVisibleValues σ ⟨some eb, eoff, elen, ecap⟩ = .ok #[w])
    (hvisO : sliceVisibleValues σ ⟨sb, off, len, cap⟩ = .ok old)
    (hcons : ch.consume (appendSpillWidth cap (len + 1)) = (extra, ch'))
    (hbuild : buildAppendBackingValue σ elem old #[w]
        (appendRealizedCap cap (len + 1) extra) = .ok bk)
    (htgt : storeLoc { σ with
          heap := GoCore.Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            ⟨some (.array (appendRealizedCap cap (len + 1) extra) elem), bk⟩,
          nextAddr := σ.nextAddr + 1 } tloc
        (.slice ⟨some (.base ⟨σ.nextAddr⟩), 0, len + 1,
          appendRealizedCap cap (len + 1) extra⟩)
      = .ok σ₂) :
    applyStmtOp σ ch (.appendSlice elem) nt
      [.addr tloc, .slice ⟨sb, off, len, cap⟩,
       .slice ⟨some eb, eoff, elen, ecap⟩]
      = .ok (σ₂, ch') := by
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, hvalidO, validateSlice_some_ok hec,
    hvisE]
  rw [if_neg (by simp; omega)]
  simp only [hvisO, Bind.bind, Except.bind, pure, Except.pure]
  simp only [Choices.consumeAt_appendSpill,
    show (#[w] : Array GoValue).size = 1 from rfl, hcons]
  rw [show len + 1 + ((appendGrowthCap cap (len + 1) - (len + 1)
        + extra) % appendSpillWidth cap (len + 1))
      = appendRealizedCap cap (len + 1) extra from rfl]
  rw [hbuild]
  simp only [ExecState.alloc, ExecState.freshLoc, Bind.bind,
    Except.bind, pure, Except.pure]
  rw [htgt]

/-- **THE APPEND-SPILL TRANSPORT**: the spill apply step at a γ-image
— mirror-side configuration, machine-level conclusion, post state
reaching a given mirror image (`S₂` carries the choice-dependent
backing cell/handle as valuation atoms; the `htgt` premise is where a
handler discharges the target write-back, e.g. through the Lens store
laws or closed evaluation at its fixture). One appended element; the
old handle may be nil-based. -/
theorem stepFn_appendSpill_transport (ρ : Valuation) (σ : ExecState)
    {S S₂ : SymState} {elem : Ty} {nt : Nat}
    {tloc : Loc} {sb : Option Loc} {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {old : Array GoValue} {bk : GoValue}
    {env : LocalEnv} {k : GoLean.Sym.Cont symDom}
    {ch ch' : Choices} {extra : Nat}
    (hfull : cap < len + 1) (hec : elen ≤ ecap)
    (hvalidO : validateSlice ⟨sb, off, len, cap⟩ = .ok ())
    (hvisE : sliceVisibleValues (γS ρ σ S) ⟨some eb, eoff, elen, ecap⟩
      = .ok #[w])
    (hvisO : sliceVisibleValues (γS ρ σ S) ⟨sb, off, len, cap⟩ = .ok old)
    (hcons : ch.consume (appendSpillWidth cap (len + 1)) = (extra, ch'))
    (hbuild : buildAppendBackingValue (γS ρ σ S) elem old #[w]
        (appendRealizedCap cap (len + 1) extra) = .ok bk)
    (htgt : storeLoc { γS ρ σ S with
          heap := GoCore.Heap.set (γS ρ σ S).heap (.base ⟨(γS ρ σ S).nextAddr⟩)
            ⟨some (.array (appendRealizedCap cap (len + 1) extra) elem), bk⟩,
          nextAddr := (γS ρ σ S).nextAddr + 1 } tloc
        (.slice ⟨some (.base ⟨(γS ρ σ S).nextAddr⟩), 0, len + 1,
          appendRealizedCap cap (len + 1) extra⟩)
      = .ok (γS ρ σ S₂)) :
    stepFn (γS ρ σ S)
      (γC ρ (.retV (.slice ⟨some eb, eoff, elen, ecap⟩)
        (.stmtOpK (.appendSlice elem) nt
          [.slice ⟨sb, off, len, cap⟩, .addr tloc] [] env k))) ch
      = .ok (γC ρ (.next k), γS ρ σ S₂, ch') := by
  have happ := applyStmtOp_append1_spill_at (σ := γS ρ σ S) (nt := nt)
    hfull hec hvalidO hvisE hvisO hcons hbuild htgt
  simp only [γC, concC, concK, concV, List.map_cons, List.map_nil]
  simp only [stepFn]
  rw [show ((GoValue.slice ⟨some eb, eoff, elen, ecap⟩) ::
        [GoValue.slice ⟨sb, off, len, cap⟩, GoValue.addr tloc]).reverse
      = [.addr tloc, .slice ⟨sb, off, len, cap⟩,
         .slice ⟨some eb, eoff, elen, ecap⟩] from rfl, happ]
  rfl

/-! ## §3.3 discharge witness — the transport instantiated on a
concrete two-cell state (a nil `[]uint64` grown by one element), every
premise discharged; #eval-checked in `artifacts/probe/HhU10Probe3.lean`
before these `rfl`s were asked of the kernel. -/

private def spillWitS : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨1⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64]))],
    nextAddr := 2 }

private def spillWitS₂ : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨2⟩), 0, 1, 4⟩)),
      (.base ⟨1⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 4 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 0) .uint64,
                  .int (.lit 0) .uint64, .int (.lit 0) .uint64]))],
    nextAddr := 3 }

/-- The witness: at the empty-stream head choice (extra 0, the
growth-formula capacity 4), the spill step crosses and lands at the
constructed mirror image. -/
theorem stepFn_appendSpill_transport_witness (ρ : Valuation)
    (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ spillWitS)
      (γC ρ (.retV (.slice ⟨some (.base ⟨1⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice (.int .uint64)) 1
          [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨0⟩)] [] [] .stop)))
      (0 :: rest)
      = .ok (γC ρ (.next .stop), γS ρ σ spillWitS₂, rest) := by
  refine stepFn_appendSpill_transport ρ σ (extra := 0)
    (by decide) (by decide) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)

/-! ## The IN-PLACE one-element append (A4-U17 — the atom-re-read
crossing's third instance, the U12 ledger row's lift threshold)

**LINEAGE: the same classic as the two transports above — symbolic
execution crossing a machine step the mirror cannot mirror — here at
the CAPACITY-SUFFICIENT appendSlice branch** (deterministic: no choice
consumed, no allocation). The motivating shape (sL×MsgBeat, first
consumer): a handler's SECOND `r.msgs = append(r.msgs, m)` re-reads
the FIRST append's spilled handle, which rides as a valuation atom —
the mirror quits at `asSlice` on the atom, and the U12 watch-item
("a cap-consuming re-read between spills is NOT choice-independent")
fires: whether this branch is taken depends on the earlier spill's
realized capacity, so the consumer carries a `len + 1 ≤ cap` premise
that is a CHOICE-VALUE side condition at its fixture (e.g.
`2 ≤ hhCap c₄`; the complement — a re-spill — is a different,
separately-censused family). Further consumers: every multi-send arm
(the MsgApp broadcast arms append once per peer). -/

/-- `normalizeListWith` over the reduced catch-all (pointer-typed
elements normalize by `pure`) is the identity, listwise. -/
private theorem normalizeListWith_ok_id (l : List GoValue) :
    normalizeListWith (fun v => (Except.ok v : Except GoError GoValue)) l
      = .ok ⟨l⟩ := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
      simp [normalizeListWith, ih, Bind.bind, Except.bind, pure, Except.pure]

/-- **The spilled-backing second write** (the in-place transport's
`hst1` discharge at a SYMBOLIC capacity `n`): a backing cell born by a
one-element spill (`[v₀]` + default padding, declared `.array n
(.pointer pt)`) takes the second element at index 1, `2 ≤ n` — the
padding peels one `.nil`, pointer-typed re-normalization is the
catch-all identity. General in the pointee and both elements; further
consumers: every k-th in-place append re-read (the MsgApp broadcast
arms) generalizes this k = 1 form on demand. -/
theorem storeLoc_spilled_backing_index1 {σ : ExecState} {b : Addr}
    {n : Nat} {pt : Ty} {v₀ w : GoValue}
    (hn : 2 ≤ n)
    (hcw : coerceStoredValue .nil w = .ok w)
    (hlook : GoCore.Heap.lookup σ.heap (.base b)
      = some ⟨some (.array n (.pointer pt)),
          .array ⟨[v₀] ++ List.replicate (n - 1) .nil⟩⟩) :
    storeLoc σ (.index (.base b) 1) w
      = .ok ({ σ with
                heap := GoCore.Heap.set σ.heap (.base b)
                  (⟨some (.array n (.pointer pt)),
                    .array ⟨[v₀, w] ++ List.replicate (n - 2) .nil⟩⟩ : GoCore.HeapCell) }) := by
  have hpeel : List.replicate (n - 1) (GoValue.nil)
      = .nil :: List.replicate (n - 2) .nil := by
    rw [show n - 1 = (n - 2) + 1 by omega, List.replicate_succ]
  have hset : ([v₀] ++ List.replicate (n - 1) (GoValue.nil)).set 1 w
      = [v₀, w] ++ List.replicate (n - 2) .nil := by
    rw [hpeel]; rfl
  have hget : ([v₀] ++ List.replicate (n - 1) (GoValue.nil))[1]?
      = some .nil := by
    rw [hpeel]; rfl
  have hlen : ([v₀] ++ List.replicate (n - 1) (GoValue.nil)).length = n := by
    simp [List.length_replicate]; omega
  simp only [storeLoc, loadLoc, hlook, Bind.bind, Except.bind, pure,
    Except.pure]
  have hset' : arraySet ⟨[v₀] ++ List.replicate (n - 1) GoValue.nil⟩ 1 w
      = .ok ⟨[v₀, w] ++ List.replicate (n - 2) GoValue.nil⟩ := by
    simp only [arraySet, arrayIndexNat, Bind.bind, Except.bind, pure,
      Except.pure]
    rw [if_neg (by decide)]
    simp only [Int.toNat_one, List.size_toArray, hlen]
    rw [if_pos (by omega)]
    simp only [List.getElem?_toArray, hget, hcw, Array.set!,
      Array.setIfInBounds, List.size_toArray, hlen]
    rw [dif_pos (by omega)]
    simp only [List.set_toArray, hset]
  simp only [hset']
  have hnorm : normalizeValueForTy σ (.array n (.pointer pt))
      (.array ⟨[v₀, w] ++ List.replicate (n - 2) GoValue.nil⟩)
      = .ok (.array ⟨[v₀, w] ++ List.replicate (n - 2) GoValue.nil⟩) := by
    rw [normalizeValueForTy,
      show typeResolutionFuel = 1023 + 1 from rfl]
    simp only [normalizeValueForTyFuel, List.size_toArray]
    rw [if_neg (by
      simp only [List.length_append, List.length_replicate,
        List.length_cons, List.length_nil, bne_iff_ne, ne_eq]
      omega)]
    simp only [pure, Except.pure, normalizeListWith_ok_id, Bind.bind,
      Except.bind, Functor.map, Except.map]
  simp only [hnorm]

/-- The in-place apply: one appended element into a `some`-base handle
with spare capacity — one `storeLoc` into the backing at index
`off + len`, one handle write `len + 1` to the target; choices ride
untouched. -/
theorem applyStmtOp_append1_inplace_at {σ σ₁ σ₂ : ExecState} {elem : Ty}
    {nt : Nat} {tloc : Loc} {b : Loc} {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {ch : Choices}
    (hfits : len + 1 ≤ cap) (hec : elen ≤ ecap)
    (hvisE : sliceVisibleValues σ ⟨some eb, eoff, elen, ecap⟩ = .ok #[w])
    (hst1 : storeLoc σ (.index b (Int.ofNat (off + len))) w = .ok σ₁)
    (hst2 : storeLoc σ₁ tloc (.slice ⟨some b, off, len + 1, cap⟩) = .ok σ₂) :
    applyStmtOp σ ch (.appendSlice elem) nt
      [.addr tloc, .slice ⟨some b, off, len, cap⟩,
       .slice ⟨some eb, eoff, elen, ecap⟩]
      = .ok (σ₂, ch) := by
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure,
    validateSlice_some_ok (Nat.le_of_succ_le hfits),
    validateSlice_some_ok hec, hvisE]
  rw [if_pos (by simpa using hfits)]
  rw [← Array.forIn_toList,
    show (#[w] : Array GoValue).toList = [w] from rfl,
    List.forIn_cons]
  simp only [Nat.add_zero, hst1, Bind.bind, Except.bind, pure, Except.pure,
    List.forIn_nil]
  rw [show (#[w] : Array GoValue).size = 1 from rfl, hst2]

/-- **THE IN-PLACE APPEND TRANSPORT**: the capacity-sufficient append
step at a γ-image — the old handle enters as a general mirror value
(`oldv`, an ATOM at the motivating fixture) pinned to its concrete
image by `hold`; the two `storeLoc` premises are where a consumer
discharges the backing write (index `off + len`) and the handle
write-back. No choice, no allocation; `σ₁` is the consumer-supplied
mid state (the backing written, the handle not yet). -/
theorem stepFn_appendInPlace_transport (ρ : Valuation) (σ σ₁ : ExecState)
    {S S₂ : SymState} {elem : Ty} {nt : Nat}
    {tloc : Loc} {oldv : GoLean.Sym.Value symDom} {b : Loc}
    {off len cap : Nat}
    {eb : Loc} {eoff elen ecap : Nat} {w : GoValue}
    {env : LocalEnv} {k : GoLean.Sym.Cont symDom} {ch : Choices}
    (hold : concV (symInterp ρ) oldv
      = .slice ⟨some b, off, len, cap⟩)
    (hfits : len + 1 ≤ cap) (hec : elen ≤ ecap)
    (hvisE : sliceVisibleValues (γS ρ σ S) ⟨some eb, eoff, elen, ecap⟩
      = .ok #[w])
    (hst1 : storeLoc (γS ρ σ S) (.index b (Int.ofNat (off + len))) w
      = .ok σ₁)
    (hst2 : storeLoc σ₁ tloc (.slice ⟨some b, off, len + 1, cap⟩)
      = .ok (γS ρ σ S₂)) :
    stepFn (γS ρ σ S)
      (γC ρ (.retV (.slice ⟨some eb, eoff, elen, ecap⟩)
        (.stmtOpK (.appendSlice elem) nt [oldv, .addr tloc] [] env k))) ch
      = .ok (γC ρ (.next k), γS ρ σ S₂, ch) := by
  have happ := applyStmtOp_append1_inplace_at (σ := γS ρ σ S)
    (elem := elem) (nt := nt) (ch := ch) hfits hec hvisE hst1 hst2
  simp only [γC, concC, concK, concV, List.map_cons, List.map_nil]
  rw [hold]
  simp only [stepFn]
  rw [show ((GoValue.slice ⟨some eb, eoff, elen, ecap⟩) ::
        [GoValue.slice ⟨some b, off, len, cap⟩, GoValue.addr tloc]).reverse
      = [.addr tloc, .slice ⟨some b, off, len, cap⟩,
         .slice ⟨some eb, eoff, elen, ecap⟩] from rfl, happ]
  rfl

/-! ## §3.3 discharge witness (the in-place transport instantiated on
a concrete three-cell state — a one-element `[]uint64` at cap 2 grown
in place; #eval-checked in `artifacts/probe/InPlaceDev.lean` history
before these `rfl`s were asked of the kernel). -/

private def ipWitS : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨1⟩), 0, 1, 2⟩)),
      (.base ⟨1⟩, .mk (some (.array 2 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 0) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 9) .uint64]))],
    nextAddr := 3 }

private def ipWitSmid : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨1⟩), 0, 1, 2⟩)),
      (.base ⟨1⟩, .mk (some (.array 2 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 9) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 9) .uint64]))],
    nextAddr := 3 }

private def ipWitS₂ : SymState :=
  { heap := [
      (.base ⟨0⟩, .mk (some (.slice (.int .uint64)))
        (.slice ⟨some (.base ⟨1⟩), 0, 2, 2⟩)),
      (.base ⟨1⟩, .mk (some (.array 2 (.int .uint64)))
        (.array #[.int (.lit 7) .uint64, .int (.lit 9) .uint64])),
      (.base ⟨2⟩, .mk (some (.array 1 (.int .uint64)))
        (.array #[.int (.lit 9) .uint64]))],
    nextAddr := 3 }

/-- The witness: every premise discharged on the concrete cells; the
stream rides untouched (the in-place branch's own `ch`-invariance). -/
theorem stepFn_appendInPlace_transport_witness (ρ : Valuation)
    (σ : ExecState) (ch : Choices) :
    stepFn (γS ρ σ ipWitS)
      (γC ρ (.retV (.slice ⟨some (.base ⟨2⟩), 0, 1, 1⟩)
        (.stmtOpK (.appendSlice (.int .uint64)) 1
          [.slice ⟨some (.base ⟨1⟩), 0, 1, 2⟩, .addr (.base ⟨0⟩)] [] [] .stop)))
      ch
      = .ok (γC ρ (.next .stop), γS ρ σ ipWitS₂, ch) := by
  refine stepFn_appendInPlace_transport ρ σ (γS ρ σ ipWitSmid)
    (by with_unfolding_all rfl)
    (by decide) (by decide)
    (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)

end GoLean.Sym
