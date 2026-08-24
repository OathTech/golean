import GoLean.GoCore.Ops
import GoLeanProofs.Frame.Sim
import GoLeanProofs.Frame.HeapOps
import GoLeanProofs.Frame.Threshold

/-!
# The field-lens layer (campaign Arc 4, A4-U8 slice A: combinators + L1 + L4)

**LINEAGE (clever-tricks doctrine): Perennial's `Access`/`AccessStrict`
field lenses (`deps/perennial new/golang/theory/mem.v:78-130` — O'Hearn-style
focusing, "P focuses to A, restoring A' yields P'", consumed by
`tac_wp_load`/`tac_wp_store`) + goose proofgen's generated per-field
instances (`deps/goose/proofgen/tmpl/types.tmpl:65-77`). Our carrier is
FIRST-ORDER — `Option` readers over `ExecState`, not iProp points-to —
so the pattern ports as one shared reader-combinator set + per-field LAW
instances discharged by rewriting (`Specs/Raft/LensInst.lean`); a missing
instance fails loudly at the proof, mirroring `mem.v:164`'s
footprint-not-covered error. Design of record:
`docs/2026-08-24_campaign-arc4-lens-design.md`.**

LAYERING: this is GENERAL proof infrastructure (the design §6 boundary):
it imports machine vocabulary (`GoCore`) and the Frame layer only —
no Sym, no `Specs.*`. Statement modules never import it. The target
half (per-field instances at the pinned twin tables) lives in
`Specs/Raft/LensInst.lean`.

Division of labor (design §2, binding): TableExt computes whole-struct
stores INSIDE windows (untouched); the lens reasons AT window
boundaries — equation conclusions, absState definitions, preservation
arguments.

The law families:
- **L1 (focus)**: a whole-struct cell fact yields the `fieldRead` value
  (`fieldRead_of_cell`, `fieldOfValue_struct`).
- **L2 (store-miss, the frame half)** and **L3 (store-hit)**: slice B,
  below — the machine's field-store path (`storeLoc` through the
  whole-struct re-normalization at the cell's declared type)
  characterized per FIELD.
- **L4 (rename)**: every reader transports along `FrameSim` to the
  relocated placement (`fieldRead_ren`, `fieldReadU64_ren`,
  `sliceRead_ren`) — ONE lemma set covers every lens-stated projection,
  retiring the per-reader hand `_ren` pattern (`absRaftNode_ren`'s
  shape) for new readers.
-/

namespace GoLean.Lens

open GoLean GoLean.GoCore GoLean.Frame

/-! ## Scalar decoders (fail closed) -/

/-- A `uint64`-kinded machine int, or nothing. -/
def readU64 : GoValue → Option Int
  | .int v .uint64 => some v
  | _ => none

/-- A machine int at an exact kind, or nothing. -/
def readIntK (k : IntKind) : GoValue → Option Int
  | .int v k' => if k' == k then some v else none
  | _ => none

/-- A machine bool, or nothing. -/
def readBool : GoValue → Option Bool
  | .bool b => some b
  | _ => none

/-! ## The reader combinators -/

/-- Field readout of a struct VALUE (fail closed: wrong shape or wrong
tag → `none`). The value-level half of `fieldRead`; also the reader for
EMBEDDED struct fields (`raftLog.unstable` — one cell hop, then value
projections). -/
def fieldOfValue (v : GoValue) (tid : TypeId) (f : String) : Option GoValue :=
  match v with
  | .struct tid' fs => if tid' == tid then StructFields.lookup fs f else none
  | _ => none

/-- Field readout at a base cell (fail closed). -/
def fieldRead (σ : ExecState) (a : Addr) (tid : TypeId) (f : String) :
    Option GoValue :=
  (Heap.lookup σ.heap (.base a)).bind fun cell => fieldOfValue cell.value tid f

/-- `fieldRead` + `uint64` decode: the projection-facing form. -/
def fieldReadU64 (σ : ExecState) (a : Addr) (tid : TypeId) (f : String) :
    Option Int :=
  (fieldRead σ a tid f).bind readU64

/-- The element walk of `sliceRead`: `n` elements of the backing array
from index `i`, each decoded by `elem` (fail closed on a short array or
a failing decode). Generalizes `absEntsFrom` (AbsState.lean, U4). -/
def sliceElems {α : Type} (σ : ExecState) (vs : Array GoValue)
    (elem : ExecState → GoValue → Option α) : Nat → Nat → Option (List α)
  | _, 0 => some []
  | i, n + 1 => do
      let v ← vs[i]?
      let x ← elem σ v
      let rest ← sliceElems σ vs elem (i + 1) n
      pure (x :: rest)

/-- Slice readout through a slice value: backing-array walk over
`[offset, offset+len)`, element decode passed in. A NIL slice of
length 0 reads as the empty list ([AGENT], design §4: `r.msgs` is nil
at init and abstracts to the empty outbox — Go's nil slice IS the
empty slice); a nil base with nonzero length is malformed → `none`. -/
def sliceRead {α : Type} (σ : ExecState) (base : GoValue)
    (elem : ExecState → GoValue → Option α) : Option (List α) :=
  match base with
  | .slice ⟨some b, off, len, _⟩ =>
      (Heap.lookup σ.heap b).bind fun cell =>
        match cell.value with
        | .array vs => sliceElems σ vs elem off len
        | _ => none
  | .slice ⟨none, _, len, _⟩ => if len == 0 then some [] else none
  | _ => none

/-- The declared type of a struct field, read from a type environment
(the instance layer's search key: per-field instances pin its value at
the twin tables). -/
def fieldTy? : List FieldDef → String → Option Ty
  | [], _ => none
  | fd :: rest, n => if fd.name == n then some fd.typ else fieldTy? rest n

/-- `fieldTy?` through the environment lookup: the one-call form. -/
def structFieldTy (types : TypeEnv) (tid : TypeId) (f : String) : Option Ty :=
  match TypeEnv.lookup types tid with
  | some (.struct fds) => fieldTy? fds.toList f
  | _ => none

/-! ## L1 — focus -/

theorem fieldOfValue_struct (tid : TypeId) (fs : Array (String × GoValue))
    (f : String) :
    fieldOfValue (.struct tid fs) tid f = StructFields.lookup fs f := by
  simp [fieldOfValue]

theorem fieldRead_of_cell {σ : ExecState} {a : Addr} {cell : HeapCell}
    (hc : Heap.lookup σ.heap (.base a) = some cell)
    (tid : TypeId) (f : String) :
    fieldRead σ a tid f = fieldOfValue cell.value tid f := by
  simp [fieldRead, hc]

theorem fieldRead_of_struct {σ : ExecState} {a : Addr} {cell : HeapCell}
    {tid : TypeId} {fs : Array (String × GoValue)}
    (hc : Heap.lookup σ.heap (.base a) = some cell)
    (hv : cell.value = .struct tid fs) (f : String) :
    fieldRead σ a tid f = StructFields.lookup fs f := by
  rw [fieldRead_of_cell hc, hv, fieldOfValue_struct]

/-! ## L4 — rename transport (`FrameSim` placement invariance) -/

theorem readU64_ren (r : Nat → Nat) (v : GoValue) :
    readU64 (renameValue r v) = readU64 v := by
  cases v <;> simp [renameValue, readU64]

theorem readIntK_ren (r : Nat → Nat) (k : IntKind) (v : GoValue) :
    readIntK k (renameValue r v) = readIntK k v := by
  cases v <;> simp [renameValue, readIntK]

theorem readBool_ren (r : Nat → Nat) (v : GoValue) :
    readBool (renameValue r v) = readBool v := by
  cases v <;> simp [renameValue, readBool]

theorem fieldOfValue_ren (r : Nat → Nat) (v : GoValue) (tid : TypeId)
    (f : String) :
    fieldOfValue (renameValue r v) tid f
      = (fieldOfValue v tid f).map (renameValue r) := by
  cases v <;> simp only [renameValue, fieldOfValue, Option.map_none]
  case struct tid' fs =>
    by_cases h : (tid' == tid) = true
    · simp only [if_pos h, structFieldsLookup_ren]
    · simp [h]

/-- **The L4 workhorse**: a successful `fieldRead` transports to the
relocated placement, the value renamed. -/
theorem fieldRead_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {tid : TypeId} {f : String} {v : GoValue}
    (h : fieldRead σ a tid f = some v) :
    fieldRead σF ⟨r a.id⟩ tid f = some (renameValue r v) := by
  unfold fieldRead at h ⊢
  cases hc : Heap.lookup σ.heap (.base a) with
  | none => rw [hc] at h; cases h
  | some cell =>
      rw [hc] at h
      have hcF := hF.lookup_some (l := .base a) hc
      rw [show renameLoc r (.base a) = Loc.base ⟨r a.id⟩ from rfl] at hcF
      rw [hcF]
      show fieldOfValue (renameCell r cell).value tid f = _
      rw [show (renameCell r cell).value = renameValue r cell.value from rfl,
        fieldOfValue_ren]
      simp only [Option.bind_some] at h
      rw [h]
      rfl

/-- Scalar readouts are placement-INDEPENDENT: `fieldReadU64` transports
verbatim (its output is loc-free). -/
theorem fieldReadU64_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {tid : TypeId} {f : String} {n : Int}
    (h : fieldReadU64 σ a tid f = some n) :
    fieldReadU64 σF ⟨r a.id⟩ tid f = some n := by
  unfold fieldReadU64 at h ⊢
  cases hv : fieldRead σ a tid f with
  | none => rw [hv] at h; cases h
  | some v =>
      rw [hv] at h
      rw [fieldRead_ren hF hv]
      simpa [readU64_ren] using h

theorem sliceElems_ren {r : Nat → Nat} {σ σF : ExecState} {α : Type}
    {elem : ExecState → GoValue → Option α}
    (helem : ∀ v x, elem σ v = some x → elem σF (renameValue r v) = some x)
    (vs : Array GoValue) :
    ∀ i n xs, sliceElems σ vs elem i n = some xs →
      sliceElems σF ((renameValueList r vs.toList).toArray) elem i n
        = some xs := by
  intro i n
  induction n generalizing i with
  | zero => intro xs h; exact h
  | succ n ih =>
      intro xs h
      unfold sliceElems at h ⊢
      cases hv : vs[i]? with
      | none => rw [hv] at h; cases h
      | some v =>
          rw [hv] at h
          rw [renamedArray_getElem?, hv]
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
            at h ⊢
          cases hx : elem σ v with
          | none => rw [hx] at h; cases h
          | some x =>
              rw [hx] at h
              rw [helem v x hx]
              simp only [Option.bind_some] at h ⊢
              cases hrest : sliceElems σ vs elem (i + 1) n with
              | none => rw [hrest] at h; cases h
              | some rest =>
                  rw [hrest] at h
                  rw [ih (i + 1) rest hrest]
                  exact h

/-- **The L4 slice law**: a successful loc-FREE slice readout (the
element decoder produces placement-independent abstractions and itself
transports — e.g. any composition of the scalar decoders and
`fieldRead_ren`-backed reads) transports verbatim. -/
theorem sliceRead_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {α : Type} {elem : ExecState → GoValue → Option α}
    (helem : ∀ v x, elem σ v = some x → elem σF (renameValue r v) = some x)
    {base : GoValue} {xs : List α}
    (h : sliceRead σ base elem = some xs) :
    sliceRead σF (renameValue r base) elem = some xs := by
  cases base <;> simp only [sliceRead, renameValue] at h ⊢ <;> try exact h
  case slice sv =>
    obtain ⟨ob, off, len, cap⟩ := sv
    cases ob with
    | none => simpa using h
    | some b =>
        simp only [Option.map_some] at h ⊢
        cases hc : Heap.lookup σ.heap b with
        | none => rw [hc] at h; cases h
        | some cell =>
            rw [hc] at h
            have hcF := hF.lookup_some hc
            rw [hcF]
            simp only [Option.bind_some] at h ⊢
            rw [show (renameCell r cell).value = renameValue r cell.value
              from rfl]
            cases hcv : cell.value <;> rw [hcv] at h <;>
              simp only [renameValue] at * <;> try cases h
            case array vs =>
              exact sliceElems_ren helem vs off len xs h

/-! ## L2/L3 infrastructure — `StructFields` characterized at the list
level (slice B; the machine's field-store path decomposes through
`StructFields.set` and the whole-struct re-normalization
`normalizeFieldsWith`, both characterized per FIELD here) -/

/-- List-level field lookup (first occurrence wins — mirrors
`StructFields.lookup`'s fold). -/
def lookupL : List (String × GoValue) → String → Option GoValue
  | [], _ => none
  | (n, v) :: rest, needle =>
      if n == needle then some v else lookupL rest needle

/-- List-level field update (every occurrence — mirrors
`StructFields.set`'s loop). -/
def setL (needle : String) (v : GoValue) :
    List (String × GoValue) → List (String × GoValue)
  | [] => []
  | (n, old) :: rest => (n, if n == needle then v else old) :: setL needle v rest

/-- Does the field list carry the name? (`StructFields.set`'s found
flag.) -/
def hasName (needle : String) : List (String × GoValue) → Bool
  | [] => false
  | (n, _) :: rest => n == needle || hasName needle rest

private theorem foldl_some_fixed {α β : Type}
    (stepf : Option α → β → Option α)
    (hstep : ∀ v x, stepf (some v) x = some v) (v : α) :
    ∀ l : List β, l.foldl stepf (some v) = some v
  | [] => rfl
  | _ :: rest => by
      rw [List.foldl_cons, hstep]
      exact foldl_some_fixed stepf hstep v rest

private theorem push_append_toArray {α : Type} (out : Array α) (x : α)
    (l : List α) : out.push x ++ l.toArray = out ++ (x :: l).toArray := by
  apply Array.ext'
  simp

/-- `StructFields.lookup` IS the list-level lookup. -/
theorem structFieldsLookup_eq (fs : Array (String × GoValue)) (n : String) :
    StructFields.lookup fs n = lookupL fs.toList n := by
  unfold StructFields.lookup
  dsimp only
  rw [← Array.foldl_toList]
  induction fs.toList with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨pn, pv⟩ := p
      rw [List.foldl_cons]
      dsimp only
      by_cases hn : (pn == n) = true
      · rw [if_pos hn]
        simp only [lookupL, hn, if_pos]
        exact foldl_some_fixed _ (fun _ _ => rfl) pv rest
      · rw [if_neg hn, ih]
        simp [lookupL, hn]

private theorem setLoop (needle : String) (v : GoValue) :
    ∀ (l : List (String × GoValue)) (found : Bool)
      (out : Array (String × GoValue)),
      (forIn l (MProd.mk found out) (fun x r =>
          if (x.fst == needle) = true then
            pure (ForInStep.yield ⟨true, r.snd.push (x.fst, v)⟩)
          else
            pure (ForInStep.yield ⟨r.fst, r.snd.push (x.fst, x.snd)⟩)) :
        Except GoError (MProd Bool (Array (String × GoValue))))
      = pure ⟨found || hasName needle l, out ++ (setL needle v l).toArray⟩
  | [], found, out => by simp [hasName, setL]
  | (n, w) :: rest, found, out => by
      rw [List.forIn_cons]
      by_cases hn : (n == needle) = true
      · simp only [hn, ↓reduceIte, pure_bind]
        rw [setLoop needle v rest true (out.push (n, v)),
          push_append_toArray]
        simp [hasName, setL, hn]
      · simp only [hn, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [setLoop needle v rest found (out.push (n, w)),
          push_append_toArray]
        simp [hasName, setL, hn]

/-- `StructFields.set` characterized: the list-level update when the
name exists, the fail-closed stuck otherwise. -/
theorem structFieldsSet_eq (fields : Array (String × GoValue))
    (needle : String) (v : GoValue) :
    StructFields.set fields needle v
      = if hasName needle fields.toList
        then .ok (setL needle v fields.toList).toArray
        else .error (.stuck s!"unknown GoCore struct field: {needle}") := by
  unfold StructFields.set
  dsimp only
  rw [← Array.forIn_toList]
  simp only [pure_bind]
  rw [setLoop needle v fields.toList false #[]]
  simp only [pure_bind, Bool.false_or]
  by_cases hf : hasName needle fields.toList
  · simp [hf]
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rfl

/-! ### `setL`/`lookupL` commutation -/

theorem lookupL_setL_ne (needle : String) (v : GoValue) (f : String)
    (hne : f ≠ needle) :
    ∀ l : List (String × GoValue), lookupL (setL needle v l) f = lookupL l f
  | [] => rfl
  | (n, old) :: rest => by
      simp only [setL, lookupL]
      by_cases hn : (n == f) = true
      · have hnn : (n == needle) = false := by
          have hnf : n = f := eq_of_beq hn
          subst hnf
          simpa using hne
        rw [if_pos hn, if_pos hn, hnn]
        simp
      · rw [if_neg hn, if_neg hn]
        exact lookupL_setL_ne needle v f hne rest

theorem lookupL_setL_hit (needle : String) (v : GoValue) :
    ∀ l : List (String × GoValue), hasName needle l = true →
      lookupL (setL needle v l) needle = some v
  | [], h => by simp [hasName] at h
  | (n, old) :: rest, h => by
      simp only [setL, lookupL]
      by_cases hn : (n == needle) = true
      · rw [if_pos hn, hn]
        simp
      · rw [if_neg hn]
        apply lookupL_setL_hit needle v rest
        simpa [hasName, hn] using h

/-! ### `normalizeFieldsWith` characterized per field: the walk is
FIELD-POINTWISE (the L2 kill-point check, discharged by proof — this
lemma existing IS the "normalization is field-pointwise" fact) -/

theorem normalizeFieldsWith_lookup
    (nf : Ty → GoValue → Except GoError GoValue) :
    ∀ (fds : List FieldDef) (fs : List (String × GoValue))
      (out : Array (String × GoValue)),
      normalizeFieldsWith nf fds fs = .ok out →
      ∀ (f : String) (τ : Ty) (v w : GoValue),
        fieldTy? fds f = some τ → lookupL fs f = some v →
        nf τ v = .ok w → lookupL out.toList f = some w := by
  intro fds
  induction fds with
  | nil =>
      intro fs out h f τ v w hty hv hw
      simp [fieldTy?] at hty
  | cons fd rest ih =>
      intro fs out h f τ v w hty hv hw
      cases fs with
      | nil => simp [lookupL] at hv
      | cons p prest =>
          obtain ⟨pn, pv⟩ := p
          unfold normalizeFieldsWith at h
          by_cases hpn : (pn != fd.name) = true
          · rw [if_pos hpn] at h
            cases h
          · rw [if_neg hpn] at h
            have hpneq : pn = fd.name := by
              have : (pn == fd.name) = true := by
                simpa [bne] using hpn
              exact eq_of_beq this
            replace h : (nf fd.typ pv >>= fun head =>
                normalizeFieldsWith nf rest prest >>= fun tail =>
                pure (#[(fd.name, head)] ++ tail)) = .ok out := h
            cases hhead : nf fd.typ pv with
            | error e =>
                rw [hhead] at h
                replace h : (Except.error e :
                    Except GoError (Array (String × GoValue))) = .ok out := h
                cases h
            | ok head =>
                rw [hhead] at h
                replace h : (normalizeFieldsWith nf rest prest >>= fun tail =>
                    pure (#[(fd.name, head)] ++ tail)) = .ok out := h
                cases htail : normalizeFieldsWith nf rest prest with
                | error e =>
                    rw [htail] at h
                    replace h : (Except.error e :
                        Except GoError (Array (String × GoValue))) = .ok out := h
                    cases h
                | ok tail =>
                    rw [htail] at h
                    replace h : Except.ok (#[(fd.name, head)] ++ tail)
                        = .ok out := h
                    have hout : #[(fd.name, head)] ++ tail = out :=
                      Except.ok.inj h
                    subst hout
                    have houtL : (#[(fd.name, head)] ++ tail).toList
                        = (fd.name, head) :: tail.toList := by
                      simp
                    rw [houtL]
                    by_cases hf : (fd.name == f) = true
                    · -- the hit field
                      have hτ : τ = fd.typ := by
                        simp only [fieldTy?, hf, if_pos] at hty
                        exact (Option.some_inj.mp hty).symm
                      have hvv : v = pv := by
                        have hpnf : (pn == f) = true := by
                          rw [hpneq]; exact hf
                        simp only [lookupL, hpnf, if_pos] at hv
                        exact (Option.some_inj.mp hv).symm
                      subst hτ; subst hvv
                      have hwh : head = w := by
                        rw [hhead] at hw
                        exact Except.ok.inj hw
                      simp [lookupL, hf, hwh]
                    · -- the walk continues
                      have hpnf : (pn == f) = false := by
                        rw [hpneq]
                        simpa using hf
                      simp only [fieldTy?, hf, Bool.false_eq_true,
                        if_false] at hty
                      simp only [lookupL, hpnf, Bool.false_eq_true,
                        if_false] at hv
                      simp only [lookupL, hf, Bool.false_eq_true, if_false]
                      exact ih prest tail htail f τ v w hty hv hw

/-! ## L2/L3 — the machine's field-store path, characterized per field

The store path (`storeLoc` at a `.field` target through a `.base`
cell): load the struct, `StructFields.set` the field, store back at
the base — where the cell's DECLARED type re-normalizes the WHOLE
struct (`normalizeValueForTy` at `typeResolutionFuel = 1024`, so the
per-field normalizer runs at fuel 1023). The laws below characterize
the result per FIELD; the per-field normalization data (the `hstab`/
`hnw` premises) is discharged by the instance layer
(`Specs/Raft/LensInst.lean`) from the shape lemmas at the end of this
section. -/

/-- `Except`'s ok-bind reduction (definitional; core ships no simp
lemma for it — the Frame layer's `ExSim.bind` sidesteps it, but the
functional decomposition below wants the equation directly). -/
theorem ok_bind {α β : Type} (a : α) (f : α → Except GoError β) :
    (Except.ok a : Except GoError α) >>= f = f a := rfl

theorem error_bind {α β : Type} (e : GoError) (f : α → Except GoError β) :
    (Except.error e : Except GoError α) >>= f = .error e := rfl

theorem map_ok {α β : Type} (f : α → β) (a : α) :
    f <$> (Except.ok a : Except GoError α) = .ok (f a) := rfl

theorem map_error {α β : Type} (f : α → β) (e : GoError) :
    f <$> (Except.error e : Except GoError α) = .error e := rfl

/-- Decomposition of a successful field store through a base cell
declared at a defined struct type: the new cell value is the
field-pointwise normalization of the updated field list. -/
theorem store_field_decomp {σ σ' : ExecState} {a : Addr} {tid : TypeId}
    {g : String} {w : GoValue} {cell : HeapCell}
    {fs : Array (String × GoValue)} {fds : Array FieldDef}
    (hst : storeLoc σ (.field (.base a) tid g) w = .ok σ')
    (hc : Heap.lookup σ.heap (.base a) = some cell)
    (hv : cell.value = .struct tid fs)
    (hd : cell.declaredTy = some (.defined tid))
    (hty : TypeEnv.lookup σ.types tid = some (.struct fds)) :
    ∃ (updated nfs : Array (String × GoValue)),
      StructFields.set fs g w = .ok updated ∧
      normalizeFieldsWith (normalizeValueForTyFuel 1023 σ) fds.toList
        updated.toList = .ok nfs ∧
      σ' = { σ with heap := Heap.set σ.heap (.base a) ⟨cell.declaredTy, .struct tid nfs⟩ } := by
  have hload : loadLoc σ (.base a) = .ok (.struct tid fs) := by
    unfold loadLoc
    rw [hc]
    show Except.ok cell.value = _
    rw [hv]
  unfold storeLoc at hst
  rw [hload, ok_bind] at hst
  dsimp only at hst
  simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
    if_false, pure_bind] at hst
  cases hset : StructFields.set fs g w with
  | error e =>
      rw [hset, error_bind] at hst
      cases hst
  | ok updated =>
      rw [hset, ok_bind] at hst
      unfold storeLoc at hst
      rw [hc] at hst
      dsimp only at hst
      rw [hd] at hst
      dsimp only at hst
      unfold normalizeValueForTy typeResolutionFuel at hst
      rw [show (1024 : Nat) = 1023 + 1 from rfl] at hst
      simp only [normalizeValueForTyFuel] at hst
      rw [hty] at hst
      dsimp only at hst
      unfold normalizeStructValueWith at hst
      dsimp only at hst
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false,
        pure_bind] at hst
      by_cases hsz : (updated.size != fds.size) = true
      · rw [if_pos hsz] at hst
        rw [show (GoCore.stuck s!"struct value field count mismatch: expected {fds.size}, got {updated.size}" : Except GoError PUnit) = .error (.stuck _) from rfl] at hst
        rw [error_bind] at hst
        cases hst
      · rw [if_neg hsz] at hst
        try simp only [pure_bind] at hst
        cases hnorm : normalizeFieldsWith (normalizeValueForTyFuel 1023 σ)
            fds.toList updated.toList with
        | error e =>
            rw [hnorm, map_error, error_bind] at hst
            cases hst
        | ok nfs =>
            rw [hnorm, map_ok, ok_bind] at hst
            refine ⟨updated, nfs, rfl, hnorm, ?_⟩
            rw [hd]
            exact (Except.ok.inj hst).symm

/-- **L2 — store-miss (the frame half)**: a store to field `g` leaves
field `f ≠ g` reading its OLD value, provided that value is stable
under its own field-type normalization (free for pointer/slice/bool/
interface fields; the in-range fact for scalar fields — the shape
lemmas below). -/
theorem fieldRead_store_miss {σ σ' : ExecState} {a : Addr} {tid : TypeId}
    {g : String} {w : GoValue} {cell : HeapCell}
    {fs : Array (String × GoValue)} {fds : Array FieldDef}
    (hst : storeLoc σ (.field (.base a) tid g) w = .ok σ')
    (hc : Heap.lookup σ.heap (.base a) = some cell)
    (hv : cell.value = .struct tid fs)
    (hd : cell.declaredTy = some (.defined tid))
    (hty : TypeEnv.lookup σ.types tid = some (.struct fds))
    {f : String} (hne : f ≠ g)
    {τ : Ty} (hfty : fieldTy? fds.toList f = some τ)
    {v : GoValue} (hold : StructFields.lookup fs f = some v)
    (hstab : normalizeValueForTyFuel 1023 σ τ v = .ok v) :
    fieldRead σ' a tid f = some v := by
  obtain ⟨updated, nfs, hset, hnorm, hσ'⟩ :=
    store_field_decomp hst hc hv hd hty
  subst hσ'
  have hupd : lookupL updated.toList f = some v := by
    rw [structFieldsSet_eq] at hset
    by_cases hg : hasName g fs.toList
    · rw [if_pos hg] at hset
      have : updated = (setL g w fs.toList).toArray := by
        cases hset; rfl
      subst this
      rw [List.toList_toArray, lookupL_setL_ne g w f hne,
        ← structFieldsLookup_eq]
      exact hold
    · rw [if_neg hg] at hset
      cases hset
  have hnfs : lookupL nfs.toList f = some v :=
    normalizeFieldsWith_lookup _ fds.toList updated.toList nfs hnorm
      f τ v v hfty hupd hstab
  show fieldRead _ a tid f = some v
  rw [fieldRead]
  simp only [Heap.lookup_set_self, Option.bind_some]
  rw [fieldOfValue_struct, structFieldsLookup_eq]
  exact hnfs

/-- **L3 — store-hit**: after a successful store of `w` to field `g`,
the field reads back as `w`'s normalization at its declared field
type. -/
theorem fieldRead_store_hit {σ σ' : ExecState} {a : Addr} {tid : TypeId}
    {g : String} {w : GoValue} {cell : HeapCell}
    {fs : Array (String × GoValue)} {fds : Array FieldDef}
    (hst : storeLoc σ (.field (.base a) tid g) w = .ok σ')
    (hc : Heap.lookup σ.heap (.base a) = some cell)
    (hv : cell.value = .struct tid fs)
    (hd : cell.declaredTy = some (.defined tid))
    (hty : TypeEnv.lookup σ.types tid = some (.struct fds))
    {τ : Ty} (hfty : fieldTy? fds.toList g = some τ)
    {w' : GoValue} (hnw : normalizeValueForTyFuel 1023 σ τ w = .ok w') :
    fieldRead σ' a tid g = some w' := by
  obtain ⟨updated, nfs, hset, hnorm, hσ'⟩ :=
    store_field_decomp hst hc hv hd hty
  subst hσ'
  have hupd : lookupL updated.toList g = some w := by
    rw [structFieldsSet_eq] at hset
    by_cases hg : hasName g fs.toList
    · rw [if_pos hg] at hset
      have : updated = (setL g w fs.toList).toArray := by
        cases hset; rfl
      subst this
      rw [List.toList_toArray]
      exact lookupL_setL_hit g w fs.toList hg
    · rw [if_neg hg] at hset
      cases hset
  have hnfs : lookupL nfs.toList g = some w' :=
    normalizeFieldsWith_lookup _ fds.toList updated.toList nfs hnorm
      g τ w w' hfty hupd hnw
  show fieldRead _ a tid g = some w'
  rw [fieldRead]
  simp only [Heap.lookup_set_self, Option.bind_some]
  rw [fieldOfValue_struct, structFieldsLookup_eq]
  exact hnfs

/-! ### Per-field-TYPE normalization shape lemmas (what the instance
layer discharges `hstab`/`hnw` with; each is arm-exact against
`normalizeValueForTyFuel`) -/

/-- Pointer-typed fields normalize by the catch-all identity arm. -/
theorem norm_pointer_id (σ : ExecState) (τ : Ty) (v : GoValue) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ (.pointer τ) v = .ok v := by
  cases v <;> rfl

/-- Slice-typed fields normalize by the catch-all identity arm. -/
theorem norm_slice_id (σ : ExecState) (τ : Ty) (v : GoValue) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ (.slice τ) v = .ok v := by
  cases v <;> rfl

/-- Bool-typed fields normalize by the catch-all identity arm. -/
theorem norm_bool_id (σ : ExecState) (v : GoValue) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ .bool v = .ok v := by
  cases v <;> rfl

/-- String-typed fields normalize by the catch-all identity arm. -/
theorem norm_string_id (σ : ExecState) (v : GoValue) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ .string v = .ok v := by
  cases v <;> rfl

/-- Interface-typed fields normalize by the explicit identity arm. -/
theorem norm_interface_id (σ : ExecState) (i : TypeId) (v : GoValue)
    (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ (.interface i) v = .ok v := rfl

/-- Int-kinded fields: normalization is the kind's wrap — the identity
exactly on in-range values (the `hvote`-style side condition's home). -/
theorem norm_int_stable {kind : IntKind} {v : Int}
    (h : kind.normalize v = v) (σ : ExecState) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ (.int kind) (.int v kind)
      = .ok (.int v kind) := by
  simp [normalizeValueForTyFuel, h]

/-- Int-kinded fields, the hit form: any incoming int wraps to the
field's kind. -/
theorem norm_int_hit (kind : IntKind) (v : Int) (k' : IntKind)
    (σ : ExecState) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ (.int kind) (.int v k')
      = .ok (.int (kind.normalize v) kind) := rfl

/-- One defined-type resolution step (`type T = U` / `type T U` with a
non-struct underlying): the instance layer chains these at the pinned
table (`raft.StateType` → `.int .uint64`, one step). -/
theorem norm_defined_step {σ : ExecState} {tid : TypeId} {target : Ty}
    (h : TypeEnv.lookup σ.types tid = some (.defined target))
    (v : GoValue) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ (.defined tid) v
      = normalizeValueForTyFuel n σ target v := by
  simp [normalizeValueForTyFuel, h]

/-- The alias variant of `norm_defined_step`. -/
theorem norm_alias_step {σ : ExecState} {tid : TypeId} {target : Ty}
    (h : TypeEnv.lookup σ.types tid = some (.alias target))
    (v : GoValue) (n : Nat) :
    normalizeValueForTyFuel (n + 1) σ (.defined tid) v
      = normalizeValueForTyFuel n σ target v := by
  simp [normalizeValueForTyFuel, h]

/-! ## Discharge witnesses (non-vacuity: every law family instantiated
live on a concrete two-cell state; the L4 witness discharges the
`FrameSim` premise at the generic zero-shift seed) -/

private def wLens : ExecState :=
  { heap := [(.base ⟨0⟩,
      { declaredTy := none
        value := .struct ⟨"T"⟩
          #[("x", .int 7 .uint64), ("p", .addr (.base ⟨1⟩))] }),
     (.base ⟨1⟩,
      { declaredTy := none
        value := .array #[.int 1 .uint64, .int 2 .uint64] })]
    nextAddr := 2 }

theorem lens_witness_L1 : fieldReadU64 wLens ⟨0⟩ ⟨"T"⟩ "x" = some 7 := by rfl

theorem lens_witness_slice :
    sliceRead wLens (.slice ⟨some (.base ⟨1⟩), 0, 2, 2⟩) (fun _ v => readU64 v)
      = some [1, 2] := by rfl

theorem lens_witness_nilslice :
    sliceRead wLens (.slice ⟨none, 0, 0, 0⟩) (fun _ v => readU64 v)
      = some [] := by rfl

theorem lens_witness_L4 :
    fieldReadU64 wLens ⟨ρT 2 0 0⟩ ⟨"T"⟩ "x" = some 7 :=
  fieldReadU64_ren (frameSim_seed rfl (fun _ hf => by simp [wLens] at hf))
    lens_witness_L1

/-! ### L2/L3 witnesses: a real machine store on a typed cell, both
laws applied with every premise discharged concretely -/

private def wTid : TypeId := ⟨"W"⟩
private def wStoreCell : HeapCell :=
  { declaredTy := some (.defined wTid)
    value := .struct wTid
      #[("x", .int 7 .uint64), ("p", .addr (.base ⟨1⟩))] }
private def wStore : ExecState :=
  { types := [(wTid, .struct
      #[⟨"x", .int .uint64, false⟩, ⟨"p", .pointer (.int .uint64), false⟩])]
    heap := [(.base ⟨0⟩, wStoreCell)]
    nextAddr := 2 }

private def wStoreCell' : HeapCell :=
  ⟨some (.defined wTid),
    .struct wTid #[("x", .int 9 .uint64), ("p", .addr (.base ⟨1⟩))]⟩

theorem lens_witness_store_ok :
    storeLoc wStore (.field (.base ⟨0⟩) wTid "x") (.int 9 .uint64)
      = .ok { wStore with
              heap := Heap.set wStore.heap (.base ⟨0⟩) wStoreCell' } := by
  with_unfolding_all rfl

theorem lens_witness_L2L3 :
    ∀ σ' : ExecState,
      storeLoc wStore (.field (.base ⟨0⟩) wTid "x") (.int 9 .uint64)
        = .ok σ' →
      fieldRead σ' ⟨0⟩ wTid "x" = some (.int 9 .uint64)
      ∧ fieldRead σ' ⟨0⟩ wTid "p" = some (.addr (.base ⟨1⟩)) := by
  intro σ' hst
  refine ⟨?_, ?_⟩
  · exact fieldRead_store_hit hst rfl rfl rfl rfl rfl rfl
  · exact fieldRead_store_miss hst rfl rfl rfl rfl (by decide) rfl rfl rfl

end GoLean.Lens
