import GoLean.GoCore.StepFn

/-! # The choice-erased canonical state form (`CForm`) and the
latitude equivalence `~` (campaign lane arc4c, unit SP1)

**What this module is.** The CANONICAL FORM of a machine state
relative to a root set: a total, fail-closed, executable
canonicalization that quotients exactly the two sequential latitude
axes the machine's draw sites can move —

- **relocation** (allocation placement): heap addresses are replaced
  by first-visit discovery indices over a deterministic
  structure-directed traversal from the roots, and unreachable cells
  (allocation garbage — retired spill backings, temporaries) are
  dropped;
- **capacity slack** (`appendSpill` latitude): slice handles are
  emitted WITHOUT their `cap` field, backing-array cells are trimmed
  to the maximal window any reachable handle views, and the trimmed
  tail is checked zero-like (spill backings pad with `defaultValue`s
  — `buildAppendBackingValue`, Ops.lean — so on machine-built states
  the check passes; a non-zero-like tail fails CLOSED by keeping the
  full array and raising a flag, so the quotient never equates states
  that differ in observable content);

plus the one canonicalization Go itself performs at the `mapIter`
site's consumers: `mapData` entries are emitted in sorted scalar-key
order (fail-closed: non-scalar keys keep entry order and raise a
flag).

Two states are **latitude-equivalent** (`CEquiv`, the unit's `~`)
when their canonical forms at corresponding roots are EQUAL. By
construction `~` is an equivalence, and any reader that factors
through the canonical form is `~`-invariant definitionally (the
representation-engineering heuristic, campaign log [USER] 2026-08-27:
invariance is bought at the representation, not proved per reader).

**Forward compatibility (standing decision, campaign log [USER]
2026-08-27 — the symbolic semantics).** `CForm` is deliberately named
and shaped as the FUTURE STATE SPACE of the choice-erasure symbolic
semantics (`opsem ↔ relational ← symbolic-with-choice-erasure`):
canonical ids are CompCert-style abstract block names (allocation-
choice erasure — the flagship lineage), capacity slack and
canonicalized iteration draws are the two axes ours adds. No
semantics packaging happens in this unit (redesign §7 middle path):
this module ships the state space and the equivalence only.

**LINEAGE:** bisimulation up-to an erasure quotient (CompCert memory
model block-naming; data independence; the project's own quotient
theorem note). The canonicalizer itself is a garbage-collected-state
serialization — a standard heap-isomorphism canonical labeling
(first-visit DFS numbering).

**Totality:** fully total, kernel-reducible code. All recursions are fueled
(the `GoValue.eqb` de-WF recipe); fuel exhaustion raises a fail-closed
flag in the output form (`CForm.flags`), so an exhausted
canonicalization can never silently equate two states: flags are part
of the form, and clean witnesses check `flags = []`.

**Placement (arc-4 landing fix round, 2026-08-26):** this module and
`ChoiceInv` live under `Frame/` as the choice-erasure layer of the
frame/placement story; their namespace is `GoLean.Frame.ChoiceErase`
(was the directory-inconsistent `GoLean.ChoiceErase` — a landing-audit
coherence finding). Curated Audit pins: `Audit/ChoiceInv.lean`. -/

namespace GoLean.Frame.ChoiceErase

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## The canonical value/cell/form types -/

/-- A canonical (choice-erased) value: `GoValue` with heap addresses
replaced by discovery ids, slice caps erased, and map data sorted.
`badLoc` is the fail-closed image of the loc shapes the canonicalizer
does not cover (non-`.base` heap references) — it always co-occurs
with a flag. -/
inductive CVal where
  | unit
  | bool (b : Bool)
  | int (v : Int) (k : GoCore.IntKind)
  | float (bits : Nat) (k : GoCore.FloatKind)
  | str (bytes : Array UInt8)
  | ref (id : Nat)
  | badLoc
  | nilv
  | sl (base : Option Nat) (off len : Nat)
  | mp (base : Option Nat)
  | chn (base : Option Nat)
  | iface (ty : GoCore.Ty) (v : CVal)
  | strct (tid : TypeId) (fields : List (String × CVal))
  | arr (elems : List CVal)
  | mdata (entries : List (CVal × CVal))
  | cdata (buf : List CVal) (capacity : Nat) (closed : Bool)
  | fn (fid : GoCore.FuncId) (captured : List CVal)
  | sync (p : SyncPrim)
  /-- The image of a MASKED struct field (declared latitude-bearing
  spot — see `Mask` below). Masking is VISIBLE in the form: a masked
  equivalence can never pass as a strict one. -/
  | masked
  deriving Repr

/-- A canonical cell's declared-type image: backing-array cells carry
their element type with the LENGTH ERASED (capacity slack); other
declared types pass through. -/
inductive CTy where
  | none
  | backing (elem : GoCore.Ty)
  | exact (t : GoCore.Ty)
  deriving Repr

structure CCell where
  ty : CTy
  val : CVal
  deriving Repr

/-- **The canonical form** — the choice-erased state. Equality of
`CForm`s IS the latitude equivalence. `flags` is the fail-closed
channel: a clean canonicalization has `flags = []`, and every
soundness-relevant refusal (fuel exhaustion, non-scalar map keys,
non-zero-like trimmed tails, mixed whole-array/slice references,
non-base locs, unstable view fixpoint) appears here. -/
structure CForm where
  roots : List CVal
  cells : List CCell
  flags : List String
  deriving Repr

/-- **A field mask** — the DECLARED latitude-bearing spots: struct
fields whose VALUES are latitude draws that persist in state without
any reachable reader (the init census's finding: exactly
`raft.raft.randomizedElectionTimeout` under the no-tick driver — see
`Specs/Raft/SeedPin.lean` for the declaration and its justification
obligations). Masked fields serialize as `CVal.masked` and are not
traversed. The EMPTY mask is the strict form; every masked
equivalence names its mask in the statement. -/
abbrev Mask := List (TypeId × String)

def Mask.hits (m : Mask) (tid : TypeId) (f : String) : Bool :=
  m.any (fun p => p.1 == tid && p.2 == f)

/-! ## Traversal bookkeeping -/

/-- View/reference collection state (phase 1): `views a` = the widest
`offset+len` window any reachable slice handle opens on cell `a`;
`direct` = cells referenced whole (plain pointer / map / chan base —
never trimmed). Assoc-list keyed by raw address id. -/
structure VSt where
  views : List (Nat × Nat)
  direct : List Nat
  flags : List String

def VSt.viewOf (st : VSt) (a : Nat) : Nat :=
  match st.views.lookup a with | some v => v | none => 0

def VSt.bumpView (st : VSt) (a : Nat) (v : Nat) : VSt :=
  if v ≤ st.viewOf a then st
  else { st with views := (a, v) :: st.views.filter (fun p => p.1 ≠ a) }

def VSt.markDirect (st : VSt) (a : Nat) : VSt :=
  if st.direct.contains a then st else { st with direct := a :: st.direct }

def VSt.flag (st : VSt) (f : String) : VSt :=
  if st.flags.contains f then st else { st with flags := f :: st.flags }

/-- Emission state (phase 2): discovery ids in first-visit order, the
emission queue (each address enters exactly once, at id assignment),
and the flag channel. -/
structure ESt where
  ids : List (Nat × Nat)
  nextId : Nat
  queue : List Nat
  flags : List String

def ESt.flag (st : ESt) (f : String) : ESt :=
  if st.flags.contains f then st else { st with flags := f :: st.flags }

def ESt.idOf (st : ESt) (a : Nat) : ESt × Nat :=
  match st.ids.lookup a with
  | some i => (st, i)
  | none =>
      let i := st.nextId
      ({ st with ids := (a, i) :: st.ids, nextId := i + 1,
                 queue := st.queue ++ [a] }, i)

/-! ## Zero-likeness (the trimmed-tail check)

Matches the shapes `defaultValue` produces (spill padding,
`buildAppendBackingValue`): a non-zero-like trimmed tail refuses the
trim, fail closed. Fueled by nesting depth. -/

def isZeroLike : Nat → GoValue → Bool
  | 0, _ => false
  | _ + 1, .unit => true
  | _ + 1, .bool b => !b
  | _ + 1, .int v _ => v == 0
  | _ + 1, .float bits _ => bits == 0
  | _ + 1, .string s => s.bytes.isEmpty
  | _ + 1, .nil => true
  | _ + 1, .slice sv => sv.base.isNone && sv.len == 0
  | _ + 1, .map mv => mv.base.isNone
  | _ + 1, .chan cv => cv.base.isNone
  | fuel + 1, .struct _ fs => fs.all (fun p => isZeroLike fuel p.2)
  | fuel + 1, .array vs => vs.all (isZeroLike fuel)
  | _ + 1, _ => false

/-! ## Scalar map-key ordering (the `mapIter` canonicalization axis) -/

/-- Total order key for scalar map keys; `none` = non-scalar (fail
closed at the sort site). Purely structural — no Format/repr in the
chain (kernel-reducibility). -/
def scalarKey : GoValue → Option (Nat × Int × List UInt8)
  | .int v _ => some (0, v, [])
  | .string s => some (1, 0, s.bytes.toList)
  | .bool b => some (2, if b then 1 else 0, [])
  | _ => none

/-- Lexicographic byte-list order (structural). -/
def bytesLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if b < a then false else bytesLe as bs

def keyLe (a b : (Nat × Int × List UInt8)) : Bool :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ bytesLe a.2.2 b.2.2 = true)))

/-- Insertion sort by scalar key (total, structural). -/
def insertByKey (x : (Nat × Int × List UInt8) × (GoValue × GoValue)) :
    List ((Nat × Int × List UInt8) × (GoValue × GoValue)) →
    List ((Nat × Int × List UInt8) × (GoValue × GoValue))
  | [] => [x]
  | y :: ys => if keyLe x.1 y.1 then x :: y :: ys else y :: insertByKey x ys

def sortEntries (l : List ((Nat × Int × List UInt8) × (GoValue × GoValue))) :
    List ((Nat × Int × List UInt8) × (GoValue × GoValue)) :=
  l.foldl (fun acc x => insertByKey x acc) []

/-- Sorted scalar-keyed entries of a `mapData`, or `none` when a key
is non-scalar. -/
def sortedEntries (es : Array (GoValue × GoValue)) :
    Option (List (GoValue × GoValue)) := do
  let keyed ← es.toList.mapM (fun p => (scalarKey p.1).map (fun k => (k, p)))
  pure ((sortEntries keyed).map (·.2))

/-! ## Phase 1 — view/direct collection (fueled, fixpointed) -/

/-- Address of a base loc; `none` (with the fail-closed flag raised by
callers) otherwise. -/
def baseAddr : Loc → Option Nat
  | .base ⟨a⟩ => some a
  | _ => none

mutual
/-- Collect views/direct marks reachable from a value. `fuel` bounds
BOTH value depth and cell jumps (decremented on every recursive call);
exhaustion flags `FUEL`. `visited` prevents cell revisits within the
pass. -/
def collectV (h : GoCore.Heap) (m : Mask) (fuel : Nat) (acc : VSt × List Nat)
    (v : GoValue) : VSt × List Nat :=
  match fuel with
  | 0 => (acc.1.flag "FUEL", acc.2)
  | fuel + 1 =>
    match v with
    | .addr l =>
        match baseAddr l with
        | some a => collectCell h m fuel ((acc.1.markDirect a), acc.2) a
        | none => (acc.1.flag "NONBASE-LOC", acc.2)
    | .slice sv =>
        match sv.base with
        | some l =>
            match baseAddr l with
            | some a =>
                collectCell h m fuel
                  ((acc.1.bumpView a (sv.offset + sv.len)), acc.2) a
            | none => (acc.1.flag "NONBASE-LOC", acc.2)
        | none => acc
    | .map mv =>
        match mv.base with
        | some l =>
            match baseAddr l with
            | some a => collectCell h m fuel ((acc.1.markDirect a), acc.2) a
            | none => (acc.1.flag "NONBASE-LOC", acc.2)
        | none => acc
    | .chan cv =>
        match cv.base with
        | some l =>
            match baseAddr l with
            | some a => collectCell h m fuel ((acc.1.markDirect a), acc.2) a
            | none => (acc.1.flag "NONBASE-LOC", acc.2)
        | none => acc
    | .struct tid fs => fs.foldl (fun acc p =>
        if m.hits tid p.1 then acc else collectV h m fuel acc p.2) acc
    | .array vs => vs.foldl (fun acc x => collectV h m fuel acc x) acc
    | .interface _ x => collectV h m fuel acc x
    | .funcVal _ cap => cap.foldl (fun acc x => collectV h m fuel acc x) acc
    | .mapData es => es.foldl (fun acc p =>
        collectV h m fuel (collectV h m fuel acc p.1) p.2) acc
    | .chanData buf _ _ => buf.foldl (fun acc x => collectV h m fuel acc x) acc
    | _ => acc
termination_by structural fuel

/-- Visit a cell once per pass; backing arrays traversed only within
the current view unless directly referenced. -/
def collectCell (h : GoCore.Heap) (m : Mask) (fuel : Nat) (acc : VSt × List Nat)
    (a : Nat) : VSt × List Nat :=
  match fuel with
  | 0 => (acc.1.flag "FUEL", acc.2)
  | fuel + 1 =>
    if acc.2.contains a then acc
    else
      let acc := (acc.1, a :: acc.2)
      match GoCore.Heap.lookup h (.base ⟨a⟩) with
      | none => acc
      | some cell =>
          match cell.value with
          | .array vs =>
              let bound := if acc.1.direct.contains a then vs.size
                           else min vs.size (acc.1.viewOf a)
              (vs.toList.take bound).foldl
                (fun acc x => collectV h m fuel acc x) acc
          | v => collectV h m fuel acc v
termination_by structural fuel
end

/-- One collection pass over the roots. -/
def collectPass (h : GoCore.Heap) (m : Mask) (fuel : Nat) (st : VSt)
    (roots : List GoValue) : VSt :=
  (roots.foldl (fun acc v => collectV h m fuel acc v) (st, [])).1

/-- The pass-stability measure: view-key count + total view width +
direct count. Along a pass all three components are MONOTONE
(`bumpView` only adds a key or strictly widens an existing key's
value — the filter-and-recons keeps the length unchanged on a widen;
`markDirect` only adds), so measure equality ⇔ the pass changed
nothing. The previous stability test compared the two LIST LENGTHS
only, which a widen leaves unchanged — the fixpoint could stop with
an untraversed widened window and silently drop content (arc-4
landing-audit fail-open finding, 2026-08-26; the dropped case's
witness module `ChoiceCanonWitness.lean` was W0-killed with all
witnesses of its era — archived at `archive/fixed-trajectory-era`;
witness owed on first consumption of the fixpoint). -/
def VSt.measure (st : VSt) : Nat :=
  st.views.length + st.views.foldl (fun s p => s + p.2) 0 +
    st.direct.length

/-- Fixpoint of the collection pass: views/direct grow monotonically
(keys, view widths, and direct marks — the `VSt.measure` components);
`n` bounds iterations, exhaustion flags `VIEWFIX-UNSTABLE`. Stability
is measure equality, NOT list-length equality (see `VSt.measure`'s
docstring for the fail-open this replaces). -/
def collectFix (h : GoCore.Heap) (m : Mask) (fuel : Nat) (roots : List GoValue) :
    Nat → VSt → VSt
  | 0, st => st.flag "VIEWFIX-UNSTABLE"
  | n + 1, st =>
      let st' := collectPass h m fuel st roots
      if st'.measure == st.measure then st'
      else collectFix h m fuel roots n st'

/-! ## Phase 2 — canonical emission -/

mutual
/-- Serialize a value, assigning discovery ids at first pointer
visit. `fuel` bounds value depth. -/
def serV (h : GoCore.Heap) (m : Mask) (vst : VSt) (fuel : Nat) (st : ESt)
    (v : GoValue) : ESt × CVal :=
  match fuel with
  | 0 => (st.flag "FUEL", .badLoc)
  | fuel + 1 =>
    match v with
    | .unit => (st, .unit)
    | .bool b => (st, .bool b)
    | .int v k => (st, .int v k)
    | .float bits k => (st, .float bits k)
    | .string s => (st, .str s.bytes)
    | .nil => (st, .nilv)
    | .addr l =>
        match baseAddr l with
        | some a => let (st, i) := st.idOf a; (st, .ref i)
        | none => (st.flag "NONBASE-LOC", .badLoc)
    | .slice sv =>
        match sv.base with
        | some l =>
            match baseAddr l with
            | some a =>
                let (st, i) := st.idOf a
                (st, .sl (some i) sv.offset sv.len)
            | none => (st.flag "NONBASE-LOC", .badLoc)
        | none => (st, .sl none sv.offset sv.len)
    | .map mv =>
        match mv.base with
        | some l =>
            match baseAddr l with
            | some a => let (st, i) := st.idOf a; (st, .mp (some i))
            | none => (st.flag "NONBASE-LOC", .badLoc)
        | none => (st, .mp none)
    | .chan cv =>
        match cv.base with
        | some l =>
            match baseAddr l with
            | some a => let (st, i) := st.idOf a; (st, .chn (some i))
            | none => (st.flag "NONBASE-LOC", .badLoc)
        | none => (st, .chn none)
    | .interface ty x =>
        let (st, cx) := serV h m vst fuel st x
        (st, .iface ty cx)
    | .struct tid fs =>
        let (st, cfs) := serFields h m vst fuel st tid fs.toList
        (st, .strct tid cfs)
    | .array vs =>
        let (st, cs) := serMany h m vst fuel st vs.toList
        (st, .arr cs)
    | .mapData es =>
        match sortedEntries es with
        | some sorted =>
            let (st, ces) := serPairs h m vst fuel st sorted
            (st, .mdata ces)
        | none =>
            let st := st.flag "MAPKEY-UNSORTABLE"
            let (st, ces) := serPairs h m vst fuel st es.toList
            (st, .mdata ces)
    | .chanData buf capacity closed =>
        let (st, cs) := serMany h m vst fuel st buf.toList
        (st, .cdata cs capacity closed)
    | .funcVal fid cap =>
        let (st, cs) := serMany h m vst fuel st cap
        (st, .fn fid cs)
    | .syncData p => (st, .sync p)
termination_by structural fuel

def serMany (h : GoCore.Heap) (m : Mask) (vst : VSt) (fuel : Nat) (st : ESt)
    (vs : List GoValue) : ESt × List CVal :=
  match fuel with
  | 0 => (st.flag "FUEL", [])
  | fuel + 1 =>
    match vs with
    | [] => (st, [])
    | v :: rest =>
        let (st, c) := serV h m vst fuel st v
        let (st, cs) := serMany h m vst fuel st rest
        (st, c :: cs)
termination_by structural fuel

def serFields (h : GoCore.Heap) (m : Mask) (vst : VSt) (fuel : Nat) (st : ESt)
    (tid : TypeId) (fs : List (String × GoValue)) : ESt × List (String × CVal) :=
  match fuel with
  | 0 => (st.flag "FUEL", [])
  | fuel + 1 =>
    match fs with
    | [] => (st, [])
    | (n, v) :: rest =>
        if m.hits tid n then
          let (st, cs) := serFields h m vst fuel st tid rest
          (st, (n, .masked) :: cs)
        else
          let (st, c) := serV h m vst fuel st v
          let (st, cs) := serFields h m vst fuel st tid rest
          (st, (n, c) :: cs)
termination_by structural fuel

def serPairs (h : GoCore.Heap) (m : Mask) (vst : VSt) (fuel : Nat) (st : ESt)
    (ps : List (GoValue × GoValue)) : ESt × List (CVal × CVal) :=
  match fuel with
  | 0 => (st.flag "FUEL", [])
  | fuel + 1 =>
    match ps with
    | [] => (st, [])
    | (k, v) :: rest =>
        let (st, ck) := serV h m vst fuel st k
        let (st, cv) := serV h m vst fuel st v
        let (st, cs) := serPairs h m vst fuel st rest
        (st, (ck, cv) :: cs)
termination_by structural fuel
end

/-- Emit one cell: declared-type image + (possibly trimmed) value. -/
def emitCell (h : GoCore.Heap) (m : Mask) (vst : VSt) (vfuel : Nat) (st : ESt)
    (a : Nat) : ESt × CCell :=
  match GoCore.Heap.lookup h (.base ⟨a⟩) with
  | none => (st.flag s!"MISSING-{a}", ⟨.none, .badLoc⟩)
  | some cell =>
      let direct := vst.direct.contains a
      let viewed := vst.viewOf a > 0
      let cty : CTy := match cell.declaredTy with
        | Option.none => .none
        | Option.some t =>
            match t with
            | .array _ elem => if direct then .exact t else .backing elem
            | _ => .exact t
      match cell.value with
      | .array vs =>
          if direct then
            let st := if viewed then st.flag s!"MIXED-REF-{a}" else st
            let (st, c) := serV h m vst vfuel st (GoValue.array vs)
            (st, ⟨cty, c⟩)
          else
            let view := min vs.size (vst.viewOf a)
            let kept := vs.extract 0 view
            let dropped := vs.extract view vs.size
            if dropped.all (isZeroLike 1024) then
              let (st, c) := serV h m vst vfuel st (GoValue.array kept)
              (st, ⟨cty, c⟩)
            else
              -- fail closed: refuse the trim, keep everything
              let st := st.flag s!"TAILNONZERO-{a}"
              let (st, c) := serV h m vst vfuel st (GoValue.array vs)
              (st, ⟨.exact (cell.declaredTy.getD (.slice .bool)), c⟩)
      | v =>
          let (st, c) := serV h m vst vfuel st v
          (st, ⟨cty, c⟩)

/-- Drain the discovery queue (each address enters at most once, so
`fuel` = an address-count bound). -/
def drain (h : GoCore.Heap) (m : Mask) (vst : VSt) (vfuel : Nat) :
    Nat → ESt → List CCell → ESt × List CCell
  | 0, st, acc => (st.flag "DRAIN-FUEL", acc.reverse)
  | fuel + 1, st, acc =>
      match st.queue with
      | [] => (st, acc.reverse)
      | a :: rest =>
          let st := { st with queue := rest }
          let (st, c) := emitCell h m vst vfuel st a
          drain h m vst vfuel fuel st (c :: acc)

/-! ## The canonical form and the equivalence -/

/-- **THE CANONICAL FORM** of a state at a root set. Fuel is derived
from the state (heap size bounds cell count; 2048 bounds value
nesting per the `GoValue.eqb` depth convention); exhaustion is a
flag, never a silent wrong answer. -/
def canonStateM (m : Mask) (σ : ExecState) (roots : List GoValue) : CForm :=
  let h := σ.heap
  let n := h.length
  let cellFuel := (n + roots.length + 2) * 2048
  let vst := collectFix h m cellFuel roots (n + 2)
    { views := [], direct := [], flags := [] }
  let st0 : ESt := { ids := [], nextId := 0, queue := [], flags := [] }
  let (st1, croots) := roots.foldl
    (fun (acc : ESt × List CVal) v =>
      let (st, c) := serV h m vst 2048 acc.1 v
      (st, acc.2 ++ [c])) (st0, [])
  let (st2, cells) := drain h m vst 2048 (n + 2) st1 []
  { roots := croots, cells := cells, flags := vst.flags ++ st2.flags }

/-- The STRICT canonical form (empty mask). -/
def canonState (σ : ExecState) (roots : List GoValue) : CForm :=
  canonStateM [] σ roots

/-- **THE LATITUDE EQUIVALENCE `~`** (choice-invariance's carrier):
states are equivalent at corresponding root sets when their canonical
forms coincide. The two erased axes are exactly the sequential
machine's two draw sites' state effects (relocation from
order-perturbed allocation, capacity slack from spill draws); flags
live inside the form, so a fail-closed canonicalization can only
REFUSE equivalence, never fake it. -/
def CEquivM (m : Mask) (σ : ExecState) (roots : List GoValue)
    (σ' : ExecState) (roots' : List GoValue) : Prop :=
  canonStateM m σ roots = canonStateM m σ' roots'

/-- The STRICT latitude equivalence (empty mask). -/
def CEquiv (σ : ExecState) (roots : List GoValue)
    (σ' : ExecState) (roots' : List GoValue) : Prop :=
  CEquivM [] σ roots σ' roots'

theorem CEquivM.refl (m : Mask) (σ : ExecState) (roots : List GoValue) :
    CEquivM m σ roots σ roots := rfl

theorem CEquivM.symm {m σ roots σ' roots'}
    (h : CEquivM m σ roots σ' roots') : CEquivM m σ' roots' σ roots :=
  Eq.symm h

theorem CEquivM.trans {m σ₁ r₁ σ₂ r₂ σ₃ r₃}
    (h₁ : CEquivM m σ₁ r₁ σ₂ r₂) (h₂ : CEquivM m σ₂ r₂ σ₃ r₃) :
    CEquivM m σ₁ r₁ σ₃ r₃ := Eq.trans h₁ h₂

theorem CEquiv.refl (σ : ExecState) (roots : List GoValue) :
    CEquiv σ roots σ roots := rfl

theorem CEquiv.symm {σ roots σ' roots'} (h : CEquiv σ roots σ' roots') :
    CEquiv σ' roots' σ roots := Eq.symm h

theorem CEquiv.trans {σ₁ r₁ σ₂ r₂ σ₃ r₃}
    (h₁ : CEquiv σ₁ r₁ σ₂ r₂) (h₂ : CEquiv σ₂ r₂ σ₃ r₃) :
    CEquiv σ₁ r₁ σ₃ r₃ := Eq.trans h₁ h₂

/-- A clean canonicalization (no fail-closed refusals). Witnesses
check this computationally; consumers may require it as a premise. -/
def CleanFormM (m : Mask) (σ : ExecState) (roots : List GoValue) : Prop :=
  (canonStateM m σ roots).flags = []

def CleanForm (σ : ExecState) (roots : List GoValue) : Prop :=
  CleanFormM [] σ roots

/-- **Reader invariance by construction** (the representation-
engineering form): any reader defined over the canonical form is
`~`-invariant. This is the module's interface for `absRead`-class
invariance — readers factor through `canonState`, and factoring IS
the invariance proof. -/
theorem read_invariant {α : Type} (read : CForm → α)
    {σ roots σ' roots'} (h : CEquiv σ roots σ' roots') :
    read (canonState σ roots) = read (canonState σ' roots') := by
  unfold CEquiv CEquivM at h; unfold canonState; rw [h]

/-- Masked reader invariance: any reader over the MASKED form is
`~ₘ`-invariant. -/
theorem readM_invariant {α : Type} (m : Mask) (read : CForm → α)
    {σ roots σ' roots'} (h : CEquivM m σ roots σ' roots') :
    read (canonStateM m σ roots) = read (canonStateM m σ' roots') := by
  unfold CEquivM at h; rw [h]

end GoLean.Frame.ChoiceErase
