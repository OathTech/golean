import GoLeanProofs.Frame.ChoiceCanon

/-! # `SpanIso` — the RELATIONAL specification of the latitude
equivalence `~ₘ` (choice-erasure arc CE1, 2026-08-27)

**What this module is.** The mathematical content of `CEquivM` stated
WITHOUT the canonicalizer: two states (at root sets, under a mask)
are span-isomorphic when there EXISTS a bijection between their
reachable spans — reachable heap cells, view-bounded exactly as slice
handles open windows — that respects value structure up to the three
erased axes:

- **relocation**: heap addresses correspond through the bijection
  `φ`, never by number;
- **capacity slack**: slice-handle `cap` fields are unconstrained,
  backing cells correspond on the maximal reachable window with
  ZERO-LIKE tails beyond it (the cleanliness side condition doing the
  quantifier work — surfaced explicitly, per the arc plan's CE1
  constraint (b));
- **canonical map contents**: `mapData` entries correspond up to an
  ∃-quantified permutation with equal (scalar) keys;

and respects the MASK: masked struct fields are exempt from value
correspondence (visible in the relation, exactly as `CVal.masked` is
visible in the form).

**THE NO-CANONICALIZER DISCIPLINE (the arc plan's CE1 hard
constraint (a); scoff 3).** Nothing in this module references the
canonicalizer: no `collectFix`/`collectPass`/`serV`/`canonStateM`/
`CForm`/`VSt`/`isZeroLike`/`sortedEntries` — checkable by grep; the
only imports from `ChoiceCanon` are the `Mask` interface
(`Mask`/`Mask.hits`), which is part of the RELATION's declared
signature ("respecting the mask"), not of the checker. The cap-slack
window is characterized relationally: `MaxView` is ∃-quantified over
reachable slice handles, never computed. The canonicalizer is the
DECISION PROCEDURE for this relation; the correspondence theorem
(`cequiv_iff_spanIso`, the CE1 gate) lives in the `SpanIso*`
proof modules, where referencing both sides is the point.

**Relational cleanliness (`RelClean`).** The fail-closed refusals the
checker signals through flags appear here as RELATIONAL side
conditions inside the relation (CE1 constraint (b)): reachable base
addresses present, no mixed whole/slice references, scalar map keys,
zero-like trimmed tails, and existence of the maximal window. They do
quantifier work: without them `SpanIso` would relate states whose
differences hide beyond a window or behind a refused
canonicalization.

**Well-formedness (`KeysWF`) is a PREMISE, not baked in** (CE1
constraint (c)): duplicate-free map keys and int-key kind homogeneity
are checker-INVISIBLE properties every machine-reachable state has
(Go maps have unique, homogeneously-typed keys) but hand-built states
can violate; the iff takes them as explicit hypotheses. Reachability
of the STATES is never assumed.

**LINEAGE**: heap/graph isomorphism up to an erasure quotient
(CompCert memory-model block renaming — the citation the basecamp
review demoted to goal-level "until `cequiv_iff_spanIso` exists";
this module plus the iff is that goal); data independence for the
mask/permutation components. The relation is the SPECIFICATION face;
all future induction (the erased step, the per-class congruences)
runs on this face, never on the checker. -/

namespace GoLean.Frame.ChoiceErase

open GoLean GoLean.GoCore

/-! ## Scalar keys and zero-likeness, relationally -/

/-- A scalar map key (int/string/bool) — the shapes Go's `mapIter`
canonicalization can order. Stated structurally; the checker's
`scalarKey` computes an order key for exactly these shapes. -/
def IsScalarKey : GoValue → Prop
  | .int _ _ => True
  | .string _ => True
  | .bool _ => True
  | _ => False

/-- Zero-likeness, as an inductive predicate (no fuel): the value
shapes `defaultValue` produces as spill padding. A zero-like value
contains NO heap references — the reason trimmed tails can be erased
without dropping reachable state. -/
inductive ZeroLike : GoValue → Prop where
  | unit : ZeroLike .unit
  | bool : ZeroLike (.bool false)
  | int {k} : ZeroLike (.int 0 k)
  | float {k} : ZeroLike (.float 0 k)
  | string {s : GoString} : s.bytes.isEmpty = true → ZeroLike (.string s)
  | nil : ZeroLike .nil
  | slice {off cap} : ZeroLike (.slice ⟨none, off, 0, cap⟩)
  | map : ZeroLike (.map ⟨none⟩)
  | chan : ZeroLike (.chan ⟨none⟩)
  | struct {tid} {fs : Array (String × GoValue)}
      (h : ∀ i (hi : i < fs.size), ZeroLike (fs[i]'hi).2) :
      ZeroLike (.struct tid fs)
  | array {vs : Array GoValue}
      (h : ∀ i (hi : i < vs.size), ZeroLike (vs[i]'hi)) :
      ZeroLike (.array vs)

/-! ## Reachability (the span)

The view-bounded reachable VALUES of a state at a root set: the
inductive closure of the roots under sub-value structure (mask-
exempt), cell dereference (whole-value for pointer/map/chan
references), and slice-window jumps (element access WITHIN the
handle's own window — the union over reachable handles of these
windows is exactly the maximal-window prefix; elements beyond every
window are NOT reachable, which is what licenses the trim). -/
inductive RVal (h : Heap) (m : Mask) (roots : List GoValue) : GoValue → Prop where
  | root {v} (hv : v ∈ roots) : RVal h m roots v
  | structField {tid} {fs : Array (String × GoValue)} {i}
      (hr : RVal h m roots (.struct tid fs)) (hi : i < fs.size)
      (hm : m.hits tid (fs[i]'hi).1 = false) :
      RVal h m roots (fs[i]'hi).2
  | arrayElem {vs : Array GoValue} {i}
      (hr : RVal h m roots (.array vs)) (hi : i < vs.size) :
      RVal h m roots (vs[i]'hi)
  | ifaceVal {t v} (hr : RVal h m roots (.interface t v)) :
      RVal h m roots v
  | funcCap {fid} {cap : List GoValue} {v}
      (hr : RVal h m roots (.funcVal fid cap)) (hv : v ∈ cap) :
      RVal h m roots v
  | mapKey {es : Array (GoValue × GoValue)} {i}
      (hr : RVal h m roots (.mapData es)) (hi : i < es.size) :
      RVal h m roots (es[i]'hi).1
  | mapVal {es : Array (GoValue × GoValue)} {i}
      (hr : RVal h m roots (.mapData es)) (hi : i < es.size) :
      RVal h m roots (es[i]'hi).2
  | chanElem {buf : Array GoValue} {c cl i}
      (hr : RVal h m roots (.chanData buf c cl)) (hi : i < buf.size) :
      RVal h m roots (buf[i]'hi)
  | derefAddr {a cell}
      (hr : RVal h m roots (.addr (.base ⟨a⟩)))
      (hc : Heap.lookup h (.base ⟨a⟩) = some cell) :
      RVal h m roots cell.value
  | derefMap {a cell}
      (hr : RVal h m roots (.map ⟨some (.base ⟨a⟩)⟩))
      (hc : Heap.lookup h (.base ⟨a⟩) = some cell) :
      RVal h m roots cell.value
  | derefChan {a cell}
      (hr : RVal h m roots (.chan ⟨some (.base ⟨a⟩)⟩))
      (hc : Heap.lookup h (.base ⟨a⟩) = some cell) :
      RVal h m roots cell.value
  | sliceElem {a off len cap cell} {vs : Array GoValue} {i}
      (hr : RVal h m roots (.slice ⟨some (.base ⟨a⟩), off, len, cap⟩))
      (hc : Heap.lookup h (.base ⟨a⟩) = some cell)
      (hval : cell.value = .array vs)
      (hw : i < off + len) (hi : i < vs.size) :
      RVal h m roots (vs[i]'hi)
  | sliceWhole {a off len cap cell}
      (hr : RVal h m roots (.slice ⟨some (.base ⟨a⟩), off, len, cap⟩))
      (hc : Heap.lookup h (.base ⟨a⟩) = some cell)
      (hnv : ∀ vs : Array GoValue, cell.value ≠ .array vs) :
      RVal h m roots cell.value

/-- Cell `a` is WHOLE-referenced by a reachable value (pointer, map
reference, or channel reference — the never-trimmed class). -/
def DirectRef (h : Heap) (m : Mask) (roots : List GoValue) (a : Nat) : Prop :=
  RVal h m roots (.addr (.base ⟨a⟩)) ∨
  RVal h m roots (.map ⟨some (.base ⟨a⟩)⟩) ∨
  RVal h m roots (.chan ⟨some (.base ⟨a⟩)⟩)

/-- Some reachable slice handle opens window `[0, w)` on cell `a`
(`w = offset + len`, the checker-independent window arithmetic). -/
def ViewedAt (h : Heap) (m : Mask) (roots : List GoValue) (a w : Nat) : Prop :=
  ∃ off len cap,
    RVal h m roots (.slice ⟨some (.base ⟨a⟩), off, len, cap⟩) ∧ off + len = w

/-- Cell `a` belongs to the reachable span. -/
def CellReach (h : Heap) (m : Mask) (roots : List GoValue) (a : Nat) : Prop :=
  DirectRef h m roots a ∨ ∃ w, ViewedAt h m roots a w

/-- `W` is THE maximal window any reachable handle opens on `a` —
∃-quantified over reachable handles (the CE1 constraint's phrase),
never computed. -/
def MaxView (h : Heap) (m : Mask) (roots : List GoValue) (a W : Nat) : Prop :=
  ViewedAt h m roots a W ∧ ∀ w, ViewedAt h m roots a w → w ≤ W

/-! ## Relational cleanliness (the flags, as side conditions) -/

/-- The fail-closed refusal conditions, stated relationally per side.
Each clause is the honest face of a checker flag: `base_present` ↔ no
`MISSING`, `no_mixed` ↔ no `MIXED-REF`, `keys_scalar` ↔ no
`MAPKEY-UNSORTABLE`, `tails_zero` ↔ no `TAILNONZERO`; `max_exists`
asserts the ∃-sup the checker computes. (Fuel/iteration flags have no
relational face — they are artifacts of the DECISION PROCEDURE, and
the iff carries the checker's own cleanliness beside this bundle.) -/
structure RelClean (h : Heap) (m : Mask) (roots : List GoValue) : Prop where
  base_present : ∀ a, CellReach h m roots a →
    ∃ c, Heap.lookup h (.base ⟨a⟩) = some c
  no_mixed : ∀ a w, DirectRef h m roots a → ViewedAt h m roots a w → w = 0
  keys_scalar : ∀ es : Array (GoValue × GoValue), RVal h m roots (.mapData es) →
    ∀ i (hi : i < es.size), IsScalarKey (es[i]'hi).1
  max_exists : ∀ a w, ViewedAt h m roots a w →
    ∃ W, MaxView h m roots a W
  tails_zero : ∀ a W c (vs : Array GoValue), ¬ DirectRef h m roots a →
    MaxView h m roots a W →
    Heap.lookup h (.base ⟨a⟩) = some c → c.value = .array vs →
    ∀ i (hi : i < vs.size), min vs.size W ≤ i → ZeroLike (vs[i]'hi)

/-! ## Value correspondence up to `φ`, cap slack, map permutation,
and the mask -/

/-- Structural value correspondence under an address bijection `φ`:
equality everywhere except the erased axes — addresses map through
`φ`; slice `cap`s are FREE (the slack); `mapData` entries correspond
up to an ∃-quantified permutation `π` with EQUAL keys (scalar keys
carry no addresses; non-scalar keys are refused by `RelClean` before
this clause matters); masked struct fields are EXEMPT (any values). -/
inductive VCorr (m : Mask) (φ : Nat → Nat) : GoValue → GoValue → Prop where
  | unit : VCorr m φ .unit .unit
  | bool {b} : VCorr m φ (.bool b) (.bool b)
  | int {v k} : VCorr m φ (.int v k) (.int v k)
  | float {bits k} : VCorr m φ (.float bits k) (.float bits k)
  | string {s} : VCorr m φ (.string s) (.string s)
  | nil : VCorr m φ .nil .nil
  | addr {a} : VCorr m φ (.addr (.base ⟨a⟩)) (.addr (.base ⟨φ a⟩))
  | sliceNil {off len cap cap'} :
      VCorr m φ (.slice ⟨none, off, len, cap⟩) (.slice ⟨none, off, len, cap'⟩)
  | slice {a off len cap cap'} :
      VCorr m φ (.slice ⟨some (.base ⟨a⟩), off, len, cap⟩)
                (.slice ⟨some (.base ⟨φ a⟩), off, len, cap'⟩)
  | mapNil : VCorr m φ (.map ⟨none⟩) (.map ⟨none⟩)
  | mapRef {a} : VCorr m φ (.map ⟨some (.base ⟨a⟩)⟩) (.map ⟨some (.base ⟨φ a⟩)⟩)
  | chanNil : VCorr m φ (.chan ⟨none⟩) (.chan ⟨none⟩)
  | chanRef {a} : VCorr m φ (.chan ⟨some (.base ⟨a⟩)⟩) (.chan ⟨some (.base ⟨φ a⟩)⟩)
  | iface {t v v'} (hv : VCorr m φ v v') :
      VCorr m φ (.interface t v) (.interface t v')
  | strct {tid} {fs fs' : Array (String × GoValue)}
      (hlen : fs.size = fs'.size)
      (hname : ∀ i (hi : i < fs.size) (hi' : i < fs'.size),
        (fs[i]'hi).1 = (fs'[i]'hi').1)
      (hval : ∀ i (hi : i < fs.size) (hi' : i < fs'.size),
        m.hits tid (fs[i]'hi).1 = false → VCorr m φ (fs[i]'hi).2 (fs'[i]'hi').2) :
      VCorr m φ (.struct tid fs) (.struct tid fs')
  | arr {vs vs' : Array GoValue}
      (hlen : vs.size = vs'.size)
      (hval : ∀ i (hi : i < vs.size) (hi' : i < vs'.size),
        VCorr m φ (vs[i]'hi) (vs'[i]'hi')) :
      VCorr m φ (.array vs) (.array vs')
  | mapData {es es' : Array (GoValue × GoValue)} (π : Nat → Nat)
      (hlen : es.size = es'.size)
      (hπlt : ∀ i, i < es.size → π i < es'.size)
      (hπinj : ∀ i j, i < es.size → j < es.size → π i = π j → i = j)
      (hπsurj : ∀ j, j < es'.size → ∃ i, i < es.size ∧ π i = j)
      (hkey : ∀ i (hi : i < es.size) (hj : π i < es'.size),
        (es[i]'hi).1 = (es'[π i]'hj).1)
      (hvalc : ∀ i (hi : i < es.size) (hj : π i < es'.size),
        VCorr m φ (es[i]'hi).2 (es'[π i]'hj).2) :
      VCorr m φ (.mapData es) (.mapData es')
  | chanData {buf buf' : Array GoValue} {c cl}
      (hlen : buf.size = buf'.size)
      (hval : ∀ i (hi : i < buf.size) (hi' : i < buf'.size),
        VCorr m φ (buf[i]'hi) (buf'[i]'hi')) :
      VCorr m φ (.chanData buf c cl) (.chanData buf' c cl)
  | funcVal {fid} {cap cap' : List GoValue}
      (hlen : cap.length = cap'.length)
      (hval : ∀ i (hi : i < cap.length) (hi' : i < cap'.length),
        VCorr m φ (cap[i]'hi) (cap'[i]'hi')) :
      VCorr m φ (.funcVal fid cap) (.funcVal fid cap')
  | syncData {p} : VCorr m φ (.syncData p) (.syncData p)

/-- Declared-type correspondence for a slice-viewed (never
whole-referenced) cell: array declarations correspond with the LENGTH
erased (the capacity-slack axis at the type level); everything else
corresponds exactly. -/
inductive BackingTyCorr : Option Ty → Option Ty → Prop where
  | none : BackingTyCorr none none
  | array {n n' e} : BackingTyCorr (some (.array n e)) (some (.array n' e))
  | other {t} (hne : ∀ n e, t ≠ .array n e) : BackingTyCorr (some t) (some t)

/-! ## The per-cell correspondence and the isomorphism -/

/-- Contents of reachable cell `a` correspond to contents of `φ a`:
whole-referenced cells correspond in full (declared type equal, value
`VCorr`); slice-viewed cells correspond up to the SHARED maximal
window `W` — equal kept-prefix length `min size W` (sizes themselves
are FREE — the slack), pointwise `VCorr` on the kept prefix (the
zero-like tails are `RelClean`'s clause), array-shape agreement, and
length-erased declared types. -/
def CellCorr (m : Mask) (h : Heap) (roots : List GoValue)
    (h' : Heap) (φ : Nat → Nat) (a : Nat) : Prop :=
  ∃ c c', Heap.lookup h (.base ⟨a⟩) = some c ∧
    Heap.lookup h' (.base ⟨φ a⟩) = some c' ∧
    (DirectRef h m roots a →
      c.declaredTy = c'.declaredTy ∧ VCorr m φ c.value c'.value) ∧
    (¬ DirectRef h m roots a →
      BackingTyCorr c.declaredTy c'.declaredTy ∧
      ((∀ vs : Array GoValue, c.value ≠ .array vs) → VCorr m φ c.value c'.value) ∧
      (∀ vs : Array GoValue, c.value = .array vs →
        ∃ vs' : Array GoValue, c'.value = .array vs') ∧
      (∀ vs' : Array GoValue, c'.value = .array vs' →
        ∃ vs : Array GoValue, c.value = .array vs) ∧
      (∀ (vs vs' : Array GoValue), c.value = .array vs → c'.value = .array vs' →
        ∃ W, MaxView h m roots a W ∧
          min vs.size W = min vs'.size W ∧
          (∀ i (hi : i < vs.size) (hi' : i < vs'.size),
            i < min vs.size W → VCorr m φ (vs[i]'hi) (vs'[i]'hi'))))

/-- **The span isomorphism at a named bijection.** All clauses over
the REACHABLE span only: `φ` maps it bijectively onto the primed
reachable span, preserving the direct/viewed classification, the
window structure, root values (pointwise), and cell contents
(`CellCorr`), with both sides relationally clean. Nothing constrains
unreachable cells — allocation garbage is erased by construction. -/
structure SpanIsoAt (m : Mask) (σ : ExecState) (roots : List GoValue)
    (σ' : ExecState) (roots' : List GoValue) (φ : Nat → Nat) : Prop where
  clean : RelClean σ.heap m roots
  clean' : RelClean σ'.heap m roots'
  roots_len : roots.length = roots'.length
  roots_corr : ∀ i (hi : i < roots.length) (hi' : i < roots'.length),
    VCorr m φ (roots[i]'hi) (roots'[i]'hi')
  reach_map : ∀ a, CellReach σ.heap m roots a →
    CellReach σ'.heap m roots' (φ a)
  reach_inj : ∀ a b, CellReach σ.heap m roots a → CellReach σ.heap m roots b →
    φ a = φ b → a = b
  reach_surj : ∀ a', CellReach σ'.heap m roots' a' →
    ∃ a, CellReach σ.heap m roots a ∧ φ a = a'
  direct_iff : ∀ a, CellReach σ.heap m roots a →
    (DirectRef σ.heap m roots a ↔ DirectRef σ'.heap m roots' (φ a))
  viewed_iff : ∀ a w, CellReach σ.heap m roots a →
    (ViewedAt σ.heap m roots a w ↔ ViewedAt σ'.heap m roots' (φ a) w)
  cells : ∀ a, CellReach σ.heap m roots a →
    CellCorr m σ.heap roots σ'.heap φ a

/-- **`SpanIso` — the relational face of `~ₘ`**: some address
bijection witnesses the span isomorphism. The CE1 gate theorem
(`cequiv_iff_spanIso`) proves this coincides with the canonicalizer's
verdict on well-formed states; all erased-semantics induction runs on
THIS relation. -/
def SpanIso (m : Mask) (σ : ExecState) (roots : List GoValue)
    (σ' : ExecState) (roots' : List GoValue) : Prop :=
  ∃ φ : Nat → Nat, SpanIsoAt m σ roots σ' roots' φ

/-! ## Well-formedness premises (stated, not baked in)

Checker-INVISIBLE properties the iff needs: duplicate keys make the
canonical sort order depend on insertion order (which IS the erased
latitude), and int-kind heterogeneity collapses distinct keys to one
sort key. Machine-reachable states satisfy both (Go maps have unique
keys of one type); hand-built states must bring the premise. -/
def KeysWF (h : Heap) (m : Mask) (roots : List GoValue) : Prop :=
  ∀ es : Array (GoValue × GoValue), RVal h m roots (.mapData es) →
    (∀ i j (hi : i < es.size) (hj : j < es.size),
      (es[i]'hi).1 = (es[j]'hj).1 → i = j) ∧
    (∀ i j (hi : i < es.size) (hj : j < es.size) vi ki vj kj,
      (es[i]'hi).1 = GoValue.int vi ki → (es[j]'hj).1 = GoValue.int vj kj →
      ki = kj)

end GoLean.Frame.ChoiceErase
