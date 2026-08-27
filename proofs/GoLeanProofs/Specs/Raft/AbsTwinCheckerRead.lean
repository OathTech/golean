import GoLeanProofs.Specs.Raft.AbsTwinRead

/-! # W3 U3.0b — THE READER EXTENSION: the checker-state lens readers

The C3 vocabulary of the adopted invariant design
(`docs/2026-08-27_w25-invariant-design.md`, open point 2 resolved as
SEPARATE LENS READERS — no new `AbsTwinV1` structure, no change to any
`AbsTwinV0` consumer): total, fail-closed, first-order lens reads of

- the checker's `leaderOf` map (twin-lib.go:165 — S1's term ↦ claimer),
- the checker's `byIndex` map (twin-lib.go:166 — S2's index ↦ slot),
- the per-node `got` map (twin-lib.go:151 — S4's data record),
- the per-node cursors `applied`/`lastTrm` (twin-lib.go:149-150 —
  S3's monotonicity state),
- the per-message entry METADATA `(Type, Data)` of the net multiset
  (raftpb.Entry:276-281 — the C4 population clause's all-EntryNormal
  vocabulary and the payload clause's data axis, which `absMessage`'s
  `(Index, Term)` projection deliberately does not carry).

Each reader follows the `AbsTwinRead` pattern (TypeId-checked, `none`
on any shape mismatch — a mis-located or mis-shaped cell never reads
back a well-formed answer) and is stated through the lens combinators
where one exists, so the `_ren` congruences below compose from the
Lens/RenCongr laws instead of re-deriving heap walks. The map lens
(`mapRead`) is NEW here — Go maps were unprojected before this unit;
it stays file-local until a second consumer bites (the promotion
ledger's ≥2 rule).

Map order note (fail-closed honesty): `mapRead` returns the
`mapData` entries IN STORE ORDER. Go map iteration order is latitude;
the machine's store order is representation. Consumers therefore
speak LOOKUP-vocabulary over the returned association list (the
invariant module's correspondence clauses do exactly this), never
order-vocabulary — the order is exposed only because an association
list must have one.

Definedness (the C1 well-shapedness conditions): each reader carries
a `*Shaped` predicate — the structural conditions C1 maintains — and
a `_defined` lemma (`Shaped → reader = some _`). LINEAGE: lens laws /
separation-logic locality of pure heap projections (the RenCongr
family's classic), nothing new.

QUANTIFIER LINE (the wave's): vocabulary only — advances no
end-theorem quantifier; every clause of `I` that mentions checker
state consumes these readers. -/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.Lens GoLean.Frame

/-! ## TypeIds (pinned, the AbsTwinRead convention) -/

/-- The S2 slot struct's TypeId (twin-lib.go:154-158, lowered as
`main.slot` — the shape the pinned `s2Guard` reads). -/
def slotTid : TypeId := ⟨"main.slot"⟩

/-- `raftpb.Entry`'s TypeId (the `absEntry` reader's match target). -/
def entryTid : TypeId := ⟨"raftpb.Entry"⟩

/-- `raftpb.Message`'s TypeId (the `absMessage` reader's field tag). -/
def msgTid : TypeId := ⟨"raftpb.Message"⟩

/-! ## Pure decoders (loc-free; `_ren` is definitional) -/

/-- A machine int of ANY kind (the `AbsTwinRead.readIntField`
convention for the twin's own scalar fields: non-pointer scalars whose
zero value is `.int 0 _`; fail closed on every other shape, `.nil`
included). -/
def asIntAny : GoValue → Option Int
  | .int v _ => some v
  | _ => none

/-- A machine string, or nothing. -/
def readStr : GoValue → Option GoString
  | .string s => some s
  | _ => none

/-- Field lookup + any-kind int decode (value level). -/
def intField (fs : Array (String × GoValue)) (n : String) : Option Int :=
  (StructFields.lookup fs n).bind asIntAny

theorem asIntAny_ren (r : Nat → Nat) (v : GoValue) :
    asIntAny (renameValue r v) = asIntAny v := by
  cases v <;> rfl

theorem readStr_ren (r : Nat → Nat) (v : GoValue) :
    readStr (renameValue r v) = readStr v := by
  cases v <;> rfl

/-- The slot decode (an EMBEDDED value — `main.slot` is a value type,
so `byIndex`'s map values carry the struct inline; no heap hop):
`(term, data, node)`. -/
def decSlot (v : GoValue) : Option (Int × GoString × Int) := do
  let t ← (fieldOfValue v slotTid "term").bind asIntAny
  let d ← (fieldOfValue v slotTid "data").bind readStr
  let n ← (fieldOfValue v slotTid "node").bind asIntAny
  pure (t, d, n)

theorem decSlot_ren (r : Nat → Nat) (v : GoValue) :
    decSlot (renameValue r v) = decSlot v := by
  unfold decSlot
  rw [fieldOfValue_ren, fieldOfValue_ren, fieldOfValue_ren]
  cases htv : fieldOfValue v slotTid "term" with
  | none => rfl
  | some tv =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some,
        asIntAny_ren]
      cases asIntAny tv with
      | none => rfl
      | some t =>
          simp only [Option.bind_some]
          cases hdv : fieldOfValue v slotTid "data" with
          | none => rfl
          | some dv =>
              simp only [Option.map_some, Option.bind_some, readStr_ren]
              cases readStr dv with
              | none => rfl
              | some d =>
                  simp only [Option.bind_some]
                  cases hnv : fieldOfValue v slotTid "node" with
                  | none => rfl
                  | some nv =>
                      simp only [Option.map_some, Option.bind_some,
                        asIntAny_ren]

/-! ## The map lens (`mapRead`) — NEW here, file-local until a second
consumer bites -/

/-- The pure entry walk: decode every `(key, value)` pair, fail
closed on any entry either decoder refuses. -/
def mapPairs {κ ν : Type} (dk : GoValue → Option κ) (dv : GoValue → Option ν) :
    List (GoValue × GoValue) → Option (List (κ × ν))
  | [] => some []
  | (k, v) :: rest => do
      let k' ← dk k
      let v' ← dv v
      let rest' ← mapPairs dk dv rest
      pure ((k', v') :: rest')

/-- **THE MAP LENS**: a map value's entries through its `mapData`
cell, each pair decoded. Fail closed: nil map, dangling base, or a
non-`mapData` cell → `none` (the twin's checker maps are `make`d in
`newTwin`, so a nil map at a loop head is a mis-shape, not a state). -/
def mapRead {κ ν : Type} (σ : ExecState) (mv : GoValue)
    (dk : GoValue → Option κ) (dv : GoValue → Option ν) :
    Option (List (κ × ν)) :=
  match mv with
  | .map ⟨some b⟩ =>
      (Heap.lookup σ.heap b).bind fun c =>
        match c.value with
        | .mapData es => mapPairs dk dv es.toList
        | _ => none
  | _ => none

theorem mapPairs_ren {κ ν : Type} {r : Nat → Nat}
    {dk : GoValue → Option κ} {dv : GoValue → Option ν}
    (hk : ∀ v, dk (renameValue r v) = dk v)
    (hv : ∀ v, dv (renameValue r v) = dv v) :
    ∀ es : List (GoValue × GoValue),
      mapPairs dk dv (renameValueEntries r es) = mapPairs dk dv es := by
  intro es
  induction es with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [renameValueEntries, mapPairs, hk, hv, ih]

/-- The map-lens congruence under `FrameSim` (loc-free decoders
transport verbatim — the L4 shape at the map lens). -/
theorem mapRead_ren {κ ν : Type} {r : Nat → Nat} {na₀ na : Nat}
    {fr : Heap} {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {dk : GoValue → Option κ} {dv : GoValue → Option ν}
    (hk : ∀ v, dk (renameValue r v) = dk v)
    (hv : ∀ v, dv (renameValue r v) = dv v)
    {mv : GoValue} {xs : List (κ × ν)}
    (h : mapRead σ mv dk dv = some xs) :
    mapRead σF (renameValue r mv) dk dv = some xs := by
  cases mv with
  | map m =>
      obtain ⟨ob⟩ := m
      cases ob with
      | none => simp [mapRead] at h
      | some b =>
          simp only [mapRead, renameValue, Option.map_some] at h ⊢
          cases hc : Heap.lookup σ.heap b with
          | none => rw [hc] at h; cases h
          | some c =>
              rw [hc] at h
              rw [hF.lookup_some hc]
              simp only [Option.bind_some] at h ⊢
              rw [show (renameCell r c).value = renameValue r c.value
                from rfl]
              cases hcv : c.value <;> rw [hcv] at h <;>
                simp only [renameValue] at * <;> try cases h
              case mapData es =>
                rw [List.toList_toArray, mapPairs_ren hk hv]
                exact h
  | _ => simp [mapRead] at h

/-! ## The deref-field lens (`locField`) — the shared spine of every
reader below -/

/-- Field readout at a heap LOCATION with a TypeId check (the
`fieldRead` shape generalized off `.base`-only addresses — the twin
cell is addressed by a `Loc`, the `absTwinRead` convention). -/
def locField (σ : ExecState) (l : Loc) (tid : TypeId) (f : String) :
    Option GoValue :=
  (Heap.lookup σ.heap l).bind fun c => fieldOfValue c.value tid f

theorem locField_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {l : Loc} {tid : TypeId} {f : String} {x : GoValue}
    (h : locField σ l tid f = some x) :
    locField σF (renameLoc r l) tid f = some (renameValue r x) := by
  unfold locField at h ⊢
  cases hc : Heap.lookup σ.heap l with
  | none => rw [hc] at h; cases h
  | some c =>
      rw [hc] at h
      rw [hF.lookup_some hc]
      simp only [Option.bind_some] at h ⊢
      rw [show (renameCell r c).value = renameValue r c.value from rfl,
        fieldOfValue_ren, h]
      rfl

/-- The pointer form (`.addr` deref + field): the node/message/entry
cells are reached through pointer values. -/
def ptrField (σ : ExecState) (v : GoValue) (tid : TypeId) (f : String) :
    Option GoValue :=
  match v with
  | .addr l => locField σ l tid f
  | _ => none

theorem ptrField_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {tid : TypeId} {f : String} {x : GoValue}
    (h : ptrField σ v tid f = some x) :
    ptrField σF (renameValue r v) tid f = some (renameValue r x) := by
  cases v with
  | addr l => exact locField_ren hF h
  | _ => simp [ptrField] at h

/-! ## READER 1/2 — the checker maps (`leaderOf`, `byIndex`) -/

/-- **THE `leaderOf` READER** (C3's S1 map): the twin cell at `tl`,
its `leaderOf` field, the entries decoded as `(term, claimer)` int
pairs. Association-list vocabulary (store order; lookup-only
consumption — module docstring). -/
def absLeaderOf (σ : ExecState) (tl : Loc) : Option (List (Int × Int)) :=
  (locField σ tl twinTid "leaderOf").bind fun mv =>
    mapRead σ mv asIntAny asIntAny

/-- **THE `byIndex` READER** (C3's S2 map): entries decoded as
`(index, (term, data, firstNode))`. -/
def absByIndex (σ : ExecState) (tl : Loc) :
    Option (List (Int × (Int × GoString × Int))) :=
  (locField σ tl twinTid "byIndex").bind fun mv =>
    mapRead σ mv asIntAny decSlot

theorem absLeaderOf_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {tl : Loc} {m : List (Int × Int)}
    (h : absLeaderOf σ tl = some m) :
    absLeaderOf σF (renameLoc r tl) = some m := by
  unfold absLeaderOf at h ⊢
  obtain ⟨mv, hmv, h⟩ := Option.bind_eq_some_iff.mp h
  rw [locField_ren hF hmv]
  simp only [Option.bind_some]
  exact mapRead_ren hF (asIntAny_ren r) (asIntAny_ren r) h

theorem absByIndex_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {tl : Loc} {m : List (Int × (Int × GoString × Int))}
    (h : absByIndex σ tl = some m) :
    absByIndex σF (renameLoc r tl) = some m := by
  unfold absByIndex at h ⊢
  obtain ⟨mv, hmv, h⟩ := Option.bind_eq_some_iff.mp h
  rw [locField_ren hF hmv]
  simp only [Option.bind_some]
  exact mapRead_ren hF (asIntAny_ren r) (decSlot_ren r) h

/-! ## READER 3/4 — the per-node cursors and `got` map

Navigation: the twin's `nodes` slice, element `i`, through the node
pointer to the `main.twinNode` cell — `absTwinNodeRaft`'s walk, with
the harness fields read instead of the deep `rn` hop. Stated as a
whole-list `sliceRead` (so the L4 slice law gives the `_ren`) indexed
afterwards. -/

/-- One node pointer → its S3 cursors `(applied, lastTrm)`. -/
def readNodeCursors (σ : ExecState) (v : GoValue) : Option (Int × Int) := do
  let ap ← (ptrField σ v twinNodeTid "applied").bind asIntAny
  let lt ← (ptrField σ v twinNodeTid "lastTrm").bind asIntAny
  pure (ap, lt)

/-- One node pointer → its `got` record (data ↦ flag; store order,
lookup vocabulary). -/
def readNodeGot (σ : ExecState) (v : GoValue) :
    Option (List (GoString × Bool)) :=
  (ptrField σ v twinNodeTid "got").bind fun mv =>
    mapRead σ mv readStr readBool

/-- **THE CURSORS READER**: node `i`'s `(applied, lastTrm)`. -/
def absNodeCursors (σ : ExecState) (tl : Loc) (i : Nat) :
    Option (Int × Int) :=
  ((locField σ tl twinTid "nodes").bind fun nv =>
    sliceRead σ nv readNodeCursors).bind fun l => l[i]?

/-- **THE `got` READER**: node `i`'s S4 data record. -/
def absNodeGot (σ : ExecState) (tl : Loc) (i : Nat) :
    Option (List (GoString × Bool)) :=
  ((locField σ tl twinTid "nodes").bind fun nv =>
    sliceRead σ nv readNodeGot).bind fun l => l[i]?

theorem readNodeCursors_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {p : Int × Int} (h : readNodeCursors σ v = some p) :
    readNodeCursors σF (renameValue r v) = some p := by
  unfold readNodeCursors at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨ap, hap, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨apv, hapv, hdap⟩ := Option.bind_eq_some_iff.mp hap
  obtain ⟨lt, hlt, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ltv, hltv, hdlt⟩ := Option.bind_eq_some_iff.mp hlt
  rw [ptrField_ren hF hapv]
  simp only [Option.bind_some, asIntAny_ren, hdap]
  rw [ptrField_ren hF hltv]
  simp only [Option.bind_some, asIntAny_ren, hdlt]
  exact h

theorem readNodeGot_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {g : List (GoString × Bool)}
    (h : readNodeGot σ v = some g) :
    readNodeGot σF (renameValue r v) = some g := by
  unfold readNodeGot at h ⊢
  obtain ⟨mv, hmv, h⟩ := Option.bind_eq_some_iff.mp h
  rw [ptrField_ren hF hmv]
  simp only [Option.bind_some]
  exact mapRead_ren hF (readStr_ren r) (readBool_ren r) h

theorem absNodeCursors_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {tl : Loc} {i : Nat} {p : Int × Int}
    (h : absNodeCursors σ tl i = some p) :
    absNodeCursors σF (renameLoc r tl) i = some p := by
  unfold absNodeCursors at h ⊢
  obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨nv, hnv, hsl⟩ := Option.bind_eq_some_iff.mp hl
  rw [locField_ren hF hnv]
  simp only [Option.bind_some]
  rw [sliceRead_ren hF (fun v x hx => readNodeCursors_ren hF hx) hsl]
  exact h

theorem absNodeGot_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {tl : Loc} {i : Nat} {g : List (GoString × Bool)}
    (h : absNodeGot σ tl i = some g) :
    absNodeGot σF (renameLoc r tl) i = some g := by
  unfold absNodeGot at h ⊢
  obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨nv, hnv, hsl⟩ := Option.bind_eq_some_iff.mp hl
  rw [locField_ren hF hnv]
  simp only [Option.bind_some]
  rw [sliceRead_ren hF (fun v x hx => readNodeGot_ren hF hx) hsl]
  exact h

/-! ## READER 5 — the net's entry metadata (C4's vocabulary)

[AGENT] addition beyond the charter's four (logged): the C4
population clause's "all entries EntryNormal" and the payload
clause's data axis are unstatable over `absMessage`'s `(Index, Term)`
entry projection; this reader supplies exactly the missing fields.
Alignment with `AbsTwinV0.net` is positional (both walk the same
`net` slice in order); the invariant carries the length equation as
a clause rather than a cross-module lemma against `absTwinRead`'s
private walk. -/

/-- One entry pointer → `(Type numeral, Data bytes)`. The plainpb
getter conventions ride the existing shims: `Type` through `derefI32`
(nil → 0 = EntryNormal, exactly `GetType`), `Data` as a byte list
(nil slice → empty, Go's nil slice IS the empty slice). -/
def absEntryMeta (σ : ExecState) (v : GoValue) : Option (Int × List Int) := do
  let ty ← (ptrField σ v entryTid "Type").bind (derefI32 σ)
  let dv ← ptrField σ v entryTid "Data"
  let data ← sliceRead σ dv (fun _ w => readIntK .uint8 w)
  pure (ty, data)

/-- One message pointer → its entries' metadata, in entry order. -/
def absMsgMeta (σ : ExecState) (v : GoValue) :
    Option (List (Int × List Int)) :=
  (ptrField σ v msgTid "Entries").bind fun entsv =>
    sliceRead σ entsv absEntryMeta

/-- **THE NET-METADATA READER**: per net message (in `net` slice
order — positionally aligned with `AbsTwinV0.net`), the entries'
`(Type, Data)` list. -/
def absNetMeta (σ : ExecState) (tl : Loc) :
    Option (List (List (Int × List Int))) :=
  (locField σ tl twinTid "net").bind fun nv =>
    sliceRead σ nv absMsgMeta

theorem absEntryMeta_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {m : Int × List Int} (h : absEntryMeta σ v = some m) :
    absEntryMeta σF (renameValue r v) = some m := by
  unfold absEntryMeta at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨ty, hty, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tyv, htyv, hdty⟩ := Option.bind_eq_some_iff.mp hty
  obtain ⟨dv, hdv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨data, hdata, h⟩ := Option.bind_eq_some_iff.mp h
  rw [ptrField_ren hF htyv]
  simp only [Option.bind_some]
  rw [derefI32_ren hF hdty]
  simp only [Option.bind_some]
  rw [ptrField_ren hF hdv]
  simp only [Option.bind_some]
  rw [sliceRead_ren hF (fun w x hx => by rw [readIntK_ren]; exact hx) hdata]
  simpa using h

theorem absMsgMeta_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {ms : List (Int × List Int)}
    (h : absMsgMeta σ v = some ms) :
    absMsgMeta σF (renameValue r v) = some ms := by
  unfold absMsgMeta at h ⊢
  obtain ⟨entsv, hentsv, h⟩ := Option.bind_eq_some_iff.mp h
  rw [ptrField_ren hF hentsv]
  simp only [Option.bind_some]
  exact sliceRead_ren hF (fun w x hx => absEntryMeta_ren hF hx) h

theorem absNetMeta_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {tl : Loc} {ms : List (List (Int × List Int))}
    (h : absNetMeta σ tl = some ms) :
    absNetMeta σF (renameLoc r tl) = some ms := by
  unfold absNetMeta at h ⊢
  obtain ⟨nv, hnv, h⟩ := Option.bind_eq_some_iff.mp h
  rw [locField_ren hF hnv]
  simp only [Option.bind_some]
  exact sliceRead_ren hF (fun w x hx => absMsgMeta_ren hF hx) h

/-! ## Definedness under the C1 well-shapedness conditions

The `*Shaped` predicates are the structural conditions the invariant's
C1 clause maintains; each `_defined` lemma is the promised
"well-shaped ⇒ the reader is defined". Two generic spines (the map
field, the slice field), instantiated per reader. -/

/-- Every entry of a list decodes (the map lens's element condition). -/
theorem mapPairs_defined {κ ν : Type} {dk : GoValue → Option κ}
    {dv : GoValue → Option ν} :
    ∀ {es : List (GoValue × GoValue)},
      (∀ p ∈ es, (dk p.1).isSome ∧ (dv p.2).isSome) →
      ∃ xs, mapPairs dk dv es = some xs := by
  intro es
  induction es with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons p rest ih =>
      intro h
      obtain ⟨k, v⟩ := p
      obtain ⟨hk, hv⟩ := h (k, v) (List.mem_cons_self ..)
      obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hk
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hv
      obtain ⟨rest', hrest'⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      exact ⟨(k', v') :: rest', by
        simp only [mapPairs, hk', hv', hrest']; rfl⟩

/-- The slice walk succeeds when every window element decodes. -/
theorem sliceElems_defined {α : Type} {σ : ExecState} {vs : Array GoValue}
    {elem : ExecState → GoValue → Option α} :
    ∀ (i n : Nat),
      (∀ j, j < n → ∃ v x, vs[i + j]? = some v ∧ elem σ v = some x) →
      ∃ xs, sliceElems σ vs elem i n = some xs := by
  intro i n
  induction n generalizing i with
  | zero => exact fun _ => ⟨[], rfl⟩
  | succ n ih =>
      intro h
      obtain ⟨v, x, hv, hx⟩ := h 0 (Nat.succ_pos n)
      rw [Nat.add_zero] at hv
      obtain ⟨rest, hrest⟩ := ih (i + 1) (fun j hj => by
        obtain ⟨v', x', hv', hx'⟩ := h (j + 1) (Nat.succ_lt_succ hj)
        rw [show i + (j + 1) = i + 1 + j by omega] at hv'
        exact ⟨v', x', hv', hx'⟩)
      refine ⟨x :: rest, ?_⟩
      unfold sliceElems
      rw [hv]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [hx]
      simp only [Option.bind_some]
      rw [hrest]
      rfl

/-- The slice walk's length is the window length (the indexing
lemma's fuel). -/
theorem sliceElems_length {α : Type} {σ : ExecState} {vs : Array GoValue}
    {elem : ExecState → GoValue → Option α} :
    ∀ {i n : Nat} {xs : List α},
      sliceElems σ vs elem i n = some xs → xs.length = n := by
  intro i n
  induction n generalizing i with
  | zero =>
      intro xs h
      cases h
      rfl
  | succ n ih =>
      intro xs h
      unfold sliceElems at h
      simp only [Option.bind_eq_bind] at h
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := (Option.some.inj h).symm
      simp only [List.length_cons, ih hrest]

/-- **The map-field shape** (C1 vocabulary): the cell at `tl` is a
`twinTid` struct whose field `f` is a live map whose entries all
decode. -/
def MapFieldShaped {κ ν : Type} (σ : ExecState) (tl : Loc) (f : String)
    (dk : GoValue → Option κ) (dv : GoValue → Option ν) : Prop :=
  ∃ tc fs b c es,
    Heap.lookup σ.heap tl = some tc ∧
    tc.value = .struct twinTid fs ∧
    StructFields.lookup fs f = some (.map ⟨some b⟩) ∧
    Heap.lookup σ.heap b = some c ∧
    c.value = .mapData es ∧
    ∀ p ∈ es.toList, (dk p.1).isSome ∧ (dv p.2).isSome

theorem mapField_defined {κ ν : Type} {σ : ExecState} {tl : Loc}
    {f : String} {dk : GoValue → Option κ} {dv : GoValue → Option ν}
    (h : MapFieldShaped σ tl f dk dv) :
    ∃ m, (locField σ tl twinTid f).bind
      (fun mv => mapRead σ mv dk dv) = some m := by
  obtain ⟨tc, fs, b, c, es, htc, hval, hf, hb, hes, hall⟩ := h
  obtain ⟨m, hm⟩ := mapPairs_defined hall
  refine ⟨m, ?_⟩
  unfold locField fieldOfValue
  rw [htc]
  simp only [Option.bind_some, hval]
  rw [if_pos (by rfl), hf]
  simp only [Option.bind_some]
  show (Heap.lookup σ.heap b).bind
      (fun c => match c.value with
        | .mapData es => mapPairs dk dv es.toList
        | _ => none) = some m
  rw [hb]
  simp only [Option.bind_some, hes]
  exact hm

/-- **The slice-field shape** (C1 vocabulary): the cell at `tl` is a
`twinTid` struct whose field `f` is a live slice of length `n` over a
backing array whose window elements all decode. -/
def SliceFieldShaped {α : Type} (σ : ExecState) (tl : Loc) (f : String)
    (elem : ExecState → GoValue → Option α) (n : Nat) : Prop :=
  ∃ tc fs b off cap c vs,
    Heap.lookup σ.heap tl = some tc ∧
    tc.value = .struct twinTid fs ∧
    StructFields.lookup fs f = some (.slice ⟨some b, off, n, cap⟩) ∧
    Heap.lookup σ.heap b = some c ∧
    c.value = .array vs ∧
    ∀ j, j < n → ∃ v x, vs[off + j]? = some v ∧ elem σ v = some x

theorem sliceField_defined {α : Type} {σ : ExecState} {tl : Loc}
    {f : String} {elem : ExecState → GoValue → Option α} {n : Nat}
    (h : SliceFieldShaped σ tl f elem n) :
    ∃ xs, (locField σ tl twinTid f).bind
        (fun nv => sliceRead σ nv elem) = some xs
      ∧ xs.length = n := by
  obtain ⟨tc, fs, b, off, cap, c, vs, htc, hval, hf, hb, hvs, hall⟩ := h
  obtain ⟨xs, hxs⟩ := sliceElems_defined off n hall
  refine ⟨xs, ?_, sliceElems_length hxs⟩
  unfold locField fieldOfValue
  rw [htc]
  simp only [Option.bind_some, hval]
  rw [if_pos (by rfl), hf]
  simp only [Option.bind_some]
  show (Heap.lookup σ.heap b).bind
      (fun cell => match cell.value with
        | .array vs => sliceElems σ vs elem off n
        | _ => none) = some xs
  rw [hb]
  simp only [Option.bind_some, hvs]
  exact hxs

/-! ### The per-reader instantiations -/

def LeaderOfShaped (σ : ExecState) (tl : Loc) : Prop :=
  MapFieldShaped σ tl "leaderOf" asIntAny asIntAny

def ByIndexShaped (σ : ExecState) (tl : Loc) : Prop :=
  MapFieldShaped σ tl "byIndex" asIntAny decSlot

def NodeCursorsShaped (σ : ExecState) (tl : Loc) (n : Nat) : Prop :=
  SliceFieldShaped σ tl "nodes" readNodeCursors n

def NodeGotShaped (σ : ExecState) (tl : Loc) (n : Nat) : Prop :=
  SliceFieldShaped σ tl "nodes" readNodeGot n

def NetMetaShaped (σ : ExecState) (tl : Loc) (n : Nat) : Prop :=
  SliceFieldShaped σ tl "net" absMsgMeta n

theorem absLeaderOf_defined {σ : ExecState} {tl : Loc}
    (h : LeaderOfShaped σ tl) : ∃ m, absLeaderOf σ tl = some m :=
  mapField_defined h

theorem absByIndex_defined {σ : ExecState} {tl : Loc}
    (h : ByIndexShaped σ tl) : ∃ m, absByIndex σ tl = some m :=
  mapField_defined h

theorem absNodeCursors_defined {σ : ExecState} {tl : Loc} {n i : Nat}
    (h : NodeCursorsShaped σ tl n) (hi : i < n) :
    ∃ p, absNodeCursors σ tl i = some p := by
  obtain ⟨xs, hxs, hlen⟩ := sliceField_defined h
  refine ⟨xs[i]'(hlen ▸ hi), ?_⟩
  unfold absNodeCursors
  rw [hxs]
  simp only [Option.bind_some]
  exact List.getElem?_eq_getElem (hlen ▸ hi)

theorem absNodeGot_defined {σ : ExecState} {tl : Loc} {n i : Nat}
    (h : NodeGotShaped σ tl n) (hi : i < n) :
    ∃ g, absNodeGot σ tl i = some g := by
  obtain ⟨xs, hxs, hlen⟩ := sliceField_defined h
  refine ⟨xs[i]'(hlen ▸ hi), ?_⟩
  unfold absNodeGot
  rw [hxs]
  simp only [Option.bind_some]
  exact List.getElem?_eq_getElem (hlen ▸ hi)

theorem absNetMeta_defined {σ : ExecState} {tl : Loc} {n : Nat}
    (h : NetMetaShaped σ tl n) :
    ∃ ms, absNetMeta σ tl = some ms ∧ ms.length = n :=
  sliceField_defined h

/-! ## READER 6 — the tracker Progress vocabulary (W3 U3.0d)

Charter Amendment 1's probe-state vocabulary: the leader's
per-follower `tracker.Progress` data (`Match`/`Next`/`State` incl.
StateProbe, the `Inflights` window's count/size) plus the raft cell's
`raftLog` hop into the LANDED `absRaftLog` view (`AbsStateV2`) — the
concrete log-length axis the Progress consistency facts (invariant
C2) are stated against. Navigation: raft cell → embedded `trk`
struct → `Progress` map → per-id `*tracker.Progress` cell →
scalar fields + the `*Inflights` hop.

The map values here are POINTERS, so the pure-decoder `mapRead`
cannot carry the element decode — `mapReadD` below is the
σ-DEPENDENT sibling (dv reads the heap). Kept beside `mapRead`
rather than replacing it: the three landed pure-decoder consumers
keep their lemma chains untouched; promotion of the pair into one
generalized lens is a recorded candidate when a third map-reader
class bites (promotion ledger). -/

/-- `raft.raft`'s TypeId (the deep cell the trackers live in). -/
def raftTid : TypeId := ⟨"raft.raft"⟩

/-- `tracker.ProgressTracker`'s TypeId (the embedded `trk` value). -/
def trackerTid : TypeId := ⟨"tracker.ProgressTracker"⟩

/-- `tracker.Progress`'s TypeId (the per-follower cell). -/
def progressTid : TypeId := ⟨"tracker.Progress"⟩

/-- `tracker.Inflights`'s TypeId. -/
def inflightsTid : TypeId := ⟨"tracker.Inflights"⟩

/-- One follower's abstract Progress: the scalar probe-state axes
(`State` is the `tracker.StateType` numeral — 0 probe, 1 replicate,
2 snapshot) plus the inflights window's count/size. Loc-free output —
`_ren` transports verbatim. -/
structure AbsProgress where
  matchIdx : Int
  nextIdx : Int
  state : Int
  infCount : Int
  infSize : Int
  deriving Repr, DecidableEq

/-- The σ-dependent pair walk (the `mapPairs` sibling for heap-reading
value decoders; keys stay pure — Go map keys are scalars here). -/
def mapPairsD {κ ν : Type} (σ : ExecState) (dk : GoValue → Option κ)
    (dv : ExecState → GoValue → Option ν) :
    List (GoValue × GoValue) → Option (List (κ × ν))
  | [] => some []
  | (k, v) :: rest => do
      let k' ← dk k
      let v' ← dv σ v
      let rest' ← mapPairsD σ dk dv rest
      pure ((k', v') :: rest')

/-- The σ-dependent map lens (`mapRead`'s sibling for pointer-valued
maps; same fail-closed arms). -/
def mapReadD {κ ν : Type} (σ : ExecState) (mv : GoValue)
    (dk : GoValue → Option κ) (dv : ExecState → GoValue → Option ν) :
    Option (List (κ × ν)) :=
  match mv with
  | .map ⟨some b⟩ =>
      (Heap.lookup σ.heap b).bind fun c =>
        match c.value with
        | .mapData es => mapPairsD σ dk dv es.toList
        | _ => none
  | _ => none

theorem mapPairsD_ren {κ ν : Type} {r : Nat → Nat}
    {σ σF : ExecState}
    {dk : GoValue → Option κ} {dv : ExecState → GoValue → Option ν}
    (hk : ∀ v, dk (renameValue r v) = dk v)
    (hv : ∀ v x, dv σ v = some x → dv σF (renameValue r v) = some x) :
    ∀ {es : List (GoValue × GoValue)} {xs : List (κ × ν)},
      mapPairsD σ dk dv es = some xs →
      mapPairsD σF dk dv (renameValueEntries r es) = some xs := by
  intro es
  induction es with
  | nil => intro xs h; exact h
  | cons p rest ih =>
      intro xs h
      obtain ⟨k, v⟩ := p
      simp only [mapPairsD, Option.bind_eq_bind] at h
      obtain ⟨k', hk', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v', hv', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest', hrest', h⟩ := Option.bind_eq_some_iff.mp h
      simp only [renameValueEntries, mapPairsD, Option.bind_eq_bind, hk, hk',
        Option.bind_some, hv _ _ hv', ih hrest']
      exact h

theorem mapReadD_ren {κ ν : Type} {r : Nat → Nat} {na₀ na : Nat}
    {fr : Heap} {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {dk : GoValue → Option κ} {dv : ExecState → GoValue → Option ν}
    (hk : ∀ v, dk (renameValue r v) = dk v)
    (hv : ∀ v x, dv σ v = some x → dv σF (renameValue r v) = some x)
    {mv : GoValue} {xs : List (κ × ν)}
    (h : mapReadD σ mv dk dv = some xs) :
    mapReadD σF (renameValue r mv) dk dv = some xs := by
  cases mv with
  | map m =>
      obtain ⟨ob⟩ := m
      cases ob with
      | none => simp [mapReadD] at h
      | some b =>
          simp only [mapReadD, renameValue, Option.map_some] at h ⊢
          cases hc : Heap.lookup σ.heap b with
          | none => rw [hc] at h; cases h
          | some c =>
              rw [hc] at h
              rw [hF.lookup_some hc]
              simp only [Option.bind_some] at h ⊢
              rw [show (renameCell r c).value = renameValue r c.value
                from rfl]
              cases hcv : c.value <;> rw [hcv] at h <;>
                simp only [renameValue] at * <;> try cases h
              case mapData es =>
                rw [List.toList_toArray, mapPairsD_ren hk hv h]
  | _ => simp [mapReadD] at h

/-- The inflights hop: `*tracker.Inflights` → `(count, size)`. -/
def readInflights (σ : ExecState) (v : GoValue) : Option (Int × Int) := do
  let c ← (ptrField σ v inflightsTid "count").bind asIntAny
  let s ← (ptrField σ v inflightsTid "size").bind asIntAny
  pure (c, s)

/-- One Progress pointer → its abstract Progress. -/
def readProgress (σ : ExecState) (v : GoValue) : Option AbsProgress := do
  let m ← (ptrField σ v progressTid "Match").bind asIntAny
  let n ← (ptrField σ v progressTid "Next").bind asIntAny
  let st ← (ptrField σ v progressTid "State").bind asIntAny
  let infv ← ptrField σ v progressTid "Inflights"
  let inf ← readInflights σ infv
  pure ⟨m, n, st, inf.1, inf.2⟩

/-- **THE PROGRESS READER**: the raft cell at `.base a` (the address
`absTwinNodeRaft` yields), its embedded tracker's `Progress` map as
`(id ↦ AbsProgress)` pairs. Store order; lookup-vocabulary consumption
only (module docstring). -/
def absProgressOf (σ : ExecState) (a : Addr) :
    Option (List (Int × AbsProgress)) :=
  (locField σ (.base a) raftTid "trk").bind fun trkv =>
    (fieldOfValue trkv trackerTid "Progress").bind fun mv =>
      mapReadD σ mv asIntAny readProgress

/-- **THE LOG-VIEW HOP**: the raft cell's `raftLog` pointer followed
into the landed `absRaftLog` view (AbsStateV2) — the concrete
log-length vocabulary the Progress consistency facts consume
(`AbsLog.lastIndex`). -/
def absRaftLogOf (σ : ExecState) (a : Addr) : Option AbsLog :=
  match locField σ (.base a) raftTid "raftLog" with
  | some (.addr (.base rl)) => absRaftLog σ rl
  | _ => none

theorem readInflights_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {p : Int × Int} (h : readInflights σ v = some p) :
    readInflights σF (renameValue r v) = some p := by
  unfold readInflights at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cv, hcv, hdc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sv, hsv, hds⟩ := Option.bind_eq_some_iff.mp hs
  rw [ptrField_ren hF hcv]
  simp only [Option.bind_some, asIntAny_ren, hdc]
  rw [ptrField_ren hF hsv]
  simp only [Option.bind_some, asIntAny_ren, hds]
  exact h

theorem readProgress_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {p : AbsProgress} (h : readProgress σ v = some p) :
    readProgress σF (renameValue r v) = some p := by
  unfold readProgress at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨mv, hmv, hdm⟩ := Option.bind_eq_some_iff.mp hm
  obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨nv, hnv, hdn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨stv, hstv, hdst⟩ := Option.bind_eq_some_iff.mp hst
  obtain ⟨infv, hinfv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨inf, hinf, h⟩ := Option.bind_eq_some_iff.mp h
  rw [ptrField_ren hF hmv]
  simp only [Option.bind_some, asIntAny_ren, hdm]
  rw [ptrField_ren hF hnv]
  simp only [Option.bind_some, asIntAny_ren, hdn]
  rw [ptrField_ren hF hstv]
  simp only [Option.bind_some, asIntAny_ren, hdst]
  rw [ptrField_ren hF hinfv]
  simp only [Option.bind_some]
  rw [readInflights_ren hF hinf]
  simpa using h

theorem absProgressOf_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {pm : List (Int × AbsProgress)}
    (h : absProgressOf σ a = some pm) :
    absProgressOf σF ⟨r a.id⟩ = some pm := by
  unfold absProgressOf at h ⊢
  obtain ⟨trkv, htrkv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨mv, hmv, h⟩ := Option.bind_eq_some_iff.mp h
  have hloc : locField σF (renameLoc r (.base a)) raftTid "trk"
      = some (renameValue r trkv) := locField_ren hF htrkv
  rw [show renameLoc r (.base a) = Loc.base ⟨r a.id⟩ from rfl] at hloc
  rw [hloc]
  simp only [Option.bind_some]
  rw [fieldOfValue_ren, hmv]
  simp only [Option.map_some, Option.bind_some]
  exact mapReadD_ren hF (asIntAny_ren r)
    (fun v x hx => readProgress_ren hF hx) h

theorem absRaftLogOf_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {L : AbsLog} (h : absRaftLogOf σ a = some L) :
    absRaftLogOf σF ⟨r a.id⟩ = some L := by
  unfold absRaftLogOf at h ⊢
  cases hv : locField σ (.base a) raftTid "raftLog" with
  | none => rw [hv] at h; cases h
  | some v =>
      rw [hv] at h
      have hloc : locField σF (renameLoc r (.base a)) raftTid "raftLog"
          = some (renameValue r v) := locField_ren hF hv
      rw [show renameLoc r (.base a) = Loc.base ⟨r a.id⟩ from rfl] at hloc
      rw [hloc]
      cases v <;> try cases h
      case addr l =>
        cases l <;> try cases h
        case base rl => exact absRaftLog_ren hF h

/-- Definedness of the σ-dependent pair walk (the `mapPairs_defined`
sibling). -/
theorem mapPairsD_defined {κ ν : Type} {σ : ExecState}
    {dk : GoValue → Option κ} {dv : ExecState → GoValue → Option ν} :
    ∀ {es : List (GoValue × GoValue)},
      (∀ p ∈ es, (dk p.1).isSome ∧ (dv σ p.2).isSome) →
      ∃ xs, mapPairsD σ dk dv es = some xs := by
  intro es
  induction es with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons p rest ih =>
      intro h
      obtain ⟨k, v⟩ := p
      obtain ⟨hk, hv⟩ := h (k, v) (List.mem_cons_self ..)
      obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hk
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hv
      obtain ⟨rest', hrest'⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      exact ⟨(k', v') :: rest', by
        simp only [mapPairsD, hk', hv', hrest']; rfl⟩

/-- **The Progress shape** (C1/C2 vocabulary): the raft cell at
`.base a` is a `raft.raft` struct whose embedded `trk` is a
`tracker.ProgressTracker` whose `Progress` field is a live map whose
entries all decode. -/
def ProgressShaped (σ : ExecState) (a : Addr) : Prop :=
  ∃ cell fs trkv pfs b c es,
    Heap.lookup σ.heap (.base a) = some cell ∧
    cell.value = .struct raftTid fs ∧
    StructFields.lookup fs "trk" = some trkv ∧
    trkv = .struct trackerTid pfs ∧
    StructFields.lookup pfs "Progress" = some (.map ⟨some b⟩) ∧
    Heap.lookup σ.heap b = some c ∧
    c.value = .mapData es ∧
    ∀ p ∈ es.toList, (asIntAny p.1).isSome ∧ (readProgress σ p.2).isSome

theorem absProgressOf_defined {σ : ExecState} {a : Addr}
    (h : ProgressShaped σ a) : ∃ pm, absProgressOf σ a = some pm := by
  obtain ⟨cell, fs, trkv, pfs, b, c, es, hc, hval, htrk, htv, hp, hb,
    hes, hall⟩ := h
  obtain ⟨pm, hpm⟩ := mapPairsD_defined hall
  refine ⟨pm, ?_⟩
  unfold absProgressOf locField fieldOfValue
  rw [hc]
  simp only [Option.bind_some, hval]
  rw [if_pos (by rfl), htrk]
  simp only [Option.bind_some, htv]
  rw [if_pos (by rfl), hp]
  simp only [Option.bind_some]
  show (Heap.lookup σ.heap b).bind
      (fun c => match c.value with
        | .mapData es => mapPairsD σ asIntAny readProgress es.toList
        | _ => none) = some pm
  rw [hb]
  simp only [Option.bind_some, hes]
  exact hpm

/-! ## Non-vacuity checks (the definedness premises are satisfiable:
one three-cell state exercising the map lens and the cursors walk
end-to-end; the Lens `wLens` convention) -/

private def wTwinState : ExecState :=
  { heap := [(.base ⟨0⟩,
      { declaredTy := none
        value := .struct twinTid
          #[("nodes", .slice ⟨some (.base ⟨1⟩), 0, 1, 1⟩),
            ("leaderOf", .map ⟨some (.base ⟨2⟩)⟩)] }),
     (.base ⟨1⟩,
      { declaredTy := none
        value := .array #[.addr (.base ⟨3⟩)] }),
     (.base ⟨2⟩,
      { declaredTy := none
        value := .mapData #[(.int 2 .uint64, .int 1 .uint64)] }),
     (.base ⟨3⟩,
      { declaredTy := none
        value := .struct twinNodeTid
          #[("applied", .int 3 .uint64), ("lastTrm", .int 2 .uint64)] })]
    nextAddr := 4 }

theorem wTwin_leaderOf :
    absLeaderOf wTwinState (.base ⟨0⟩) = some [(2, 1)] := by rfl

theorem wTwin_cursors :
    absNodeCursors wTwinState (.base ⟨0⟩) 0 = some (3, 2) := by rfl

theorem wTwin_leaderOfShaped : LeaderOfShaped wTwinState (.base ⟨0⟩) := by
  refine ⟨_, _, .base ⟨2⟩, _, _, rfl, rfl, by rfl, rfl, rfl, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp'
  · exact ⟨rfl, rfl⟩
  · exact absurd hp' (List.not_mem_nil)

/-- Non-vacuity for the U3.0d Progress reader: a four-cell state
(raft cell → embedded trk → Progress map → one Progress cell →
Inflights cell) the reader decodes end-to-end. -/
private def wProgState : ExecState :=
  { heap := [(.base ⟨0⟩,
      { declaredTy := none
        value := .struct raftTid
          #[("trk", .struct trackerTid
              #[("Progress", .map ⟨some (.base ⟨1⟩)⟩)])] }),
     (.base ⟨1⟩,
      { declaredTy := none
        value := .mapData #[(.int 2 .uint64, .addr (.base ⟨2⟩))] }),
     (.base ⟨2⟩,
      { declaredTy := none
        value := .struct progressTid
          #[("Match", .int 1 .uint64), ("Next", .int 2 .uint64),
            ("State", .int 1 .uint64),
            ("Inflights", .addr (.base ⟨3⟩))] }),
     (.base ⟨3⟩,
      { declaredTy := none
        value := .struct inflightsTid
          #[("count", .int 0 .int), ("size", .int 256 .int)] })]
    nextAddr := 4 }

theorem wProg_read :
    absProgressOf wProgState ⟨0⟩ = some [(2, ⟨1, 2, 1, 0, 256⟩)] := by rfl

theorem wProg_shaped : ProgressShaped wProgState ⟨0⟩ := by
  refine ⟨_, _, _, _, .base ⟨1⟩, _, _, rfl, rfl, by rfl, rfl, by rfl,
    rfl, rfl, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp'
  · exact ⟨rfl, rfl⟩
  · exact absurd hp' (List.not_mem_nil)

end GoLean.RaftSeam
