import GoLean.GoCore.Multi
import GoLean.GoCore.MachineSound

/-!
# The emitted access trace EQUALS the footprint table — `accesses_eq_stepAccesses`
(C1 S2b, 2026-09-18; charter `docs/2026-09-17_c1-memory-module-charter.md` §3 + §7 D6)

The memory module (`Ops.lean`) EMITS every data access as the operations run; the
footprint TABLE (`stepAccesses`, `Race.lean`) COMPUTES a step's accesses from its
pre-configuration by a curated per-shape table. Since C1 S2a both accounts exist in one
binary and the tracer compares them per step over the whole corpus and the raft twin
(0 mismatches). This file is the UNIVERSAL companion the charter asks for (D6 (c)): a
kernel-checked proof, per rule of the labelled relation `Step`, that the step's LABEL is
the table's account — EXACTLY, not up to permutation — with ONE stated exception: a step
that DELIVERED a panic carries the label `[]` (the apply's effects are discarded, its
accesses never happened — `deliver`'s convention and, before S2b, `raceUpdate`'s «the step
panicked» rule), while the table, computed before the step, may list the accesses the
panicking apply would have performed (e.g. the map read before an unhashable key's panic).
So the statement is a disjunction: `tr = tableTrace (stepAccesses ctx s c) ∨ (tr = [] ∧
c'.isPanicking = true)`; on a non-panicking successor the two accounts coincide
(`accesses_eq_stepAccesses_of_not_panicking`). The spawn step's label is the child's
frame-entry read, `dispatchAccesses`, under the same proviso (`spawnStep_trace`).

WHAT THE DETECTOR FOLD INHERITS (S2b: `raceUpdate` reads `StepEvent.trace`). The former
fold recorded the table's account on every step except a step that BECAME panicking from a
non-panicking configuration; the new fold records the label. By this theorem the two agree
on every step whose successor is not panicking, and on a step that became panicking (both
record nothing). The ONE remaining corner: a step from an already-panicking configuration
that panics again — the deferred-call entry during unwinding (`panicFrameDefer`) whose
receiver load panics, i.e. an out-of-range element ADDRESS dereferenced by the dispatch
(`loadLoc` → `arrayGet`): the table recorded the read at the leaf, the label records
nothing — the read never happened. Unreachable from a well-formed program (an element
address is bounds-checked at its formation); recorded as the fold's one semantic
tightening in the handoff.

HOW THE PROOF IS BUILT. One lemma per emitting helper (`Mem.*_trace`, `loadResults_trace`,
`mapLookupValue_trace`, `applyStrictOp_trace`, `applyStmtOpCore_trace`/`applyStmtOp_trace`,
`enterFrame_trace` via `dynamicDispatch?_trace`, `storeTarget_trace`, `applyRhsOp_trace`,
`mapIterCandidates_trace`, the `unseq*` lemmas), each stating the helper's trace as the
table's own expression; then `accesses_eq_stepAccesses` by `cases` over the 122 rules — the
94 pure rules by reduction of the table on the configuration's shape, the 28 helper-bearing
rules by the lemmas, the apply-then-deliver rules split into the value branch (the lemma)
and the panic branch (the right disjunct). The tactic macros `trace_split`/`trace_close`/
`trace_arm` decompose an op-table arm's `do`-block hypothesis bind by bind.

THIS FILE LEAVES WITH THE TABLE IT AUDITS (charter §3: «the theorem leaves with the table,
its proving SHA recorded»): S2b-ii deletes `stepAccesses` and its family together with this
module; the handoff's §1 row names the commit at which this theorem was checked.
-/

namespace GoLean.GoCore.Machine

open GoLean

variable {ctx : ProgramCtx}

/-- The table's account as a trace: every footprint entry under the `.data` key. -/
def tableTrace (l : List RaceAccess) : AccessTrace := l.map fun a => (a.1, .data a.2)

@[simp] theorem tableTrace_nil : tableTrace [] = [] := rfl
@[simp] theorem tableTrace_cons {a : RaceAccess} {l : List RaceAccess} :
    tableTrace (a :: l) = (a.1, .data a.2) :: tableTrace l := rfl
@[simp] theorem tableTrace_append {l₁ l₂ : List RaceAccess} :
    tableTrace (l₁ ++ l₂) = tableTrace l₁ ++ tableTrace l₂ := List.map_append ..
theorem tableTrace_map {β : Type} {k : AccessKind} {f : β → Loc} {l : List β} :
    tableTrace (l.map fun x => (k, f x)) = l.map fun x => (k, .data (f x)) := by
  simp [tableTrace]

/-- `count` consecutive element accesses of kind `k` from `.index b start`. -/
def indexRun (k : AccessKind) (b : Loc) (start count : Nat) : AccessTrace :=
  (List.range' start count).map fun j => (k, .data (.index b (Int.ofNat j)))

@[simp] theorem indexRun_zero {k : AccessKind} {b : Loc} {start : Nat} : indexRun k b start 0 = [] := rfl
theorem indexRun_succ {k : AccessKind} {b : Loc} {start n : Nat} :
    indexRun k b start (n + 1) = (k, .data (.index b (Int.ofNat start))) :: indexRun k b (start + 1) n := by
  simp [indexRun, List.range'_succ]

/-- The table's element run (`sliceElemLocs`) IS the module's index run. -/
theorem tableTrace_sliceElemLocs {k : AccessKind} {b : Loc} {slice : SliceValue} {count : Nat}
    (hb : slice.base = some b) :
    tableTrace ((sliceElemLocs slice count).map ((k, ·))) = indexRun k b slice.offset count := by
  simp [sliceElemLocs, hb, indexRun, List.range'_eq_map_range, tableTrace, List.map_map, Function.comp_def]

theorem sliceElemLocs_none {slice : SliceValue} {count : Nat} (hb : slice.base = none) :
    sliceElemLocs slice count = [] := by
  simp [sliceElemLocs, hb]

/-! ## The module's operations -/

theorem Mem.load_trace {s : Store} {l : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.load ctx s l = .ok (v, tr)) : tr = [(.read, .data l)] := by
  unfold Mem.load at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, _, rfl⟩ := h
  rfl

theorem Mem.loadFor_trace {s : Store} {root leaf : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.loadFor ctx s root leaf = .ok (v, tr)) : tr = [(.read, .data leaf)] := by
  unfold Mem.loadFor at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, _, rfl⟩ := h
  rfl

theorem Mem.store_trace {s s' : Store} {l : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.store ctx s l v = .ok (s', tr)) : tr = [(.write, .data l)] := by
  unfold Mem.store at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, _, rfl⟩ := h
  rfl

theorem Mem.mapRead_trace {s : Store} {l : Loc} {p : Array (Nat × GoValue × GoValue) × Nat}
    {tr : AccessTrace} (h : Mem.mapRead s l = .ok (p, tr)) : tr = [(.read, .data l)] := by
  unfold Mem.mapRead at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, _, rfl⟩ := h
  rfl

theorem Mem.mapWrite_trace {s s' : Store} {l : Loc} {es : Array (Nat × GoValue × GoValue)} {n : Nat}
    {tr : AccessTrace} (h : Mem.mapWrite s l es n = .ok (s', tr)) : tr = [(.write, .data l)] := by
  unfold Mem.mapWrite at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, _, rfl⟩ := h
  rfl

theorem Mem.load_trace' {s : Store} {l : Loc} {r : GoValue × AccessTrace}
    (h : Mem.load ctx s l = .ok r) : r.2 = [(.read, .data l)] := by
  obtain ⟨v, t⟩ := r; exact Mem.load_trace h
theorem Mem.loadFor_trace' {s : Store} {root leaf : Loc} {r : GoValue × AccessTrace}
    (h : Mem.loadFor ctx s root leaf = .ok r) : r.2 = [(.read, .data leaf)] := by
  obtain ⟨v, t⟩ := r; exact Mem.loadFor_trace h
theorem Mem.mapRead_trace' {s : Store} {l : Loc} {r : (Array (Nat × GoValue × GoValue) × Nat) × AccessTrace}
    (h : Mem.mapRead s l = .ok r) : r.2 = [(.read, .data l)] := by
  obtain ⟨p, t⟩ := r; exact Mem.mapRead_trace h

theorem Mem.loadElems_trace {s : Store} {b : Loc} :
    ∀ {start n : Nat} {vs : List GoValue} {tr : AccessTrace},
    Mem.loadElems ctx s b start n = .ok (vs, tr) → tr = indexRun .read b start n
  | _, 0, vs, tr, h => by
      simp only [Mem.loadElems, pure_eq_ok] at h
      obtain ⟨_, rfl⟩ := h
      rfl
  | start, n + 1, vs, tr, h => by
      unfold Mem.loadElems at h
      simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨⟨v, t⟩, hv, ⟨vs', ts⟩, hrest, _, rfl⟩ := h
      rw [Mem.load_trace hv, Mem.loadElems_trace hrest, indexRun_succ]
      rfl

theorem Mem.storeElems_trace {s₀ : Store} {b : Loc} :
    ∀ {vs : List GoValue} {s : Store} {start : Nat} {s' : Store} {tr : AccessTrace},
    Mem.storeElems ctx s b start vs = .ok (s', tr) → tr = indexRun .write b start vs.length
  | [], s, start, s', tr, h => by
      simp only [Mem.storeElems, pure_eq_ok] at h
      obtain ⟨_, rfl⟩ := h
      rfl
  | v :: vs, s, start, s', tr, h => by
      unfold Mem.storeElems at h
      simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨⟨s₁, t⟩, hw, ⟨s₂, ts⟩, hrest, _, rfl⟩ := h
      rw [Mem.store_trace hw, Mem.storeElems_trace (s₀ := s₀) hrest, List.length_cons, indexRun_succ]
      rfl

theorem Mem.loadRun_trace {s : Store} {slice : SliceValue} {count : Nat} {vs : List GoValue}
    {tr : AccessTrace} (h : Mem.loadRun ctx s slice count = .ok (vs, tr)) :
    tr = tableTrace ((sliceElemLocs slice count).map ((.read, ·))) := by
  unfold Mem.loadRun at h
  split at h
  · rename_i b hb
    rw [tableTrace_sliceElemLocs hb]
    exact Mem.loadElems_trace h
  · rename_i hb
    rw [sliceElemLocs_none hb]
    split at h
    · simp only [pure_eq_ok] at h
      obtain ⟨_, rfl⟩ := h
      rfl
    · simp at h

theorem Mem.storeRun_trace {s s' : Store} {slice : SliceValue} {start : Nat} {vs : List GoValue}
    {tr : AccessTrace} (h : Mem.storeRun ctx s slice start vs = .ok (s', tr)) :
    (∃ b, slice.base = some b ∧ tr = indexRun .write b (slice.offset + start) vs.length)
      ∨ (slice.base = none ∧ vs = [] ∧ tr = []) := by
  unfold Mem.storeRun at h
  split at h
  · rename_i b hb
    exact .inl ⟨b, hb, Mem.storeElems_trace (s₀ := s) h⟩
  · rename_i hb
    split at h
    · simp only [pure_eq_ok] at h
      obtain ⟨_, rfl⟩ := h
      exact .inr ⟨hb, rfl, rfl⟩
    · simp at h

theorem Mem.loadSlice_trace {s : Store} {slice : SliceValue} {vs : Array GoValue}
    {tr : AccessTrace} (h : Mem.loadSlice ctx s slice = .ok (vs, tr)) :
    tr = tableTrace ((sliceElemLocs slice slice.len).map ((.read, ·))) := by
  unfold Mem.loadSlice at h
  simp only [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  split at h
  · rename_i b hb
    simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨⟨vs', ts⟩, hrest, _, rfl⟩ := h
    rw [tableTrace_sliceElemLocs hb]
    exact Mem.loadElems_trace hrest
  · rename_i hb
    simp only [pure_eq_ok] at h
    obtain ⟨_, rfl⟩ := h
    rw [sliceElemLocs_none hb]
    rfl

theorem loadResults_trace {s : Store} :
    ∀ {locs : List Loc} {vs : List GoValue} {tr : AccessTrace},
    loadResults ctx s locs = .ok (vs, tr) → tr = tableTrace (locs.map ((.read, ·)))
  | [], vs, tr, h => by
      simp only [loadResults, pure_eq_ok] at h
      obtain ⟨_, rfl⟩ := h
      rfl
  | loc :: locs, vs, tr, h => by
      unfold loadResults at h
      simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨⟨v, t⟩, hv, ⟨vs', ts⟩, hrest, _, rfl⟩ := h
      rw [Mem.load_trace hv, loadResults_trace hrest]
      rfl

/-! ## Value shapes -/

theorem valueAsMap_ok {v : GoValue} {m : MapValue} (h : valueAsMap v = .ok m) : v = .map m := by
  cases v <;> simp [valueAsMap] at h
  subst h; rfl

theorem valueAsSlice_ok {v : GoValue} {sl : SliceValue} (h : valueAsSlice v = .ok sl) : v = .slice sl := by
  cases v <;> simp [valueAsSlice] at h
  subst h; rfl

theorem valueAsLoc_ok {v : GoValue} {l : Loc} (h : valueAsLoc v = .ok l) : v = .addr l := by
  cases v <;> simp [valueAsLoc] at h
  subst h; rfl

theorem mapEntries_some {s : Store} {m : MapValue} {l : Loc} {es : Array (Nat × GoValue × GoValue)}
    {n : Nat} (h : mapEntries s m = .ok (some (l, es, n))) : m.base = some l := by
  unfold mapEntries at h
  split at h
  · simp at h
  · rename_i l' hb
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    exact hb

/-- `targetWrite` at a resolved address. -/
theorem targetWrite_of_ok {tv : GoValue} {l : Loc} (h : valueAsLoc tv = .ok l) :
    targetWrite tv = [(.write, l)] := by
  simp [targetWrite, h]

theorem mapAccess_some {k : AccessKind} {m : MapValue} {l : Loc} (hb : m.base = some l) :
    mapAccess k (.map m) = [(k, l)] := by
  simp [mapAccess, hb]

theorem mapAccess_none {k : AccessKind} {m : MapValue} (hb : m.base = none) :
    mapAccess k (.map m) = [] := by
  simp [mapAccess, hb]

/-! ## The map operations -/

theorem mapLookupValue_trace {s : Store} {m : MapValue} {key : GoValue} {kt vt : Ty}
    {p : GoValue × Bool} {tr : AccessTrace}
    (h : mapLookupValue ctx s m key kt vt = .ok (p, tr)) :
    tr = tableTrace (mapAccess .read (.map m)) := by
  unfold mapLookupValue at h
  split at h
  · rename_i hb
    rw [mapAccess_none hb]
    simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, _, rfl⟩ := h
    rfl
  · rename_i l hb
    rw [mapAccess_some hb]
    simp only [bind_eq_ok] at h
    obtain ⟨⟨⟨es, n⟩, t⟩, hr, h⟩ := h
    rw [Mem.mapRead_trace hr] at h
    obtain ⟨i?, _, h⟩ := h
    split at h
    · split at h
      · simp only [pure_eq_ok] at h
        obtain ⟨_, rfl⟩ := h
        rfl
      · simp at h
    · simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨_, _, _, rfl⟩ := h
      rfl

theorem mapAssignValue_trace {s s' : Store} {kt vt : Ty} {bv kv vv : GoValue} {tr : AccessTrace}
    (h : mapAssignValue ctx s kt vt bv kv vv = .ok (s', tr)) :
    tr = tableTrace (mapAccess .write bv) := by
  unfold mapAssignValue at h
  simp only [bind_eq_ok] at h
  obtain ⟨m, hm, _, _, _, _, e?, he, h⟩ := h
  rw [valueAsMap_ok hm]
  split at h
  · simp at h
  · rename_i l es n
    rw [mapAccess_some (mapEntries_some he)]
    simp only [bind_eq_ok] at h
    obtain ⟨i?, _, h⟩ := h
    split at h
    · split at h
      · simp only [bind_eq_ok, pure_eq_ok] at h
        obtain ⟨_, _, h⟩ := h
        exact Mem.mapWrite_trace h
      · simp [Bind.bind, Except.bind] at h
    · simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      exact Mem.mapWrite_trace h

theorem mapRangeStartSets_trace {s : Store} {v : GoValue} {base : Option Loc} {start : Array Nat}
    {tr : AccessTrace} (h : mapRangeStartSets s v = .ok (base, start, tr)) :
    tr = tableTrace (mapAccess .read v) := by
  unfold mapRangeStartSets at h
  simp only [bind_eq_ok] at h
  obtain ⟨m, hm, h⟩ := h
  rw [valueAsMap_ok hm]
  split at h
  · rename_i hb
    rw [mapAccess_none hb]
    simp only [pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  · rename_i l hb
    rw [mapAccess_some hb]
    simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨⟨p, t⟩, hr, _, _, rfl⟩ := h
    exact Mem.mapRead_trace hr

/-- The table's account of a map-iteration pick: the live cell's read (nil map: nothing). -/
def iterRead : Option Loc → List RaceAccess
  | some l => [(.read, l)]
  | none => []

theorem mapIterLiveEntries_trace {s : Store} {base : Option Loc}
    {es : Array (Nat × GoValue × GoValue)} {tr : AccessTrace}
    (h : mapIterLiveEntries s base = .ok (es, tr)) : tr = tableTrace (iterRead base) := by
  cases base with
  | none =>
    simp only [mapIterLiveEntries, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    rfl
  | some l =>
    simp only [mapIterLiveEntries, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨⟨p, t⟩, hr, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    rw [Mem.mapRead_trace hr]
    rfl

theorem mapIterCandidates_trace {s : Store} {kt vt : Ty} {base : Option Loc} {produced : Array Nat}
    {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace}
    (h : mapIterCandidates ctx s kt vt base produced = .ok (cands, tr)) :
    tr = tableTrace (iterRead base) := by
  unfold mapIterCandidates at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨es, t⟩, he, h⟩ := h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact mapIterLiveEntries_trace he
  · simp at h

/-! ## Phase-2 stores and the comma-ok sources -/

theorem storeTarget_trace {s s' : Store} {r : TargetRef} {v : GoValue} {tr : AccessTrace}
    (h : storeTarget ctx s r v = .ok (s', tr)) : tr = tableTrace (storeTargetAccess ctx s r) := by
  unfold storeTarget at h
  split at h
  · rename_i anchor idxs steps
    simp only [bind_eq_ok] at h
    obtain ⟨tv, htv, l, hl, h⟩ := h
    simp only [storeTargetAccess, htv, targetWrite_of_ok hl]
    exact Mem.store_trace h
  · rename_i b k kt vt
    simp only [storeTargetAccess]
    exact mapAssignValue_trace h

/-- The table's account of the `rhsK` apply step (the `stepAccesses` rhsK arm's match). -/
def rhsAccesses : RhsOp → List GoValue → List RaceAccess
  | .mapLookup _ _, [bv, _] => mapAccess .read bv
  | _, _ => []

theorem applyRhsOp_trace {s : Store} {rop : RhsOp} {vs vals : List GoValue} {tr : AccessTrace}
    (h : applyRhsOp ctx s rop vs = .ok (vals, tr)) : tr = tableTrace (rhsAccesses rop vs) := by
  unfold applyRhsOp at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    rfl
  · rename_i kt vt bv kv
    simp only [bind_eq_ok] at h
    obtain ⟨m, hm, key, _, ⟨p, t⟩, hl, h⟩ := h
    rw [valueAsMap_ok hm]
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact mapLookupValue_trace hl
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    rfl
  · simp at h

/-! ## The strict operators -/

/-- The strict table's account, with `.deref`'s read at the caller's leaf (the
`stepAccesses` deref arm; `strictOpAccesses` itself records nothing for `.deref`). -/
def strictTrace (leafOf : Loc → Loc) (op : StrictOp) (vs : List GoValue) : AccessTrace :=
  match op, vs with
  | .deref _, [p] =>
      match valueAsLoc p with
      | .ok l => [(.read, .data (leafOf l))]
      | .error _ => []
  | _, _ => tableTrace (strictOpAccesses op vs)

/-- `throw e` in `Except` is the error. -/
theorem throw_def {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

/-- `x *> y` in `Except`, as a bind (the `validateSlice slice *> …` shape). -/
theorem seqRight_eq_ok {ε α β : Type} {x : Except ε α} {y : Except ε β} {b : β} :
    (x *> y) = .ok b ↔ ∃ a, x = .ok a ∧ y = .ok b := by
  cases x <;> cases y <;> simp [SeqRight.seqRight, Except.bind]

/-- Decompose a do-block hypothesis completely: one bind at a time (outermost first,
the continuation beta-reduced; a `pure`-bind reduced in place), every match/if split,
on every goal. -/
macro "trace_split" h:ident : tactic => `(tactic|
  repeat' (first
    | (dsimp only at $h:ident)
    | (simp only [pure_bind] at $h:ident)
    | split at $h:ident
    | (rw [bind_eq_ok] at $h:ident; obtain ⟨_, _, $h:ident⟩ := $h:ident)
    | (rw [seqRight_eq_ok] at $h:ident; obtain ⟨_, _, $h:ident⟩ := $h:ident)))

/-- Close a fully decomposed arm whose return carries the empty trace, or a refusal arm. -/
macro "trace_close" h:ident : tactic => `(tactic| first
  | (obtain ⟨_, _, rfl⟩ := $h:ident; rfl)
  | (obtain ⟨_, rfl⟩ := $h:ident; rfl)
  | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, _, rfl⟩ := $h:ident; rfl)
  | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, rfl⟩ := $h:ident; rfl)
  | (simp [Bind.bind, Except.bind, throw_def] at $h:ident; done))

/-- The bulk closer for an op-table arm whose every return carries `[]`. -/
macro "trace_arm" h:ident : tactic => `(tactic|
  (trace_split $h:ident; all_goals trace_close $h:ident))

theorem applyStrictOp_trace {s s' : Store} {leafOf : Loc → Loc} {op : StrictOp} {vs : List GoValue}
    {v : GoValue} {tr : AccessTrace}
    (h : applyStrictOp ctx s leafOf op vs = .ok (v, s', tr)) : tr = strictTrace leafOf op vs := by
  unfold applyStrictOp at h
  split at h
  all_goals try (simp only [strictTrace, strictOpAccesses, tableTrace_nil]; trace_arm h; done)
  all_goals first
    | -- stringFromByteSlice / stringFromRuneSlice: the visible elements read (`Mem.loadSlice`)
      (first
        | guard_target =~ tr = strictTrace leafOf StrictOp.stringFromByteSlice _
        | guard_target =~ tr = strictTrace leafOf StrictOp.stringFromRuneSlice _
       rename_i v₀
       simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨sl, hsl, ⟨values, t⟩, hload, _, _, _, _, rfl⟩ := h
       simp only [strictTrace, strictOpAccesses, hsl]
       exact Mem.loadSlice_trace hload)
    | -- deref: the pointee read at the caller's leaf
      (guard_target =~ tr = strictTrace leafOf (StrictOp.deref _) _
       rename_i ty v₀
       simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨l, hl, ⟨x, t⟩, hload, _, _, rfl⟩ := h
       simp only [strictTrace, hl]
       exact Mem.loadFor_trace hload)
    | -- indexGet: a slice element, a pointer-to-array element, or no access
      (guard_target =~ tr = strictTrace leafOf StrictOp.indexGet _
       rename_i b i
       rw [bind_eq_ok] at h
       obtain ⟨idx, hidx, h⟩ := h
       try dsimp only at h
       simp only [strictTrace, strictOpAccesses, hidx]
       split at h
       · trace_arm h
       · trace_arm h
       · rename_i sl
         rw [bind_eq_ok] at h
         obtain ⟨l, hl, h⟩ := h
         try dsimp only at h
         rw [bind_eq_ok] at h
         obtain ⟨⟨x, t⟩, hload, h⟩ := h
         try dsimp only at h
         have ht := Mem.load_trace hload
         subst ht
         simp only [hl]
         trace_arm h
       · rename_i baseLoc
         rw [bind_eq_ok] at h
         obtain ⟨⟨cell, t⟩, hload, h⟩ := h
         try dsimp only at h
         have ht := Mem.loadFor_trace hload
         subst ht
         trace_arm h
       · simp at h
       · simp at h)
    | -- mapGet: the map cell's read (nil map: nothing)
      (guard_target =~ tr = strictTrace leafOf (StrictOp.mapGet _ _) _
       rename_i kt vt b i
       rw [bind_eq_ok] at h
       obtain ⟨m, hm, h⟩ := h
       try dsimp only at h
       rw [bind_eq_ok] at h
       obtain ⟨key, _, h⟩ := h
       try dsimp only at h
       simp only [strictTrace, strictOpAccesses, valueAsMap_ok hm]
       split at h
       · rename_i hb
         rw [mapAccess_none hb]
         trace_arm h
       · rename_i l hb
         rw [mapAccess_some hb]
         rw [bind_eq_ok] at h
         obtain ⟨⟨⟨es, n⟩, t⟩, hr, h⟩ := h
         try dsimp only at h
         have ht := Mem.mapRead_trace hr
         subst ht
         trace_arm h)
    | -- lengthOf / capacityOf: the map cell's read on a map (`len`); the type-static,
      -- header and peek arms record nothing
      (first
        | guard_target =~ tr = strictTrace leafOf (StrictOp.lengthOf _) _
        | guard_target =~ tr = strictTrace leafOf (StrictOp.capacityOf _) _
       rename_i typ v₀
       simp only [strictTrace, strictOpAccesses]
       split at h
       · split at h
         · trace_arm h
         · trace_arm h
         · simp at h
       · split at h
         all_goals first
           | trace_arm h
           | (rename_i m
              split at h
              · rename_i hb
                rw [mapAccess_none hb]
                trace_arm h
              · rename_i l hb
                rw [mapAccess_some hb]
                rw [bind_eq_ok] at h
                obtain ⟨⟨p, t⟩, hr, h⟩ := h
                try dsimp only at h
                have ht := Mem.mapRead_trace hr
                subst ht
                trace_arm h))

/-! ## The wide statements -/

theorem intElems_length : ∀ {l : List GoValue} {r : List (Int × IntKind)},
    intElems l = .ok r → r.length = l.length
  | [], r, h => by
      simp only [intElems, pure_eq_ok, Except.ok.injEq] at h
      subst h; rfl
  | .int v k :: rest, r, h => by
      simp only [intElems, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨r', hr, rfl⟩ := h
      simp [intElems_length hr]
  | .bool _ :: _, r, h => by simp [intElems] at h
  | .string _ :: _, r, h => by simp [intElems] at h
  | .float _ _ :: _, r, h => by simp [intElems] at h
  | .addr _ :: _, r, h => by simp [intElems] at h
  | .nil :: _, r, h => by simp [intElems] at h
  | .struct _ _ :: _, r, h => by simp [intElems] at h
  | .array _ :: _, r, h => by simp [intElems] at h
  | .slice _ :: _, r, h => by simp [intElems] at h
  | .map _ :: _, r, h => by simp [intElems] at h
  | .chan _ :: _, r, h => by simp [intElems] at h
  | .funcVal _ _ :: _, r, h => by simp [intElems] at h
  | .interface _ _ :: _, r, h => by simp [intElems] at h

theorem insertLe_length {α : Type} {le : α → α → Bool} {x : α} :
    ∀ {l : List α}, (insertLe le x l).length = l.length + 1
  | [] => rfl
  | y :: ys => by
      simp only [insertLe]
      split
      · rfl
      · simp [insertLe_length (l := ys)]

theorem sortLe_length {α : Type} {le : α → α → Bool} :
    ∀ {l : List α}, (sortLe le l).length = l.length
  | [] => rfl
  | x :: xs => by simp [sortLe, insertLe_length, sortLe_length (l := xs)]

/-- A store-run's trace on a slice whose run length is `count`, as the table's element writes. -/
theorem Mem.storeRun_trace_table {s s' : Store} {slice : SliceValue} {vs : List GoValue}
    {tr : AccessTrace} {u : Unit} (_hv : validateSlice slice = .ok u)
    (h : Mem.storeRun ctx s slice 0 vs = .ok (s', tr)) :
    tr = tableTrace ((sliceElemLocs slice vs.length).map ((.write, ·))) := by
  rcases Mem.storeRun_trace h with ⟨b, hb, rfl⟩ | ⟨hb, rfl, rfl⟩
  · rw [tableTrace_sliceElemLocs hb, Nat.add_zero]
  · rw [sliceElemLocs_none hb]
    rfl

theorem applyStmtOpCore_trace {s s' : Store} {op : StmtOp} {vs : List GoValue} {tr : AccessTrace}
    (h : applyStmtOpCore ctx s op vs = .ok (s', tr)) : tr = tableTrace (stmtOpAccesses op vs) := by
  unfold applyStmtOpCore at h
  split at h
  · -- allocNew: the target write
    rename_i typ
    split at h
    · rename_i tv value
      simp only [bind_eq_ok] at h
      obtain ⟨loc, hloc, ⟨nloc, s₁⟩, _, h⟩ := h
      simp only [stmtOpAccesses, targetWrite_of_ok hloc]
      exact Mem.store_trace h
    · simp at h
  · -- makeSlice: the target write (the backing is fresh)
    rename_i elem hasCap
    match vs, hasCap, h with
    | [tv, lenV], false, h =>
        simp only [stmtOpAccesses]
        trace_split h
        all_goals first
          | (simp [Bind.bind, Except.bind] at h; done)
          | (rw [Mem.store_trace h]; simp [targetWrite, *])
    | [tv, lenV, capV], true, h =>
        simp only [stmtOpAccesses]
        trace_split h
        all_goals first
          | (simp [Bind.bind, Except.bind] at h; done)
          | (rw [Mem.store_trace h]; simp [targetWrite, *])
    | [], _, h => simp [Bind.bind, Except.bind] at h
    | [_], _, h => simp [Bind.bind, Except.bind] at h
    | [_, _], true, h => simp [Bind.bind, Except.bind] at h
    | [_, _, _], false, h => simp [Bind.bind, Except.bind] at h
    | _ :: _ :: _ :: _ :: _, _, h => simp [Bind.bind, Except.bind] at h
  · -- makeMap
    rename_i hasSpace
    match vs, hasSpace, h with
    | [tv], false, h =>
        simp only [stmtOpAccesses]
        trace_split h
        all_goals first
          | (simp [Bind.bind, Except.bind] at h; done)
          | (rw [Mem.store_trace h]; simp [targetWrite, *])
    | [tv, spaceV], true, h =>
        simp only [stmtOpAccesses]
        trace_split h
        all_goals first
          | (simp [Bind.bind, Except.bind] at h; done)
          | (rw [Mem.store_trace h]; simp [targetWrite, *])
    | [], _, h => simp [Bind.bind, Except.bind] at h
    | [_], true, h => simp [Bind.bind, Except.bind] at h
    | [_, _], false, h => simp [Bind.bind, Except.bind] at h
    | _ :: _ :: _ :: _, _, h => simp [Bind.bind, Except.bind] at h
  · -- makeChan
    rename_i elem hasCap
    match vs, hasCap, h with
    | [tv], false, h =>
        simp only [stmtOpAccesses]
        trace_split h
        all_goals first
          | (simp [Bind.bind, Except.bind] at h; done)
          | (rw [Mem.store_trace h]; simp [targetWrite, *])
    | [tv, capV], true, h =>
        simp only [stmtOpAccesses]
        trace_split h
        all_goals first
          | (simp [Bind.bind, Except.bind] at h; done)
          | (rw [Mem.store_trace h]; simp [targetWrite, *])
    | [], _, h => simp [Bind.bind, Except.bind] at h
    | [_], true, h => simp [Bind.bind, Except.bind] at h
    | [_, _], false, h => simp [Bind.bind, Except.bind] at h
    | _ :: _ :: _ :: _, _, h => simp [Bind.bind, Except.bind] at h
  · -- mapAssign: the map write
    rename_i kt vt
    split at h
    · rename_i bv kv vv
      simp only [stmtOpAccesses]
      exact mapAssignValue_trace h
    · simp at h
  · -- mapDelete: the map write, present or absent key; nil map: nothing
    rename_i kt
    split at h
    · rename_i bv kv
      rw [bind_eq_ok] at h
      obtain ⟨m, hm, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨key, _, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨e?, he, h⟩ := h
      try dsimp only at h
      simp only [stmtOpAccesses, valueAsMap_ok hm]
      split at h
      · rename_i hnone
        have hb : m.base = none := by
          revert he
          unfold mapEntries
          split
          · intro _; assumption
          · intro he'
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at he'
            obtain ⟨_, _, he'⟩ := he'
            cases he'
        rw [mapAccess_none hb]
        trace_arm h
      · rename_i l es n
        rw [mapAccess_some (mapEntries_some he)]
        rw [bind_eq_ok] at h
        obtain ⟨i?, _, h⟩ := h
        try dsimp only at h
        split at h
        · exact Mem.mapWrite_trace h
        · exact Mem.mapWrite_trace h
    · simp at h
  · -- clearMap
    split at h
    · rename_i bv
      rw [bind_eq_ok] at h
      obtain ⟨m, hm, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨e?, he, h⟩ := h
      try dsimp only at h
      simp only [stmtOpAccesses, valueAsMap_ok hm]
      split at h
      · have hb : m.base = none := by
          revert he
          unfold mapEntries
          split
          · intro _; assumption
          · intro he'
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at he'
            obtain ⟨_, _, he'⟩ := he'
            cases he'
        rw [mapAccess_none hb]
        trace_arm h
      · rename_i l es n
        rw [mapAccess_some (mapEntries_some he)]
        exact Mem.mapWrite_trace h
    · simp at h
  · -- clearSlice: one write per visible element
    rename_i elem
    split at h
    · rename_i bv
      simp only [bind_eq_ok] at h
      obtain ⟨sl, hsl, u, hv, zero, _, h⟩ := h
      simp only [stmtOpAccesses, valueAsSlice_ok hsl, valueAsSlice, pure_eq_ok]
      rw [Mem.storeRun_trace_table hv h, List.length_replicate]
    · simp at h
  · -- sortSlice (dead op): the visible elements read, the sorted run written back
    split at h
    · rename_i bv
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨sl, hsl, ⟨values, trR⟩, hload, loaded, hints, ⟨s₁, trW⟩, hst, _, rfl⟩ := h
      simp only [stmtOpAccesses, valueAsSlice_ok hsl, valueAsSlice, pure_eq_ok, tableTrace_append]
      have hv : validateSlice sl = .ok () := by
        unfold Mem.loadSlice at hload
        simp only [bind_eq_ok] at hload
        obtain ⟨⟨⟩, hv, _⟩ := hload
        exact hv
      rw [Mem.loadSlice_trace hload, Mem.storeRun_trace_table hv hst, List.length_map, sortLe_length,
        intElems_length hints, Array.length_toList, Mem.loadSlice_size hload]
    · simp at h
  · -- copySlice: the source run read, the destination run written, the count stored
    split at h
    · rename_i tv dstV srcV
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨dst, hdst, src, hsrc, _, hvd, _, hvs, ⟨values, trR⟩, hread, ⟨current, trW⟩, hwrite,
        tloc, htloc, ⟨s₂, trT⟩, hst, _, rfl⟩ := h
      simp only [stmtOpAccesses, valueAsSlice_ok hdst, valueAsSlice_ok hsrc, valueAsSlice, pure_eq_ok,
        tableTrace_append, targetWrite_of_ok htloc]
      have hlen : values.length = Nat.min dst.len src.len := by
        unfold Mem.loadRun at hread
        split at hread
        · exact (Mem.loadElems_locSup hread).2
        · split at hread
          · rename_i hc
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hread
            obtain ⟨rfl, rfl⟩ := hread
            exact hc.symm
          · simp at hread
      rw [Mem.loadRun_trace hread, Mem.storeRun_trace_table hvd hwrite, hlen, Mem.store_trace hst]
      rfl
    · simp at h
  · -- print: validated only
    rename_i newline
    simp only [stmtOpAccesses]
    trace_arm h
  · -- appendSlice dispatches through applyStmtOp
    simp at h

theorem applyStmtOp_trace {s s' : Store} {ch ch' : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {tr : AccessTrace}
    (h : applyStmtOp ctx s ch op nt vs = .ok (s', ch', tr)) : tr = tableTrace (stmtOpAccesses op vs) := by
  unfold applyStmtOp at h
  split at h
  · -- appendSlice: the appended elements read; in place the tail written, on a spill the
    -- old elements read; the header written
    rename_i elem
    split at h
    · rename_i tv sliceV elemsV
      rw [bind_eq_ok] at h
      obtain ⟨sl, hsl, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨el, hel, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨_, hvs, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨_, hve, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨⟨elemValues, trE⟩, hE, h⟩ := h
      try dsimp only at h
      rw [bind_eq_ok] at h
      obtain ⟨tloc, htloc, h⟩ := h
      try dsimp only at h
      have hsize : elemValues.size = el.len := Mem.loadSlice_size hE
      simp only [stmtOpAccesses, valueAsSlice_ok hsl, valueAsSlice_ok hel, valueAsSlice, pure_eq_ok,
        targetWrite_of_ok htloc]
      split at h
      · -- in place
        rename_i hle
        rw [hsize] at hle
        rw [if_pos hle]
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨current, trW⟩, hW, ⟨s₂, trT⟩, hT, _, _, rfl⟩ := h
        rw [Mem.loadSlice_trace hE, Mem.store_trace hT]
        rcases Mem.storeRun_trace hW with ⟨b, hb, rfl⟩ | ⟨hb, hnil, rfl⟩
        · simp only [hb, tableTrace_append, tableTrace_map, indexRun,
            List.range'_eq_map_range, List.map_map, Function.comp_def, Array.length_toList, hsize,
            tableTrace_cons, tableTrace_nil]
        · simp only [hb, List.append_nil, tableTrace_append, tableTrace_cons, tableTrace_nil]
      · -- spill
        rename_i hgt
        rw [hsize] at hgt
        rw [if_neg hgt]
        rw [bind_eq_ok] at h
        obtain ⟨_, _, h⟩ := h
        try dsimp only at h
        split at h
        · simp [Bind.bind, Except.bind] at h
        · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨oldValues, trO⟩, hO, backing, _, ⟨base, current⟩, _, ⟨s₂, trT⟩, hT, _, _, rfl⟩ := h
          rw [Mem.loadSlice_trace hE, Mem.loadSlice_trace hO, Mem.store_trace hT]
          simp only [tableTrace_append, tableTrace_cons, tableTrace_nil]
    · simp at h
  · rename_i op' hne
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨s₁, t⟩, hc, _, _, rfl⟩ := h
    exact applyStmtOpCore_trace hc

/-! ## Frame entry -/

/-- The table's dispatch read at the target's leaf IS `dispatchLeaf`. -/
theorem dispatchLeaf_table {target : Func} {loc : Loc} :
    tableTrace (if target.wrapper then
        match target.args[0]? with
        | some recvParam =>
            match wrapperForwardArg target.body >>= recvFieldChain recvParam.id with
            | some hops => [(AccessKind.read, hops.foldl (fun l (h : TypeId × String) => Loc.field l h.1 h.2) loc)]
            | none => [(AccessKind.read, loc)]
        | none => [(AccessKind.read, loc)]
      else [(AccessKind.read, loc)]) = [(AccessKind.read, .data (dispatchLeaf target loc))] := by
  unfold dispatchLeaf
  by_cases hw : target.wrapper = true
  · simp only [hw, ↓reduceIte]
    cases target.args[0]? with
    | none => rfl
    | some recvParam =>
      exact (fun o : Option (List (TypeId × String)) =>
        show tableTrace (match o with
            | some hops => [(AccessKind.read, hops.foldl (fun l (h : TypeId × String) => Loc.field l h.1 h.2) loc)]
            | none => [(AccessKind.read, loc)])
          = [(AccessKind.read, .data (match o with
            | some hops => hops.foldl (fun l (h : TypeId × String) => Loc.field l h.1 h.2) loc
            | none => loc))] from by cases o <;> rfl) _
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem dynamicDispatch?_trace {s : Store} {fid : FuncId} {func : Func} {args : List GoValue}
    {r : Option (Func × Array GoValue)} {tr : AccessTrace}
    (hf : findFunctionIn? ctx.functions fid = some func)
    (h : dynamicDispatch? ctx s func args.toArray = .ok (r, tr)) :
    tr = tableTrace (dispatchAccesses ctx fid args) := by
  unfold dynamicDispatch? at h
  simp only [dispatchAccesses, hf, List.head?_eq_getElem?, ← List.getElem?_toArray]
  split at h
  · rename_i hmi
    simp only [hmi]
    trace_arm h
  · rename_i method hmi
    simp only [hmi]
    split at h
    · rename_i hri
      simp only [hri]
      trace_arm h
    · rename_i iname hri
      simp only [hri]
      split at h
      · rename_i dynTy inner hhead
        simp only [hhead]
        split at h
        · rename_i concrete needsDeref hcm
          simp only [hcm]
          try dsimp only at h
          split at h
          case h_2 => simp [Bind.bind, Except.bind] at h
          rename_i target htarget'
          try simp only [pure_bind] at h
          try dsimp only at h
          simp only [htarget']
          split at h
          · rename_i hnd
            simp only [hnd, ↓reduceIte]
            split at h
            · rename_i loc
              rw [bind_eq_ok] at h
              obtain ⟨⟨recv, t⟩, hload, h⟩ := h
              try dsimp only at h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              rw [Mem.loadFor_trace hload]
              dsimp only
              exact dispatchLeaf_table.symm
            · simp [Bind.bind, Except.bind, throw_def] at h
            · simp [Bind.bind, Except.bind] at h
          · rename_i hnd
            simp only [hnd, Bool.false_eq_true, ↓reduceIte]
            trace_arm h
        · rename_i hcm
          simp only [hcm]
          split at h <;> simp at h
      · rename_i hhead
        simp only [hhead]
        trace_arm h
      · split
        · simp_all
        · trace_arm h

theorem dynamicDispatch?_trace' {s : Store} {fid : FuncId} {func : Func} {args : List GoValue}
    {d : Option (Func × Array GoValue) × AccessTrace}
    (hf : findFunctionIn? ctx.functions fid = some func)
    (h : dynamicDispatch? ctx s func args.toArray = .ok d) :
    d.2 = tableTrace (dispatchAccesses ctx fid args) := by
  obtain ⟨o, t⟩ := d; exact dynamicDispatch?_trace hf h

theorem enterFrame_trace {s s' : Store} {fid : FuncId} {args : List GoValue} {func : Func}
    {frameEnv : LocalEnv} {resultLocs : List Loc} {tr : AccessTrace}
    (h : enterFrame ctx s fid args = .ok (func, frameEnv, resultLocs, s', tr)) :
    tr = tableTrace (dispatchAccesses ctx fid args) := by
  unfold enterFrame at h
  try dsimp only at h
  split at h
  · rename_i func₀ hf
    try simp only [pure_bind] at h
    try dsimp only at h
    split at h
    · rw [bind_eq_ok] at h
      obtain ⟨_, hst, _⟩ := h
      simp at hst
    · rw [bind_eq_ok] at h
      obtain ⟨d, hd, h⟩ := h
      try dsimp only at h
      trace_split h
      all_goals first
        | (simp at h; done)
        | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨_, _, _, _, rfl⟩ := h
           first
             | exact dynamicDispatch?_trace hf hd
             | exact dynamicDispatch?_trace' hf hd)
  · simp [Bind.bind, Except.bind] at h

/-! ## The `unseq` construct -/

theorem unseqCellLoc_ok {env : LocalEnv} {bind : String} {loc : Loc}
    (h : unseqCellLoc env bind = .ok loc) : env.lookup bind = some loc := by
  unfold unseqCellLoc at h
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq] at h; subst h; assumption
  · simp at h

/-- The table's account of one target-plan atom (the `unseqRunAccesses` target arm's lambda). -/
def atomAcc (env : LocalEnv) (e : Expr) : Option RaceAccess :=
  match e with
  | .var id => (env.lookup id).map ((AccessKind.read, ·))
  | _ => none

theorem unseqAtom_trace {env : LocalEnv} {s : Store} {e : Expr} {v : GoValue} {tr : AccessTrace}
    (h : unseqAtom ctx env s e = .ok (v, tr)) : tr = tableTrace (atomAcc env e).toList := by
  unfold unseqAtom at h
  split at h
  · rename_i id
    split at h
    · rename_i loc hl
      simp only [atomAcc, hl, Option.map_some, Option.toList]
      exact Mem.load_trace h
    · simp at h
  · rename_i id
    simp only [atomAcc]
    split at h
    · trace_arm h
    · simp at h
  · simp only [atomAcc]; trace_arm h
  · simp only [atomAcc]; trace_arm h
  · simp at h

theorem unseqAtoms_trace {env : LocalEnv} {s : Store} :
    ∀ {es : List Expr} {vs : List GoValue} {tr : AccessTrace},
    unseqAtoms ctx env s es = .ok (vs, tr) → tr = tableTrace (es.filterMap (atomAcc env))
  | [], vs, tr, h => by
      simp only [unseqAtoms, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rfl
  | e :: es, vs, tr, h => by
      unfold unseqAtoms at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨v, t⟩, hv, ⟨vs', ts⟩, hrest, _, rfl⟩ := h
      rw [unseqAtom_trace hv, unseqAtoms_trace hrest, List.filterMap_cons]
      cases atomAcc env e <;> simp [tableTrace]

theorem unseqTargetPlan_trace {s : Store} {env : LocalEnv} {lhs : Assignee} {r : TargetRef}
    {tr : AccessTrace} (h : unseqTargetPlan ctx s env lhs = .ok (r, tr)) :
    tr = tableTrace (match targetPlan lhs with
      | some (_, ops) => ops.filterMap (atomAcc env)
      | none => []) := by
  unfold unseqTargetPlan at h
  split at h
  · simp at h
  · rename_i sh ops hplan
    simp only [hplan]
    rw [bind_eq_ok] at h
    obtain ⟨⟨vals, t⟩, hatoms, h⟩ := h
    try dsimp only at h
    split at h
    · split at h
      · simp at h
      · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact unseqAtoms_trace hatoms
    · simp at h

theorem unseqReadTarget_trace {s : Store} {r : TargetRef} {v : GoValue} {tr : AccessTrace}
    (h : unseqReadTarget ctx s r = .ok (v, tr)) :
    tr = tableTrace (match r with
      | .chain anchor idxs steps =>
          match resolveChain ctx s anchor steps idxs with
          | .ok v => match valueAsLoc v with | .ok l => [(AccessKind.read, l)] | .error _ => []
          | .error _ => []
      | .mapElem b _ _ _ => mapAccess .read b) := by
  unfold unseqReadTarget at h
  split at h
  · rename_i anchor idxs steps
    simp only [bind_eq_ok] at h
    obtain ⟨tv, htv, l, hl, h⟩ := h
    simp only [htv, hl]
    exact Mem.load_trace h
  · simp at h

theorem unseqLoad_trace {s s' : Store} {env : LocalEnv} {tg : List (String × TargetRef)}
    {bind tgt : String} {tr : AccessTrace}
    (h : unseqLoad ctx s env tg bind tgt = .ok (s', tr)) :
    tr = tableTrace ((match unseqLookupTarget tg tgt with
      | .ok (.chain anchor idxs steps) =>
          match resolveChain ctx s anchor steps idxs with
          | .ok v => match valueAsLoc v with | .ok l => [(AccessKind.read, l)] | .error _ => []
          | .error _ => []
      | .ok (.mapElem b _ _ _) => mapAccess .read b
      | .error _ => []) ++ ((env.lookup bind).toList.map ((AccessKind.write, ·)))) := by
  unfold unseqLoad at h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨r, hr, ⟨v, t₁⟩, hread, loc, hloc, ⟨s₁, t₂⟩, hst, _, rfl⟩ := h
  rw [hr, unseqCellLoc_ok hloc, tableTrace_append, Mem.store_trace hst]
  cases r with
  | chain anchor idxs steps =>
    rw [unseqReadTarget_trace hread]
    rfl
  | mapElem b k kt vt =>
    simp [unseqReadTarget] at hread

theorem unseqGuard_trace {s s' : Store} {g : UnseqGraph} {env : LocalEnv} {st st' : List UnseqStatus}
    {i : Nat} {test : String} {w : Bool} {out : String} {tr : AccessTrace}
    (h : unseqGuard ctx s g env st i test w out = .ok (st', s', tr)) :
    tr = tableTrace (((env.lookup test).toList.map ((AccessKind.read, ·)))
      ++ (match env.lookup test with
          | some tl =>
              match loadLoc ctx s tl with
              | .ok (.bool b) =>
                  if b == w then [] else (env.lookup out).toList.map ((AccessKind.write, ·))
              | _ => []
          | none => [])) := by
  unfold unseqGuard at h
  rw [bind_eq_ok] at h
  obtain ⟨tl, htl, h⟩ := h
  try dsimp only at h
  rw [bind_eq_ok] at h
  obtain ⟨⟨tv, t₁⟩, hload, h⟩ := h
  try dsimp only at h
  rw [bind_eq_ok] at h
  obtain ⟨b, hb, h⟩ := h
  try dsimp only at h
  have htv : tv = .bool b := by
    cases tv <;> simp [valueAsBool] at hb
    subst hb; rfl
  have hll : loadLoc ctx s tl = .ok (.bool b) := by
    unfold Mem.load at hload
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hload
    obtain ⟨x, hx, rfl, _⟩ := hload
    rw [← htv]; exact hx
  have ht₁ := Mem.load_trace hload
  subst ht₁
  rw [unseqCellLoc_ok htl]
  simp only [Option.toList, hll, List.map_cons, List.map_nil, tableTrace_append, tableTrace_cons,
    tableTrace_nil]
  split at h
  · rename_i heq
    rw [if_pos heq]
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  · rename_i hne
    rw [if_neg hne]
    rw [bind_eq_ok] at h
    obtain ⟨ol, hol, h⟩ := h
    try dsimp only at h
    rw [bind_eq_ok] at h
    obtain ⟨⟨s₁, t₂⟩, hst, h⟩ := h
    try dsimp only at h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      rw [unseqCellLoc_ok hol, Mem.store_trace hst]
      rfl
    · simp at h


/-! ## Small facts the per-arm cases use -/

/-- No strict operator emits on an empty operand list. -/
theorem strictTrace_nil {leafOf : Loc → Loc} {op : StrictOp} : strictTrace leafOf op [] = [] := by
  cases op <;> rfl

/-- Off `.deref`, the strict account is the table's. -/
theorem strictTrace_ne_deref {leafOf : Loc → Loc} {op : StrictOp} {vs : List GoValue}
    (hop : ∀ t, op ≠ .deref t) : strictTrace leafOf op vs = tableTrace (strictOpAccesses op vs) := by
  cases op <;> first | exact absurd rfl (hop _) | rfl

/-- `.deref` on anything but one operand is stuck; its account is empty. -/
theorem strictTrace_deref_of_ne {leafOf : Loc → Loc} {t : Ty} {vs : List GoValue}
    (hvs : ∀ p, vs ≠ [p]) : strictTrace leafOf (.deref t) vs = [] := by
  cases vs with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => exact absurd rfl (hvs a)
    | cons b l' => rfl

/-- A delivered outcome whose successor builder carries no trace delivers `[]`. -/
theorem deliver_trace_nil {α : Type} {s s' : Store} {k : Cont}
    {next : α → Config × Store × AccessTrace} {r : Result α} {chain : List PanicEntry}
    {c' : Config} {tr : AccessTrace}
    (hn : ∀ a, (next a).2.2 = []) (h : deliver s k next r chain = (c', s', tr)) : tr = [] := by
  cases r with
  | ok a =>
    simp only [deliver_ok] at h
    have := congrArg (fun p : Config × Store × AccessTrace => p.2.2) h
    simp only at this
    rw [hn] at this
    exact this.symm
  | panic msg =>
    obtain ⟨_, _, rfl⟩ := deliver_panic_eq h
    rfl

/-- A frame entry with no arguments dispatches nothing (no receiver). -/
theorem dispatchAccesses_nil {fid : FuncId} : dispatchAccesses ctx fid [] = [] := by
  unfold dispatchAccesses
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rfl

/-- Split an apply-then-deliver rule: the panic branch is closed (the label is `[]` and
the successor unwinds); the value branch is left with the apply's `.ok` equation. -/
macro "deliver_split" htr:ident hdel:ident a:ident hx:ident : tactic => `(tactic| (
  rcases toResult_cases $htr:ident with ⟨$a:ident, hr, $hx:ident⟩ | ⟨_, hr, _⟩
  case inr =>
    subst hr
    obtain ⟨h1, h2, h3⟩ := deliver_panic_eq $hdel:ident
    subst h1; subst h2; subst h3
    exact Or.inr ⟨rfl, rfl⟩
  subst hr))

/-- The value branch of a frame-entry rule: the entered frame's trace is the table's. -/
macro "entry_value" hpick:ident hdel:ident : tactic => `(tactic| (
  rcases enterFramePick_cases $hpick:ident with ⟨func, frameEnv, resultLocs, s₁, t, hr, hef, _⟩ | ⟨msg, hr, _, _⟩
  case inr =>
    subst hr
    obtain ⟨h1, h2, h3⟩ := deliver_panic_eq $hdel:ident
    subst h1; subst h2; subst h3
    exact Or.inr ⟨rfl, rfl⟩
  subst hr
  simp only [deliver_ok, Prod.mk.injEq] at $hdel:ident
  obtain ⟨h1, h2, h3⟩ := $hdel:ident
  subst h1; subst h2; subst h3
  left
  unfold stepAccesses
  dsimp only
  first
    | exact enterFrame_trace hef
    | (rw [enterFrame_trace hef, dispatchAccesses_nil])
    | (simp only [deferEntryAccesses]; exact enterFrame_trace hef)))

/-! ## The theorem -/

/-- **`accesses_eq_stepAccesses` (C1 charter §3, D6).** Every step's LABEL is the footprint
table's account of the step — EXACTLY, not up to permutation — unless the step DELIVERED a
panic, in which case the label is `[]` (the apply's effects are discarded, its accesses never
happened: `deliver`'s convention, `raceUpdate`'s former «the step panicked» rule). On a
non-panicking successor the two accounts coincide on every one of the 122 rules. -/
theorem accesses_eq_stepAccesses {c : Config} {s : Store} {c' : Config} {s' : Store}
    {tr : AccessTrace} (h : Step ctx c s c' s' tr) :
    tr = tableTrace (stepAccesses ctx s c) ∨ (tr = [] ∧ c'.isPanicking = true) := by
  cases h
  all_goals try (left; unfold stepAccesses; dsimp only; (try rfl); done)
  -- ---- pure rules on shapes the table cannot decide by the configuration's head alone
  case evalStrict e op e₁ rest env k hplan =>
    left
    cases e <;> first | (unfold stepAccesses; dsimp only; rfl) | (simp [strictPlan] at hplan)
  case strictShift op done e rest v env k =>
    left
    cases op <;> (try cases done) <;> (unfold stepAccesses; dsimp only; rfl)
  case signal sg k hsig =>
    left
    cases sg <;> cases k <;> first | (unfold stepAccesses; dsimp only; rfl) | (simp [signalStep] at hsig)
  case panicUnwind chain k k' hpass =>
    left
    cases k <;> first | (unfold stepAccesses; dsimp only; rfl) | (simp [panicPassthrough, Cont.isGlue, Cont.class] at hpass)
  case unseqRunEval g thenB st tg env k o bind head i hocc hbody =>
    left
    unfold stepAccesses
    dsimp only
    simp only [unseqRunAccesses, hocc, hbody]
    rfl
  case unseqRunInvoke g thenB st tg env k o binds callee args i hocc hbody =>
    left
    unfold stepAccesses
    dsimp only
    simp only [unseqRunAccesses, hocc, hbody]
    rfl
  case stmtOpShiftTarget op nt done v r e rest env k hlt htr hdel =>
    have htr' := deliver_trace_nil (fun _ => rfl) hdel
    subst htr'
    left
    unfold stepAccesses
    dsimp only
    rfl
  -- ---- the variable read
  case evalVar id loc v env k hlook hload =>
    left
    unfold stepAccesses
    dsimp only
    simp only [hlook]
    rw [Mem.loadFor_trace hload]
    rfl
  -- ---- strict operators
  case evalStrictNullary e op r env k hplan htr hdel =>
    deliver_split htr hdel a hx
    obtain ⟨out, s₁, t⟩ := a
    simp only [deliver_ok, Prod.mk.injEq] at hdel
    obtain ⟨rfl, rfl, rfl⟩ := hdel
    left
    rw [applyStrictOp_trace hx, strictTrace_nil]
    cases e <;> first | (unfold stepAccesses; dsimp only; rfl) | (simp [strictPlan] at hplan)
  case strictApply op done v r env k htr hdel =>
    deliver_split htr hdel a hx
    obtain ⟨out, s₁, t⟩ := a
    simp only [deliver_ok, Prod.mk.injEq] at hdel
    obtain ⟨rfl, rfl, rfl⟩ := hdel
    left
    rw [applyStrictOp_trace hx]
    cases op
    case deref ty =>
      cases done with
      | nil =>
        unfold stepAccesses
        dsimp only
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, strictTrace]
        cases valueAsLoc v <;> rfl
      | cons d ds =>
        unfold stepAccesses
        dsimp only
        rw [strictTrace_deref_of_ne]
        · simp only [strictOpAccesses]
          rfl
        · intro p hp
          have := congrArg List.length hp
          simp at this
    all_goals
      rw [strictTrace_ne_deref (by intro t ht; cases ht)]
      unfold stepAccesses
      dsimp only
      try rfl
  -- ---- frame entries
  case callImmediate targets fid args plans r env k ch ch' htargets hargs hpick hdel =>
    entry_value hpick hdel
  case callArgsDoneEnter v fid plans vals r env k ch ch' hpick hdel =>
    entry_value hpick hdel
  case callValCalleeEnter fid captured plans r env k ch ch' hpick hdel =>
    entry_value hpick hdel
  case callValArgsEnter v fid captured plans vals r env k ch ch' hpick hdel =>
    entry_value hpick hdel
  case frameDeferFall targets tenv results fid captured args ds k w r ch ch' hpick hdel =>
    entry_value hpick hdel
  case frameDeferReturn targets tenv results fid captured args ds k w r ch ch' hpick hdel =>
    entry_value hpick hdel
  case panicFrameDefer chain targets tenv results fid captured args ds k w r ch ch' hpick hdel =>
    entry_value hpick hdel
  -- ---- wide statements
  case stmtOpApply op nt done v r env k ch htr hdel =>
    deliver_split htr hdel a hx
    obtain ⟨s₁, ch₂, t⟩ := a
    simp only [deliver_ok, Prod.mk.injEq] at hdel
    obtain ⟨rfl, rfl, rfl⟩ := hdel
    left
    unfold stepAccesses
    dsimp only
    exact applyStmtOp_trace hx
  -- ---- map iteration
  case mapRangeStart v base start keyVar valVar keyTy valTy body env k hstart =>
    left
    unfold stepAccesses
    dsimp only
    exact mapRangeStartSets_trace hstart
  case mapIterDone keyVar valVar keyTy valTy body base produced start env k hc =>
    left
    unfold stepAccesses
    dsimp only
    rw [mapIterCandidates_trace hc]
    cases base <;> rfl
  case mapIterNext keyVar valVar keyTy valTy body base produced start cands idx env env' k hidx hbind hc =>
    left
    unfold stepAccesses
    dsimp only
    rw [mapIterCandidates_trace hc]
    cases base <;> rfl
  case mapIterStop keyVar valVar keyTy valTy body base produced start cands env k hne hmand hc =>
    left
    unfold stepAccesses
    dsimp only
    rw [mapIterCandidates_trace hc]
    cases base <;> rfl
  -- ---- frame exit
  case frameReturnTargets sh e ops rest tenv results k w vs hload =>
    left
    unfold stepAccesses
    dsimp only
    exact loadResults_trace hload
  case frameFallTargets sh e ops rest tenv results k w vs hload =>
    left
    unfold stepAccesses
    dsimp only
    exact loadResults_trace hload
  -- ---- the registry ops: no data trace
  case chanStApply =>
    rename_i htr hdel
    have htr' := deliver_trace_nil (by intro a; split; rfl) hdel
    subst htr'
    left
    unfold stepAccesses
    dsimp only
    rfl
  case selectApply =>
    rename_i htr hdel
    have htr' := deliver_trace_nil (by intro a; split; rfl) hdel
    subst htr'
    left
    unfold stepAccesses
    dsimp only
    rfl
  case syncStApply =>
    rename_i htr hdel
    have htr' := deliver_trace_nil (by intro a; split; rfl) hdel
    subst htr'
    left
    unfold stepAccesses
    dsimp only
    rfl
  case atomicStApply =>
    rename_i htr hdel
    have htr' := deliver_trace_nil (by intro a; split; rfl) hdel
    subst htr'
    left
    unfold stepAccesses
    dsimp only
    rfl
  -- ---- the assignment spine
  case rhsStores rop refs done v r body env k htr hdel =>
    deliver_split htr hdel a hx
    obtain ⟨vals, t⟩ := a
    simp only [deliver_ok, Prod.mk.injEq] at hdel
    obtain ⟨rfl, rfl, rfl⟩ := hdel
    left
    unfold stepAccesses
    dsimp only
    rw [applyRhsOp_trace hx]
    unfold rhsAccesses
    rfl
  case storeStep ref rs val vals r body env k htr hdel =>
    deliver_split htr hdel a hx
    obtain ⟨s₁, t⟩ := a
    simp only [deliver_ok, Prod.mk.injEq] at hdel
    obtain ⟨rfl, rfl, rfl⟩ := hdel
    left
    unfold stepAccesses
    dsimp only
    exact storeTarget_trace hx
  -- ---- the unseq construct
  case unseqRunLoad g thenB st tg env k o bind tgt r i hocc hbody htr hdel =>
    deliver_split htr hdel a hx
    obtain ⟨s₁, t⟩ := a
    simp only [deliver_ok, Prod.mk.injEq] at hdel
    obtain ⟨rfl, rfl, rfl⟩ := hdel
    left
    unfold stepAccesses
    dsimp only
    simp only [unseqRunAccesses, hocc, hbody]
    rw [unseqLoad_trace hx]
    rfl
  case unseqRunTarget g thenB st tg env k o bind lhs r i hocc hbody hplan =>
    left
    unfold stepAccesses
    dsimp only
    simp only [unseqRunAccesses, hocc, hbody]
    rw [unseqTargetPlan_trace hplan]
    unfold atomAcc
    rfl
  case unseqRunGuard g thenB st tg env k o test w out st' i hocc hbody hguard =>
    left
    unfold stepAccesses
    dsimp only
    simp only [unseqRunAccesses, hocc, hbody]
    rw [unseqGuard_trace hguard]
    rfl
  case unseqValue g thenB st tg env k o bind head v loc i hocc hbody hloc hstore =>
    left
    unfold stepAccesses
    dsimp only
    obtain ⟨o₁, o₂, o₃, o₄⟩ := o
    simp only at hbody
    subst hbody
    simp only [hocc, unseqCellLoc_ok hloc, Option.toList, List.map_cons, List.map_nil]
    rw [Mem.store_trace hstore]
    rfl


/-- On a non-panicking successor the label IS the table's account. -/
theorem accesses_eq_stepAccesses_of_not_panicking {c : Config} {s : Store} {c' : Config} {s' : Store}
    {tr : AccessTrace} (h : Step ctx c s c' s' tr) (hc : c'.isPanicking = false) :
    tr = tableTrace (stepAccesses ctx s c) := by
  rcases accesses_eq_stepAccesses h with h | ⟨_, hp⟩
  · exact h
  · rw [hp] at hc; cases hc

/-- **The spawn step's label** (the child's frame-entry read, attributed to the child by the
fold) is the table's `dispatchAccesses`, unless the child's entry panicked (label `[]`, the
child unwinding). -/
theorem spawnStep_trace {s s' : Store} {fid : FuncId} {captured args : List GoValue} {k : Cont}
    {ch ch' : Choices} {parent' child : Config} {tr : AccessTrace}
    (h : spawnStep ctx s (.funcVal fid captured) args k ch = .ok (parent', child, s', ch', tr)) :
    tr = tableTrace (dispatchAccesses ctx fid (captured ++ args))
      ∨ (tr = [] ∧ child.isPanicking = true) := by
  unfold spawnStep at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨r, ch₁⟩, hpick, h⟩ := h
  rcases enterFramePick_cases hpick with ⟨func, frameEnv, resultLocs, s₁, t, hr, hef, _⟩ | ⟨msg, hr, _, _⟩
  · subst hr
    simp only [deliver_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hchild, _, _, htr⟩ := h
    subst hchild; subst htr
    exact .inl (enterFrame_trace hef)
  · subst hr
    simp only [deliver_panic, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hchild, _, _, htr⟩ := h
    subst hchild; subst htr
    exact .inr ⟨rfl, rfl⟩

end GoLean.GoCore.Machine
