import GoLean.GoCore.State

/-!
# `Store` — the mutable half of the machine state (B7, 2026-09-17)

The heap, and nothing else: program facts are `ProgramCtx`, the choice
tape is a parameter of the step, program output is a per-step event folded
by the driver (G-OUT), the detector state and the thread pool are driver/
pool data (`docs/2026-09-16_b7-context-store-charter.md` §2). `Store` is
the ONE named seam C1 redesigns (`docs/2026-09-11_bug090-rediagnosis.md`
§5): B7 changes neither cost A (whole-root re-normalization) nor cost B
(pre-step retention) — every operation below is `ExecState`'s, re-typed.

Provenance: copied by hand from the previous build's snapshot
`85f9abd7:GoLean/GoCore/Store.lean` (never merged), which matches the
charter §3 exactly; refusal texts byte-preserved (the allocator spelling
in `updateCell`'s `.internal` text is the historical one, kept so the
message is byte-identical — C1 owns the seam and its wording).
-/

namespace GoLean.GoCore

/-- Mutable memory only. Program facts, platform, choices, output and thread
state are supplied by the semantic operation or its driver. -/
structure Store where
  heap : Heap := #[]
  deriving Repr, BEq

/-- The allocator's NEXT address = the heap's size (dense heap, A2). A
derived quantity, not a field: it cannot drift from the heap. -/
def Store.nextAddr (s : Store) : Nat := s.heap.size

/-- Allocate a fresh cell: the new address is the heap's size and the
cell is pushed (dense heap, A2 — the ONLY way a cell comes to exist). -/
def Store.allocCell (s : Store) (cell : HeapCell) : Loc × Store :=
  (.base ⟨s.heap.size⟩, { heap := s.heap.push cell })

/-- Allocate a VALUE cell at its declared type. Allocation does NOT
normalize (the pre-existing hole `State.lean`'s `HeapCell` docstring
names; C1 §5 item 1's) — byte-identical to the pre-B7 machine. -/
def Store.alloc (s : Store) (value : GoValue) (typ : Ty) : Loc × Store :=
  s.allocCell (.value typ value)

/-- Overwrite root cell `a` through `f` (which sees the old cell), FAIL
CLOSED out of range: `.internal` (BUG-085 — an unallocated address is an
invariant breach, never Go behaviour). The ONE write path for every root
cell (`storeLoc`, `storeMapPayload`, `storeChanPayload`); `Array.set` under
`hi` is what makes a phantom cell unrepresentable (A2/A3). -/
def Store.updateCell (s : Store) (a : Addr)
    (f : HeapCell → Except Stop HeapCell) : Except Stop Store :=
  if hi : a.id < s.heap.size then do
    let cell ← f s.heap[a.id]
    return { heap := s.heap.set a.id cell hi }
  else
    throw (.internal s!"store to unallocated address {repr (Loc.base a)}: no heap cell (allocation goes through ExecState.alloc only)")

/-! ## Payload cells (A3): the map/channel readers and writers -/

/-- The map payload at a root cell: `(entries, nextId)`. Anything else
there (a value cell, a channel, no cell) is an ill-shaped program
operand — refused. -/
def mapPayload? (state : Store) (loc : Loc) :
    Except Stop (Array (Nat × GoValue × GoValue) × Nat) :=
  match Heap.lookup state.heap loc with
  | some (.mapPayload entries nextId) => return (entries, nextId)
  | some (.value _ v) => stuck s!"expected map data at {repr loc}, got value {repr v}"
  | some (.chanPayload ..) => stuck s!"expected map data at {repr loc}, got channel data"
  | none => stuck s!"unbound GoCore heap location: {repr loc}"

/-- The channel payload at a root cell: `(buf, capacity, closed)`. -/
def chanPayload? (state : Store) (loc : Loc) :
    Except Stop (Array GoValue × Nat × Bool) :=
  match Heap.lookup state.heap loc with
  | some (.chanPayload buf capacity closed) => return (buf, capacity, closed)
  | some (.value _ v) => stuck s!"expected channel data at {repr loc}, got value {repr v}"
  | some (.mapPayload ..) => stuck s!"expected channel data at {repr loc}, got map data"
  | none => stuck s!"unbound GoCore heap location: {repr loc}"

/-- Replace a map payload WHOLE (the only way a map cell is written); the
cell must already be a map payload. -/
def storeMapPayload (state : Store) (loc : Loc)
    (entries : Array (Nat × GoValue × GoValue)) (nextId : Nat) :
    Except Stop Store :=
  match loc with
  | .base a =>
      state.updateCell a fun
        | .mapPayload _ _ => pure (.mapPayload entries nextId)
        | .value _ v => stuck s!"expected map data at {repr loc}, got value {repr v}"
        | .chanPayload .. => stuck s!"expected map data at {repr loc}, got channel data"
  | other => stuck s!"map payload store through a non-root path {repr other}"

/-- Replace a channel payload WHOLE; the cell must already be a channel
payload. -/
def storeChanPayload (state : Store) (loc : Loc) (buf : Array GoValue)
    (capacity : Nat) (closed : Bool) : Except Stop Store :=
  match loc with
  | .base a =>
      state.updateCell a fun
        | .chanPayload .. => pure (.chanPayload buf capacity closed)
        | .value _ v => stuck s!"expected channel data at {repr loc}, got value {repr v}"
        | .mapPayload .. => stuck s!"expected channel data at {repr loc}, got map data"
  | other => stuck s!"channel payload store through a non-root path {repr other}"

end GoLean.GoCore
