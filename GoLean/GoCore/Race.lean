import GoLean.GoCore.StepFn

/-!
# Segment-level happens-before race detection — the per-step kit
(channels arc slice 3, D2+D3(b); `docs/2026-08-06_channels-arc-design.md`)

The synchronization-op registry's SECOND duty: execution between
registry ops is a SEGMENT; the pool records each segment's read/write
set at `Loc`-path granularity and advances vector clocks over goroutine
ids on the registry ops' happens-before edges (the memory model's
channel rules, quoted at their implementation sites in `Multi.lean`).
Two HB-unordered conflicting accesses from different goroutines are the
terminal `GoError.raceDetected` — races FAIL CLOSED per run,
deterministically given the stream (the detector is a pure function of
the observed steps; it consumes NO choices).

This file is the pool-independent half: vector clocks, the per-location
shadow (TSan/FastTrack's skeleton — per-loc last-access epochs, one per
goroutine, subsumption by program order), the `Loc`-path overlap
relation, and THE ACCESS FOOTPRINT `stepAccesses` — the read/write set
of one private machine step, computed from the pre-step configuration.
The pool half (channel-clock events, the `raceUpdate` dispatcher, the
detecting loop) lives in `Multi.lean`, which imports this.

## Why a curated per-shape footprint, NOT autologging at the
`loadLoc`/`storeLoc` chokepoint (recorded deviation from the design
note's phrasing "through the existing loadLoc/storeLoc chokepoint")

Every heap access does flow through `loadLoc`/`storeLoc` — the
chokepoint is what makes the footprint below AUDITABLE (its arms are
exactly the loadLoc/storeLoc call-site inventory of the access-bearing
step shapes). But logging raw chokepoint calls would record accesses
gc never performs and misgrade granularity in BOTH directions:

* `indexTargetLoc`/`resolveChain` LOAD base cells to bounds-check —
  gc's address formation reads no user memory (bounds come from
  headers/types); logging those loads would flag races on address
  formation (false positives vs `-race`).
* channel-cell loads/stores are SYNCHRONIZATION, race-free by spec
  ("A single channel may be used … by any number of goroutines without
  further synchronization") — never data accesses.
* `loadLoc` is a pure reader (no state to carry a log), so chokepoint
  logging would mean re-plumbing the sequential machine — growth by
  REVISION, against the arc's deciding principle.

So the footprint is a per-shape table argued against Go's ACCESS
semantics (what memory does gc's compiled code read/write here), in
the plan-extraction mold (`stmtPlan`/`spawnPlan` precedent). Its
completeness over access-bearing shapes is a LOCKSTEP obligation like
the relation's: a new `stepFn` arm that touches user memory must add
its footprint arm, and the racy-negative corpus lane is the executable
check. Recorded over-approximation (fail-closed direction, may refuse
a `-race`-green program): `evalVar` reads the WHOLE cell of a
composite local (`p.a` through the value path records a read of `p`) —
the value-projection machine cannot see which field a later `fieldGet`
will take; the fix, if a real race-free case ever needs it, is
address-based field reads in the frontend. Recorded under-approximation
(TSan-aligned): `len`/`cap` record nothing (gc instruments neither —
`len(m)` beside a map write is invisible to `-race`; aligning keeps
our refusals justifiable by the oracle).
-/

namespace GoLean.GoCore.Machine

open GoLean

/-! ## Vector clocks over goroutine ids -/

/-- A vector clock: component `t` is the last-known epoch of goroutine
`t`. Ragged on purpose — absent components read 0 (`get`). -/
abbrev VClock := Array Nat

/-- Component read; absent = 0. -/
def VClock.get (vc : VClock) (t : Nat) : Nat := (vc[t]?).getD 0

/-- Pointwise max (length = max of the lengths). -/
def VClock.join (a b : VClock) : VClock :=
  (Array.range (max a.size b.size)).map fun t => max (a.get t) (b.get t)

/-- Pad to length ≥ `n` with zeros. -/
def VClock.pad (vc : VClock) (n : Nat) : VClock :=
  if vc.size ≥ n then vc else vc ++ Array.replicate (n - vc.size) 0

/-- Set component `t` (padding as needed). -/
def VClock.setC (vc : VClock) (t : Nat) (v : Nat) : VClock :=
  (vc.pad (t + 1)).setIfInBounds t v

/-- Bump goroutine `t`'s own component — the RELEASE-side epoch
increment (FastTrack): accesses after a release are distinguishable
from the ones the release published. -/
def VClock.bump (vc : VClock) (t : Nat) : VClock :=
  vc.setC t (vc.get t + 1)

/-- The birth clock of goroutine `t` before any synchronization: own
component 1 (so its accesses are visibly unordered for every peer whose
view of `t` is still 0), everything else 0. -/
def VClock.birth (t : Nat) : VClock :=
  (Array.replicate (t + 1) 0).setIfInBounds t 1

/-! ## Loc-path overlap

Go's memory locations at our heap's granularity: a `Loc` PATH names a
memory region; two paths conflict iff one is a prefix of the other
(equal included) — a whole-struct write overlaps every field, distinct
fields / distinct indices are disjoint. -/

/-- Is `l` a prefix of `m` (equality included)? -/
def locPrefix (l : Loc) : Loc → Bool
  | m@(.base _) => l == m
  | m@(.field b _ _) => l == m || locPrefix l b
  | m@(.index b _) => l == m || locPrefix l b

/-- Path overlap: the conflict relation on recorded accesses. -/
def locOverlap (a b : Loc) : Bool := locPrefix a b || locPrefix b a

/-! ## The per-location shadow (TSan/FastTrack skeleton) -/

/-- Last-access epochs at one `Loc` path: at most one entry `(t, e)`
per goroutine per kind (same-goroutine accesses are totally ordered by
sequenced-before, so the LATEST epoch subsumes older ones for every
future HB test). -/
structure ShadowCell where
  reads : List (Nat × Nat) := []
  writes : List (Nat × Nat) := []
  deriving Repr, BEq

/-- Replace-or-insert goroutine `t`'s entry. -/
def ShadowCell.upsert (entries : List (Nat × Nat)) (t : Nat) (e : Nat) :
    List (Nat × Nat) :=
  match entries with
  | [] => [(t, e)]
  | (u, e') :: rest =>
      if u == t then (t, e) :: rest else (u, e') :: ShadowCell.upsert rest t e

/-- Does some entry `(u, e)` with `u ≠ t` satisfy `e > vt[u]` — i.e. is
some prior access by another goroutine NOT happens-before goroutine
`t`'s current point? (Prior access at epoch `e` by `u` is ordered
before `t`-now iff `e ≤ vt[u]`.) -/
def ShadowCell.someConcurrent (entries : List (Nat × Nat)) (t : Nat)
    (vt : VClock) : Bool :=
  entries.any fun (u, e) => u != t && e > vt.get u

/-! ## The access footprint of one private step -/

/-- `(isWrite, loc)` — one recorded access. -/
abbrev RaceAccess := Bool × Loc

/-- The element paths a slice's visible range names. -/
def sliceElemLocs (slice : SliceValue) (count : Nat) : List Loc :=
  match slice.base with
  | none => []
  | some b =>
      (List.range count).map fun i => .index b (Int.ofNat (slice.offset + i))

/-- Read of a map's data cell (map objects are ONE location for race
purposes — gc/TSan's classification of "concurrent map read and map
write"). A nil map contributes nothing (the op returns zeros or
panics; no memory named). -/
def mapAccess (isWrite : Bool) : GoValue → List RaceAccess
  | .map m =>
      match m.base with
      | some l => [(isWrite, l)]
      | none => []
  | _ => []

/-- A write through an evaluated target-address value; nothing if the
address is malformed/nil (the step itself panics — no store happens). -/
def targetWrite (tv : GoValue) : List RaceAccess :=
  match valueAsLoc tv with
  | .ok l => [(true, l)]
  | .error _ => []

/-- Footprint of a strict-operator application (the operands are
already values — their own reads were recorded at their own steps).
Arms argued against gc's compiled accesses; anything not listed
touches no user memory (bounds/type metadata, header math, values in
hand). -/
def strictOpAccesses (op : StrictOp) (vs : List GoValue) : List RaceAccess :=
  match op, vs with
  | .deref _, [v] =>
      match valueAsLoc v with
      | .ok l => [(false, l)]
      | .error _ => []
  | .indexGet, [b, i] =>
      match b with
      | .slice slice =>
          match valueAsInt i with
          | .ok idx =>
              match sliceIndexLoc slice idx with
              | .ok l => [(false, l)]
              | .error _ => []
          | .error _ => []
      | _ => []  -- array/string VALUES are in hand (read recorded at their producer)
  | .mapGet _ _, [b, _] => mapAccess false b
  | .stringFromByteSlice, [v] =>
      match valueAsSlice v with
      | .ok slice => (sliceElemLocs slice slice.len).map ((false, ·))
      | .error _ => []
  | _, _ => []

/-- Footprint of a wide-statement application. Fresh allocations are
never recorded (the malloc convention: a fresh location's creating
write precedes every path by which its address can race-freely
escape); target-cell writes, map-object accesses, and slice-element
reads/writes are. -/
def stmtOpAccesses (op : StmtOp) (vs : List GoValue) : List RaceAccess :=
  match op, vs with
  | .newValue _, [tv, _] => targetWrite tv
  | .makeSlice _ _, tv :: _ => targetWrite tv
  | .makeMap _, tv :: _ => targetWrite tv
  | .makeChan _, tv :: _ => targetWrite tv
  | .mapAssign _ _, [bv, _, _] => mapAccess true bv
  | .mapLookup _ _, [tv, okv, bv, _] =>
      mapAccess false bv ++ targetWrite tv ++ targetWrite okv
  | .typeAssertStmt _, [tv, okv, _] => targetWrite tv ++ targetWrite okv
  | .appendSlice _, [tv, sliceV, elemsV] =>
      (match valueAsSlice sliceV, valueAsSlice elemsV with
       | .ok slice, .ok elems =>
           let newLen := slice.len + elems.len
           let srcReads := (sliceElemLocs elems elems.len).map ((false, ·))
           if newLen ≤ slice.cap then
             -- in place: writes the cells [len, newLen) of the backing
             (match slice.base with
              | some b =>
                  srcReads ++ ((List.range elems.len).map fun i =>
                    (true, Loc.index b (Int.ofNat (slice.offset + slice.len + i))))
              | none => srcReads)
           else
             -- spill: reads the old elements out; the new backing is fresh
             srcReads ++ (sliceElemLocs slice slice.len).map ((false, ·))
       | _, _ => []) ++ targetWrite tv
  | .copySlice, [tv, dstV, srcV] =>
      (match valueAsSlice dstV, valueAsSlice srcV with
       | .ok dst, .ok src =>
           let count := Nat.min dst.len src.len
           (sliceElemLocs src count).map ((false, ·))
             ++ (sliceElemLocs dst count).map ((true, ·))
       | _, _ => []) ++ targetWrite tv
  | .mapDelete _, [bv, _] => mapAccess true bv
  | .clearMap, [bv] => mapAccess true bv
  | .clearSlice _, [bv] =>
      match valueAsSlice bv with
      | .ok slice => (sliceElemLocs slice slice.len).map ((true, ·))
      | .error _ => []
  | .sortSlice _, [bv] =>
      match valueAsSlice bv with
      | .ok slice =>
          (sliceElemLocs slice slice.len).map ((false, ·))
            ++ (sliceElemLocs slice slice.len).map ((true, ·))
      | .error _ => []
  | _, _ => []

/-! ## The detector state

Vector clocks per goroutine, the per-`Loc` access shadow, and the
per-channel synchronization clocks. The pool threads one `RaceState`
alongside the `MultiConfig` (external instrumentation, like `Choices`
and fuel: it OBSERVES steps and never influences them except by the
terminal `raceDetected` refusal) — deterministic given the stream, no
`Choices` consumption, kernel-reducible plain structures. -/

/-- Per-channel synchronization clocks — gc's race instrumentation
realized (`runtime/chan.go`'s `racenotify`/`racesync`/`racerelease`/
`raceacquire` points), which is what keeps the in-machine
classification structurally aligned with the `go run -race` oracle:

* `slots` — one clock per buffer slot (`max 1 cap`); a buffered send
  RELEASE-ACQUIREs slot `sendCount % size`, a buffered receive slot
  `recvCount % size`. Slot reuse every `cap` operations is EXACTLY the
  memory model's counting-semaphore rule — go_mem: "The kth receive on
  a channel with capacity C is synchronized before the k+Cth send from
  that channel completes" — and the release half of the send slot-op
  is go_mem's "A send on a channel is synchronized before the
  completion of the corresponding receive from that channel."
* `closeVC` — the closer's clock; a receive that returns a zero value
  because the channel is closed ACQUIREs it — go_mem: "The closing of
  a channel is synchronized before a receive that returns a zero value
  because the channel is closed." (A close-woken SENDER's panic gets
  NO edge — gc's woken `chansend` path performs no `raceacquire`;
  TSan-aligned, the fail-closed direction.)
* unbuffered rendezvous is the bidirectional `racesync` (both go_mem
  directions at once: send-before-receive AND "A receive from an
  unbuffered channel is synchronized before the completion of the
  corresponding send on that channel"), implemented as
  `RaceState.rendezvous` at the pool's pairing step. -/
structure ChanClocks where
  slots : Array VClock
  sendCount : Nat := 0
  recvCount : Nat := 0
  closeVC : Option VClock := none
  deriving Repr, BEq

/-- Update-or-insert in a `Loc`-keyed association list. -/
def assocSet {α : Type} (xs : List (Loc × α)) (loc : Loc) (v : α) :
    List (Loc × α) :=
  match xs with
  | [] => [(loc, v)]
  | (l, w) :: rest =>
      if l == loc then (loc, v) :: rest else (l, w) :: assocSet rest loc v

/-- The detector state: per-goroutine clocks (index = pool goroutine
id; absent = the birth clock), the access shadow, the channel clocks.
Empty until the pool holds a second goroutine — a single goroutine
cannot race with itself (every access is sequenced), so the detector
is inert on sequential runs BY CONSTRUCTION (the conservation
theorem's hinge, and the whole-corpus zero-overhead guarantee). -/
structure RaceState where
  clocks : Array VClock := #[]
  shadow : List (Loc × ShadowCell) := []
  chans : List (Loc × ChanClocks) := []
  deriving Repr, BEq

def RaceState.vcOf (r : RaceState) (t : Nat) : VClock :=
  (r.clocks[t]?).getD (VClock.birth t)

/-- Set goroutine `t`'s clock, padding missing peers with their birth
clocks. -/
def RaceState.setVC (r : RaceState) (t : Nat) (vc : VClock) : RaceState :=
  let clocks :=
    if t < r.clocks.size then r.clocks
    else r.clocks ++ (Array.range (t + 1 - r.clocks.size)).map
      (fun k => VClock.birth (r.clocks.size + k))
  { r with clocks := clocks.setIfInBounds t vc }

def RaceState.chanOf (r : RaceState) (loc : Loc) (cap : Nat) : ChanClocks :=
  match r.chans.find? (·.1 == loc) with
  | some (_, cc) => cc
  | none => { slots := Array.replicate (max 1 cap) #[] }

def RaceState.setChan (r : RaceState) (loc : Loc) (cc : ChanClocks) : RaceState :=
  { r with chans := assocSet r.chans loc cc }

/-- RELEASE-ACQUIRE on the channel's next send/receive buffer slot
(gc's `racenotify` — see `ChanClocks`): the goroutine's clock joins the
slot's, the slot takes the joined clock, the goroutine's own epoch
bumps (the FastTrack release increment). -/
def RaceState.slotOp (r : RaceState) (t : Nat) (loc : Loc) (cap : Nat)
    (isSend : Bool) : RaceState :=
  let cc := r.chanOf loc cap
  let size := max 1 cc.slots.size
  let idx := (if isSend then cc.sendCount else cc.recvCount) % size
  let joined := (r.vcOf t).join ((cc.slots[idx]?).getD #[])
  let cc' := { cc with
    slots := cc.slots.setIfInBounds idx joined
    sendCount := if isSend then cc.sendCount + 1 else cc.sendCount
    recvCount := if isSend then cc.recvCount else cc.recvCount + 1 }
  (r.setVC t (joined.bump t)).setChan loc cc'

/-- Unbuffered rendezvous (gc's `racesync`): both goroutines join each
other's clocks — both go_mem directions of the unbuffered rules — then
each bumps its own epoch. -/
def RaceState.rendezvous (r : RaceState) (i j : Nat) : RaceState :=
  let joined := (r.vcOf i).join (r.vcOf j)
  (r.setVC i (joined.bump i)).setVC j (joined.bump j)

/-- `close(ch)` releases the closer's clock into `closeVC` (gc's
`racerelease(c.raceaddr())`). -/
def RaceState.closeOp (r : RaceState) (t : Nat) (loc : Loc) (cap : Nat) :
    RaceState :=
  let cc := r.chanOf loc cap
  let vt := r.vcOf t
  let cc' := { cc with closeVC := some (vt.join ((cc.closeVC).getD #[])) }
  (r.setVC t (vt.bump t)).setChan loc cc'

/-- A receive that returns the zero value because the channel is
closed acquires the closer's clock (gc's closed-and-empty
`raceacquire`). -/
def RaceState.closeAcquire (r : RaceState) (t : Nat) (loc : Loc) : RaceState :=
  match r.chans.find? (·.1 == loc) with
  | some (_, cc) =>
      match cc.closeVC with
      | some cv => r.setVC t ((r.vcOf t).join cv)
      | none => r
  | none => r

/-- The `go` statement's edge — go_mem: "The go statement that starts
a new goroutine is synchronized before the start of the goroutine's
execution." The child is born with the parent's clock (own epoch 1);
the parent's epoch bumps, so its post-spawn accesses are visibly
unordered with the child. The goroutine-EXIT direction gets NO edge —
go_mem: "The exit of a goroutine is not guaranteed to be synchronized
before any event in the program." -/
def RaceState.spawn (r : RaceState) (parent child : Nat) : RaceState :=
  let pv := r.vcOf parent
  let childVC := (pv.pad (child + 1)).setIfInBounds child 1
  (r.setVC parent (pv.bump parent)).setVC child childVC

/-- Check ONE access against the shadow, then record it. A conflict —
some overlapping path holds an access by another goroutine that is not
happens-before this goroutine's current point, with at least one side
a write — is the terminal `raceDetected` (fail closed per run; the
message is fixed so the refusal is choice-invariant per stream). -/
def RaceState.access (r : RaceState) (t : Nat) (a : RaceAccess) :
    Except GoError RaceState :=
  let (isWrite, loc) := a
  let vt := r.vcOf t
  let conflict := r.shadow.any fun (l, cell) =>
    locOverlap loc l &&
      (ShadowCell.someConcurrent cell.writes t vt
        || (isWrite && ShadowCell.someConcurrent cell.reads t vt))
  if conflict then throw .raceDetected
  else
    let cell := ((r.shadow.find? (·.1 == loc)).map (·.2)).getD {}
    let myE := vt.get t
    let cell' :=
      if isWrite then { cell with writes := ShadowCell.upsert cell.writes t myE }
      else { cell with reads := ShadowCell.upsert cell.reads t myE }
    return { r with shadow := assocSet r.shadow loc cell' }

def RaceState.accesses (r : RaceState) (t : Nat) :
    List RaceAccess → Except GoError RaceState
  | [] => return r
  | a :: rest => do RaceState.accesses (← r.access t a) t rest

/-- The write of one phase-2 store step (`storeK`): the resolved
target path. Chain resolution itself reads no user memory (address
formation — see the module docstring); a resolution/bounds/nil failure
means the step panics and no store happens. -/
def storeTargetAccess (s : ExecState) (r : TargetRef) : List RaceAccess :=
  match r with
  | .chain anchor idxs steps =>
      match resolveChain s anchor steps idxs with
      | .ok v => targetWrite v
      | .error _ => []
  | .mapElem b _ _ _ => mapAccess true b

/-- **The footprint of one PRIVATE machine step**, from its pre-step
configuration: which user-memory paths the step reads/writes. Every
configuration shape not listed performs no user-memory access (control
gluing, operand accumulation, address formation, fresh allocation,
channel/select operations — the latter are the registry's
synchronization ops, handled by the HB updater in `Multi.lean`, and
race-free by spec). Completeness over access-bearing shapes is a
lockstep obligation (module docstring). -/
def stepAccesses (s : ExecState) (c : Config) : List RaceAccess :=
  match c with
  | .evalE (.var id) env _ =>
      match LocalEnv.lookup env id with
      | some loc => [(false, loc)]
      | none => []
  | .retV v (.strictK op done [] _ _) =>
      strictOpAccesses op ((v :: done).reverse)
  | .retV _ (.assignStoreK loc _) => [(true, loc)]
  | .retV v (.stmtOpK op _ done [] _ _) =>
      stmtOpAccesses op ((v :: done).reverse)
  | .retV v (.mapRangeK _ _ _ _ _ _ _) => mapAccess false v
  | .next (.storeK (r :: _) (_ :: _) _ _ _) => storeTargetAccess s r
  | .next (.frame targets results [] _ _) =>
      results.map ((false, ·)) ++ targets.map ((true, ·))
  | .returning (.frame targets results [] _ _) =>
      results.map ((false, ·)) ++ targets.map ((true, ·))
  | _ => []

end GoLean.GoCore.Machine
