import GoLean.CLI

/-!
# `choice-trace` — the labeled-consumption tracer and menu-invariant validator

LANE TOOLING (membership-depth lane, 2026-09-01; assessment findings
B4/B13, C3-F3, D-10, E-D8). NOT a gate, NOT part of the trusted surface:
it reads the machine, it never changes it.

Two questions the differential apparatus could not answer before this
module existed:

1. **Depth exposure of the strict lane (B4).** The strict lane re-runs a
   row under three fixed 8–10-entry choice streams; `Choices.consume` on
   an exhausted stream yields pick 0 (State.lean), so every consumption
   past the prefix is the canonical default and the "adversarial" runs
   converge to the default trajectory. Nothing measured how many
   consumptions a strict row actually makes. This tracer replays ONE
   stream in lockstep with the consumption accountant (`CLI.stepNeeds` /
   `CLI.stepNeedsSeq`, the enumerator's mirror of the machine's
   consumption points) and records EVERY consumption: site, bound, the
   stream value drawn (or EXHAUSTED), the realized pick.

2. **modeled ⊆ permitted at the site level (C3 finding 3).** Per
   consumption it checks the MENU INVARIANTS: the pick is inside the
   bound; the bound equals the width the latitude census states for the
   site (C1–C6, C8, E9, R2 rows of
   `docs/2026-08-11_latitude-inventory.md`), recomputed here from the
   PRE-STATE by a second, deliberately simple derivation rather than
   read back from the machine's menu function; plus per-site structural
   invariants (scheduler menu is a permutation of the runnable set with
   the declared slot-0 convention; every waiter candidate is a parked
   partner; a select's commit count equals its ready-clause count; the
   map stop slot is offered exactly when no mandatory entry remains;
   the append-spill slot map is a bijection onto [newLen, upper]).

WHAT IT DOES NOT WITNESS (stated so the claim is not over-read): menu
CONTENT beyond the bound and the structural checks above — e.g. that
the goroutine at slot k is the goroutine the spec would let run (the
spec is silent, so any runnable one is fine, and runnability itself is
taken from the machine's `threadRunnable`); that a "ready" clause is
ready per the spec (readiness is recomputed with the machine's own
`clauseReady`, so this is a consistency check between two machine
functions, not an oracle); that the append envelope's UPPER end is the
right pragmatic subset (R2's width is a DECLARED subset of the spec's
unbounded latitude — the check is against the declaration).

THREE-WAY SELF-CHECK on every run (so the tracer cannot silently drift
from what it traces): (a) the site-tagged mirror here must agree with
`CLI.stepNeeds` on every bound; (b) the sentinel discipline of the
enumerator — a pool step fed exactly the accounted picks plus one
sentinel must leave the sentinel alone; (c) the machine's OWN labeled
records (`StepEvent.picks`, emitted by `Choices.consumeAtE` at the
pool-layer sites) must equal the tracer's records for those sites.
Additionally the run's status and consumption count are checked
against `CLI.enumRunProgram`'s leftover meter and the real engine's
observation (`runProgramPoolIntsM`) — the driver-agreement pin.
-/

namespace GoLean.ChoiceTrace

open GoLean GoLean.GoCore GoLean.GoCore.Machine

def siteName : ChoiceSite → String
  | .mapIter => "mapIter"
  | .appendSpill => "appendSpill"
  | .l2Entry => "l2Entry"
  | .l2Arrival => "l2Arrival"
  | .l4Waiter => "l4Waiter"
  | .l1Sched => "l1Sched"
  | .l5ExitWindow => "l5ExitWindow"
  | .postOp => "postOp"
  | .backEdge => "backEdge"
  | .nilValueMethodText => "nilValueMethodText"
  | .tryLock => "tryLock"

def allSites : List ChoiceSite :=
  [.mapIter, .appendSpill, .l2Entry, .l2Arrival, .l4Waiter, .l1Sched,
   .l5ExitWindow, .postOp, .backEdge, .nilValueMethodText, .tryLock]

/-- Pool-layer sites: the ones whose consumption the machine records in
`StepEvent.picks` (`Choices.consumeAtE`); the sequential-machine sites
(`mapIter`, `appendSpill`, `l2Entry`, `tryLock`) and the driver's
`l5ExitWindow` consume through `Choices.consumeAt` and emit no record. -/
def isPoolRecorded : ChoiceSite → Bool
  | .l1Sched | .postOp | .backEdge | .l2Arrival | .l4Waiter => true
  | _ => false

/-- The menu facts for one consumption, computed from the PRE-STATE
before the pick is drawn. -/
structure MenuFacts where
  /-- The width the census states for the site (C1–C6/C8: |runnable| or
  #matching waiters or #ready clauses; C4: 2; E9: candidates + stop slot;
  R2: the declared envelope width), independently recomputed. `none`
  when the recomputation itself failed (reported as a violation). -/
  specWidth : Option Nat
  /-- Structural invariants evaluated on the pre-state: (name, holds). -/
  invariants : List (String × Bool)
  /-- Pick-dependent checks (given the realized pick). -/
  pickCheck : Nat → List String

def MenuFacts.violations (f : MenuFacts) (site : ChoiceSite) (bound pick : Nat) :
    List String :=
  let w := match f.specWidth with
    | none => [s!"{siteName site}: spec-width recomputation failed"]
    | some w => if w == bound then []
        else [s!"{siteName site}: bound {bound} ≠ recomputed width {w}"]
  let inv := f.invariants.filterMap fun (name, ok) =>
    if ok then none else some s!"{siteName site}: {name}"
  let pk := if pick < max 1 bound then [] else [s!"{siteName site}: pick {pick} ≥ bound {bound}"]
  w ++ inv ++ pk ++ (f.pickCheck pick).map (s!"{siteName site}: " ++ ·)

structure Consumption where
  idx : Nat
  phase : String
  site : ChoiceSite
  bound : Nat
  /-- `none` = the stream was EXHAUSTED at this consumption (the machine
  drew the canonical default 0). -/
  streamValue : Option Nat
  pick : Nat
  violations : List String

structure Acc where
  stream : List Nat
  phase : String := "init"
  consumed : Array Consumption := #[]
  alarms : Array String := #[]
  steps : Nat := 0

/-- Draw one consumption from the stream (0 on exhaustion, as the
machine does), recording it with its menu-invariant verdict. Returns the
RAW value to feed the machine (the machine reduces modulo the bound
itself). -/
def Acc.draw (a : Acc) (site : ChoiceSite) (bound : Nat) (facts : MenuFacts) :
    Nat × Acc :=
  let (sv, rest) := match a.stream with
    | [] => ((none : Option Nat), ([] : List Nat))
    | c :: r => (some c, r)
  let raw := sv.getD 0
  let pick := raw % (max 1 bound)
  let c : Consumption :=
    { idx := a.consumed.size, phase := a.phase, site, bound, streamValue := sv, pick
      violations := facts.violations site bound pick }
  (raw, { a with stream := rest, consumed := a.consumed.push c })

def Acc.alarm (a : Acc) (msg : String) : Acc :=
  { a with alarms := a.alarms.push msg }

/-! ## Independent re-derivations used by the menu facts -/

/-- Parked partners of an arriving op on channel `loc` from goroutine
`i`: threads ≠ i parked on the OPPOSITE side, select clauses counted
individually (the C5 census width: "#matches (select clauses counted
individually)"). A deliberately plain scan over the thread shapes. -/
def parkedPartners (threads : Array Config) (i : Nat) (loc : Loc)
    (arrivingSend : Bool) : Nat :=
  (List.range threads.size).foldl (init := 0) fun acc j =>
    if j == i then acc else
    match threads[j]? with
    | some (.blockedRecv (some l) _ _ _ _) =>
        if arrivingSend && l == loc then acc + 1 else acc
    | some (.blockedSend (some l) _ _) =>
        if !arrivingSend && l == loc then acc + 1 else acc
    | some (.blockedSelect evs _ _) =>
        acc + (evs.filter fun ev =>
          match ev with
          | .recvEv chv _ _ _ => arrivingSend && chanValueLoc chv == some loc
          | .sendEv chv _ _ _ => !arrivingSend && chanValueLoc chv == some loc).length
    | _ => acc

/-- Partners for an op on channel value `chv` (nil channel: none; closed
channel: none — a send panics, a receive drains/zeroes, neither pairs). -/
def partnersFor (s : ExecState) (threads : Array Config) (i : Nat)
    (chv : GoValue) (arrivingSend : Bool) : Option Nat :=
  match chanValueLoc chv with
  | none => some 0
  | some loc =>
      match chanCell s loc with
      | .ok (_, _, closed) => if closed then some 0 else some (parkedPartners threads i loc arrivingSend)
      | .error _ => none

def clauseChan : EvClause → (Bool × GoValue)
  | .sendEv chv _ _ _ => (true, chv)
  | .recvEv chv _ _ _ => (false, chv)

def sortNats (l : List Nat) : List Nat := (l.toArray.qsort (· < ·)).toList

/-- Scheduler-family facts (C1 l1Sched, C2 backEdge, C3 postOp): width =
|runnable|; the slot menu is a permutation of the runnable set; slot 0 =
lowest runnable (l1Sched) or the current goroutine (postOp/backEdge). -/
def schedFacts (m : MultiConfig) (site : ChoiceSite) (menu : List Nat) : MenuFacts :=
  let rs := runnableIdxs m.shared m.threads
  let indep := (List.range m.threads.size).filter fun j =>
    match m.threads[j]? with
    | some c => threadRunnable m.shared c
    | none => false
  { specWidth := some indep.length
    invariants :=
      [ ("menu.length = |runnableIdxs|", menu.length == rs.length),
        ("menu is a permutation of the runnable set", sortNats menu == sortNats rs),
        ("slots are distinct", menu.eraseDups.length == menu.length),
        ("every slot indexes a live thread", menu.all (· < m.threads.size)),
        (match site with
          | .l1Sched => ("l1Sched: menu = runnableIdxs in goroutine order", menu == rs)
          | _ => ("postOp/backEdge: slot 0 = the current goroutine", menu.head? == some m.cur)) ]
    pickCheck := fun p => if p < menu.length then [] else [s!"pick {p} outside the {menu.length}-slot menu"] }

def exitWindowFacts (m : MultiConfig) : MenuFacts :=
  let rs := runnableIdxs m.shared m.threads
  { specWidth := some 2
    invariants :=
      [ ("window opens only with a runnable other goroutine", !rs.isEmpty),
        ("main is at its terminal", m.mainOutcome?.isSome) ]
    pickCheck := fun _ => [] }

/-- Waiter-pick facts (C5): the candidate list against the independent
partner scan for the arriving op's channel/side. `chvSide` = the
arriving clause's (isSend, chan value) when it could be determined. -/
def waiterFacts (s : ExecState) (threads : Array Config) (i : Nat)
    (chvSide : Option (Bool × GoValue)) (cands : List (Nat × PairTarget)) : MenuFacts :=
  let expected := match chvSide with
    | some (isSend, chv) => partnersFor s threads i chv isSend
    | none => none
  { specWidth := expected
    invariants :=
      [ ("every candidate partner is a parked goroutine", cands.all fun c =>
          match threads[c.2.partnerIdx]? with
          | some pc => isBlockedConfig pc
          | none => false),
        ("no candidate is the arriving goroutine", cands.all fun c => c.2.partnerIdx != i),
        ("candidates are distinct", (cands.map (·.2)).eraseDups.length == cands.length),
        ("≥ 2 candidates (a singleton pairs without a pick)", cands.length ≥ 2) ]
    pickCheck := fun p => if p < cands.length then [] else [s!"pick {p} outside {cands.length} candidates"] }

/-- The arriving clause (side, chan value) of a chan-op config. -/
def chanOpClause (c : Config) : Option (Bool × GoValue) :=
  match c with
  | .retV v (.chanStK op done [] _ _) =>
      match op, (v :: done).reverse with
      | .send _, chv :: _ => some (true, chv)
      | .recv _ _, chv :: _ => some (false, chv)
      | _, _ => none
  | _ => none

/-- The evaluated clauses of a select at its apply position. -/
def selectEvs (c : Config) : Option (Except Stop (List EvClause) × Nat) :=
  match c with
  | .retV v (.selectOpsK clauses _ done [] _ _) =>
      some (evalClauses clauses ((v :: done).reverse), clauses.length)
  | _ => none

/-- Arrival-path select facts (C6, waiter-extended readiness): width =
#clauses that are cell-ready or have a parked partner. -/
def arrivalFacts (s : ExecState) (threads : Array Config) (i : Nat) (c : Config)
    (os : Nat) : MenuFacts :=
  match selectEvs c with
  | some (.ok evs, n) =>
      let readyCount := evs.foldl (init := (some 0 : Option Nat)) fun acc ev =>
        match acc with
        | none => none
        | some k =>
          let (isSend, chv) := clauseChan ev
          let cell := match clauseReady s ev with | .ok b => some b | .error _ => none
          match cell, partnersFor s threads i chv isSend with
          | some b, some w => some (k + (if b || w > 0 then 1 else 0))
          | _, _ => none
      { specWidth := readyCount
        invariants := [ ("2 ≤ outcomes ≤ #clauses", 2 ≤ os && os ≤ n) ]
        pickCheck := fun p => if p < os then [] else [s!"pick {p} outside {os} outcomes"] }
  | _ => { specWidth := none, invariants := [("select apply shape recognized", false)], pickCheck := fun _ => [] }

/-- Entry-path select facts (C6, cell readiness): width = #ready clauses. -/
def entryFacts (s : ExecState) (c : Config) (commits : Nat) : MenuFacts :=
  match selectEvs c with
  | some (.ok evs, n) =>
      let readyCount := evs.foldl (init := (some 0 : Option Nat)) fun acc ev =>
        match acc, clauseReady s ev with
        | some k, .ok b => some (k + (if b then 1 else 0))
        | _, _ => none
      { specWidth := readyCount
        invariants := [ ("2 ≤ commits ≤ #clauses", 2 ≤ commits && commits ≤ n) ]
        pickCheck := fun p => if p < commits then [] else [s!"pick {p} outside {commits} commits"] }
  | _ => { specWidth := none, invariants := [("select apply shape recognized", false)], pickCheck := fun _ => [] }

/-- Map-iteration facts (E9): candidates = live entries whose id is not
yet produced; the stop slot is offered exactly when no never-removed
start entry (an id in `start`) remains unproduced. Pure `Nat`
membership since the B1 entry-identity stamps (2026-09-03). -/
def mapIterFacts (s : ExecState) (base : Option Loc)
    (produced start : Array Nat) : MenuFacts :=
  match mapIterLiveEntries s base with
  | .error _ => { specWidth := none, invariants := [("live map cell readable", false)], pickCheck := fun _ => [] }
  | .ok live =>
      let (cands, mand) := live.toList.foldl (init := ((0 : Nat), false)) fun (cands, mand) e =>
        if produced.contains e.1 then (cands, mand)
        else (cands + 1, mand || start.contains e.1)
      { specWidth := some (cands + (if mand then 0 else 1))
        invariants :=
          [ ("candidates ≤ live entries", cands ≤ live.size),
            ("stop slot offered iff no mandatory entry remains", true) ]
        pickCheck := fun p =>
          (if p > cands then [s!"pick {p} beyond the stop slot {cands}"] else []) ++
          (if p == cands && mand then ["stop slot taken while a mandatory entry remains"] else []) }

/-- Append-spill facts (R2): the DECLARED envelope [newLen, upper] with
upper = `appendSpillUpper`; every slot realizes a capacity ≥ newLen (the
spec floor) and ≤ upper; slot 0 is the growth-formula point; the slot map
is a bijection onto the envelope. -/
def spillFacts (s : ExecState) (c : Config) : MenuFacts :=
  let bad := fun (why : String) =>
    ({ specWidth := none, invariants := [(why, false)], pickCheck := fun _ => [] } : MenuFacts)
  match c with
  | .retV v (.stmtOpK (.appendSlice _) _ done [] _ _) =>
      match (v :: done).reverse with
      | [_, sliceV, elemsV] =>
          match valueAsSlice sliceV, valueAsSlice elemsV with
          | .ok slice, .ok elems =>
              match sliceVisibleValues s elems with
              | .error _ => bad "appended elements readable"
              | .ok elemValues =>
                  let newLen := slice.len + elemValues.size
                  let growth := appendGrowthCap slice.cap newLen
                  let upper := appendSpillUpper slice.cap newLen
                  let width := upper - newLen + 1
                  let capOf := fun (e : Nat) => newLen + ((growth - newLen + e) % width)
                  let bij := if width ≤ 8192 then
                      sortNats ((List.range width).map capOf) == (List.range width).map (newLen + ·)
                    else true
                  { specWidth := some width
                    invariants :=
                      [ ("spill only when newLen > cap", newLen > slice.cap),
                        ("newLen ≤ growth ≤ upper", newLen ≤ growth && growth ≤ upper),
                        (s!"slot map is a bijection onto [newLen, upper]{if width > 8192 then " (skipped: width > 8192)" else ""}", bij) ]
                    pickCheck := fun p =>
                      let cap := capOf p
                      (if cap < newLen then [s!"realized cap {cap} below the spec floor newLen={newLen}"] else []) ++
                      (if cap > upper then [s!"realized cap {cap} above the declared upper {upper}"] else []) ++
                      (if p == 0 && cap != growth then [s!"slot 0 is not the growth-formula point ({cap} ≠ {growth})"] else []) }
          | _, _ => bad "append operands are slices"
      | _ => bad "append operand arity"
  | _ => bad "append apply shape recognized"

/-- Frame-entry panic-text facts (BUG-087, R9a): the DECLARED width is
2 on the wrapper family and the site is consulted only there; the
structural invariants recompute the family's shape from the pre-state by
a second, simpler derivation — the receiver argument is an interface box
holding a nil POINTER, the anchor is an interface-receiver method, and
the resolved target is a value-receiver method of exactly the pointee
that is not a synthesized promotion wrapper. -/
def nilTextFacts (s : ExecState) (fid : FuncId) (args : List GoValue) : MenuFacts :=
  let bad := fun (why : String) =>
    ({ specWidth := none, invariants := [(why, false)], pickCheck := fun _ => [] } : MenuFacts)
  match findFunctionIn? s.functions fid with
  | none => bad "entry function found"
  | some func =>
    match methodInfoByFuncId? s func.id with
    | none => bad "entry anchor is a method"
    | some method =>
      let anchorIsIface := (methodRecvInterfaceName? s method).isSome
      let nilPtrBox := match args.head? with
        | some (.interface (.pointer _) .nil) => true
        | _ => false
      let pointee : Option Ty := match args.head? with
        | some (.interface (.pointer elem) _) => some elem
        | _ => none
      let target := s.methods.find? fun m =>
        m.name == method.name && (pointee.map fun e => methodRecvDynamicTy? s m == some e).getD false
      let valueRecvOfPointee := target.isSome
      let notWrapper := match target >>= fun m => findFunctionIn? s.functions m.funcId with
        | some f => !f.wrapper
        | none => false
      { specWidth := some 2
        invariants :=
          [ ("anchor is an interface-receiver method", anchorIsIface),
            ("receiver argument is an interface box holding a nil pointer", nilPtrBox),
            ("target is a value-receiver method of exactly the pointee", valueRecvOfPointee),
            ("target is not a synthesized promotion wrapper", notWrapper) ]
        pickCheck := fun p => if p < 2 then [] else [s!"pick {p} outside the two texts"] }

/-- TryLock facts (Q-TRYLOCK, `ChoiceSite.tryLock`): the width is
recomputed through the machine's own `tryLockWidth` over the receiver
cell (2 iff `tryAcquire` says acquirable, else 1 — and a width-1 consult
pops nothing, so the mirror only reports a site at width 2). -/
def tryLockFacts (s : ExecState) (c : Config) : MenuFacts :=
  let bad := fun (why : String) =>
    ({ specWidth := none, invariants := [(why, false)], pickCheck := fun _ => [] } : MenuFacts)
  match c with
  | .retV v (.syncStK op done [] _ _) =>
      match op.tryTargets?, (v :: done).reverse with
      | some _, [av] =>
          match valueAsLoc av with
          | .error _ => bad "try-lock receiver is an address"
          | .ok loc =>
              match syncCell s loc with
              | .error _ => bad "try-lock receiver cell is a sync primitive"
              | .ok pre =>
                  let w := tryLockWidth op pre
                  let acquirable := match tryAcquire op pre with
                    | .ok (some _) => true
                    | _ => false
                  { specWidth := some w
                    invariants :=
                      [ ("width ∈ {1, 2}", w == 1 || w == 2),
                        ("width 2 iff the cell is acquirable (tryAcquire)", (w == 2) == acquirable) ]
                    pickCheck := fun p =>
                      (if p ≥ w then [s!"pick {p} outside the width {w}"] else []) ++
                      (if w == 1 && p != 0 then ["a held cell forces slot 0 (false)"] else []) }
      | _, _ => bad "try-lock apply shape recognized"
  | _ => bad "try-lock apply shape recognized"

/-! ## The site-tagged consumption mirror -/

/-- The sequential-machine sites at a `stepFn` position (the mirror of
`CLI.stepNeedsSeq`, tagged with the census site and the menu facts). -/
def seqSite (σ : ExecState) (c : Config) :
    Option (ChoiceSite × Nat × MenuFacts) :=
  match c with
  | .next (.mapIterK _ _ keyTy valTy _ base produced start _ _) =>
      match mapIterCandidates σ keyTy valTy base produced with
      | .error _ => none
      | .ok cands =>
          if cands.isEmpty then none
          else
            let mand := mapIterMandatoryRemains cands start
            some (.mapIter, cands.size + (if mand then 0 else 1),
                mapIterFacts σ base produced start)
  | .retV v (.selectOpsK clauses default? done [] env k) =>
      match applySelectCore σ clauses default? ((v :: done).reverse) env k with
      | .ok (.picks commits) => some (.l2Entry, commits.length, entryFacts σ c commits.length)
      | _ => none
  | .retV v (.stmtOpK (.appendSlice _) _ done [] _ _) =>
      match (v :: done).reverse with
      | [_, sliceV, elemsV] =>
          match valueAsSlice sliceV, valueAsSlice elemsV with
          | .ok slice, .ok elems =>
              let newLen := slice.len + elems.len
              if newLen ≤ slice.cap then none
              else some (.appendSpill, appendSpillWidth slice.cap newLen, spillFacts σ c)
          | _, _ => none
      | _ => none
  | .retV v (.syncStK op done [] _ _) =>
      -- The TRY heads' `tryLock` site (Q-TRYLOCK): the bound is the
      -- machine's own `tryLockWidth` over the receiver cell; width 1
      -- pops nothing (`consumeAtOne := false`), so no site is reported.
      match op.tryTargets?, (v :: done).reverse with
      | some _, [av] =>
          match valueAsLoc av with
          | .error _ => none
          | .ok loc =>
              match syncCell σ loc with
              | .error _ => none
              | .ok pre =>
                  let w := tryLockWidth op pre
                  if w ≤ 1 then none else some (.tryLock, w, tryLockFacts σ c)
      | _, _ => none
  | c =>
      -- The frame-entry panic-text site (BUG-087): the mirror of
      -- `CLI.stepNeedsSeq`'s arm, tagged.
      match entryCallSite? c with
      | some (fid, args) =>
          if nilValueMethodWidth σ fid args ≤ 1 then none
          else some (.nilValueMethodText, nilValueMethodWidth σ fid args, nilTextFacts σ fid args)
      | none => none

/-- The pool-step mirror of `CLI.stepNeeds`, tagged: given the picks
already supplied for the CURRENT pool step, the next consumption's site,
bound, and menu facts — or `none` when the step draws nothing further. -/
def poolSite (m : MultiConfig) (picks : List Nat) :
    Option (ChoiceSite × Nat × MenuFacts) :=
  match m.threads[m.cur]? with
  | none => none
  | some c₀ =>
    let site₀ := c₀.boundarySite
    let menu := schedSlots m.shared m.threads m.cur site₀
    let l1 : Option (Nat × List Nat) :=
      if c₀.atBoundary then
        match menu with
        | [] => none
        | [j] => some (j, picks)
        | rs =>
            match picks with
            | [] => none
            | p :: rest =>
                match rs[p % rs.length]? with
                | some j => some (j, rest)
                | none => none
      else some (m.cur, picks)
    match c₀.atBoundary, menu, picks with
    | true, _ :: _ :: _, [] => some (site₀, menu.length, schedFacts m site₀ menu)
    | _, _, _ =>
      match l1 with
      | none => none
      | some (i, ch) =>
        match m.threads[i]? with
        | none => none
        | some c =>
          if isBlockedConfig c then none
          else if (opDoneInner c).isSome then none
          else
            match spawnPlan c with
            | some _ =>
                match entryCallSite? c with
                | some (fid, args) =>
                    if nilValueMethodWidth m.shared fid args ≤ 1 then none
                    else match ch with
                      | [] => some (.nilValueMethodText, nilValueMethodWidth m.shared fid args,
                          nilTextFacts m.shared fid args)
                      | _ :: _ => none
                | none => none
            | none =>
              match arrivalCases m.shared m.threads i c with
              | .error _ => none
              | .ok (.single _ cs) =>
                  if cs.length ≤ 1 then none
                  else match ch with
                    | [] => some (.l4Waiter, cs.length,
                        waiterFacts m.shared m.threads i (chanOpClause c) cs)
                    | _ :: _ => none
              | .ok (.multi os) =>
                  match ch with
                  | [] => some (.l2Arrival, os.length, arrivalFacts m.shared m.threads i c os.length)
                  | p :: rest =>
                      match os[p % os.length]? with
                      | some (.pair _ cs) =>
                          if cs.length ≤ 1 then none
                          else match rest with
                            | [] =>
                                -- The chosen clause's channel/side, for
                                -- the independent partner scan.
                                let chvSide : Option (Bool × GoValue) :=
                                  match cs.head?, selectEvs c with
                                  | some (ci, _), some (.ok evs, _) =>
                                      (evs[ci]?).map clauseChan
                                  | _, _ => none
                                some (.l4Waiter, cs.length,
                                  waiterFacts m.shared m.threads i chvSide cs)
                            | _ :: _ => none
                      | _ => none
              | .ok .cellPath =>
                  -- The sequential machine's own sites: at most one pick
                  -- per step, so a supplied pick means nothing further.
                  match ch with
                  | [] => seqSite m.shared c
                  | _ :: _ => none

/-! ## The lockstep driver -/

structure RunOutcome where
  status : String
  acc : Acc

/-- Records of THIS step for the pool-recorded sites, in order — to be
compared with the machine's own `StepEvent.picks`. -/
def stepRecords (a : Acc) (from_ : Nat) : List PickRecord :=
  (a.consumed.toList.drop from_).filterMap fun c =>
    if isPoolRecorded c.site then some ⟨c.site, c.bound, c.pick⟩ else none

partial def feedPicks (m : MultiConfig) (picks : List Nat) (a : Acc) : List Nat × Acc :=
  match poolSite m picks with
  | none =>
      -- Cross-check (a): the tagged mirror vs the accountant.
      let a := match CLI.stepNeeds m picks with
        | none => a
        | some b => a.alarm s!"mirror/accountant drift: mirror says no further consumption, stepNeeds says bound {b} (after {picks.length} pick(s))"
      (picks, a)
  | some (site, bound, facts) =>
      let a := match CLI.stepNeeds m picks with
        | some b => if b == bound then a
            else a.alarm s!"mirror/accountant drift at {siteName site}: mirror bound {bound}, stepNeeds {b}"
        | none => a.alarm s!"mirror/accountant drift at {siteName site}: mirror bound {bound}, stepNeeds says none"
      let (raw, a) := a.draw site bound facts
      feedPicks m (picks ++ [raw]) a

mutual

partial def poolLoop (fuel : Nat) (m : MultiConfig) (r : RaceState) (a : Acc) :
    Except String RunOutcome := do
  if m.threads.isEmpty then throw "thread pool without a main goroutine"
  match m.panicMsg? with
  | some _ => return { status := "panic", acc := a }
  | none =>
    match m.mainOutcome? with
    | some (.normal _) =>
        match runnableIdxs m.shared m.threads with
        | [] => return { status := "ok", acc := a }
        | _ :: _ =>
            let a := { a with phase := "exit" }
            let (raw, a) := a.draw .l5ExitWindow 2 (exitWindowFacts m)
            if raw % 2 == 0 then return { status := "ok", acc := a }
            else
              match fuel with
              | 0 => return { status := "fuel-out", acc := a }
              | fuel' + 1 => poolStep fuel' m r { a with phase := "pool" }
    | some _ => throw "main terminal outside its barrier frame"
    | none =>
      if (runnableIdxs m.shared m.threads).isEmpty then
        return { status := "deadlock", acc := a }
      else
        match fuel with
        | 0 => return { status := "fuel-out", acc := a }
        | fuel' + 1 => poolStep fuel' m r a

partial def poolStep (fuel : Nat) (m : MultiConfig) (r : RaceState) (a : Acc) :
    Except String RunOutcome := do
  let from_ := a.consumed.size
  let (picks, a) := feedPicks m [] a
  -- Cross-check (b): the sentinel discipline.
  match stepMulti m (picks ++ [0]) with
  | .error e =>
      -- The machine's own terminal refusal/diagnostic (unsupported, stuck,
      -- internal, fatal, …) is the run's STATUS, traced up to this point
      -- — the same classification `native-json-run` prints.
      return { status := e.status, acc := a }
  | .ok (m', leftover, ev) =>
      let a := if leftover == [0] then a
        else a.alarm s!"sentinel drift: step left {leftover} (accountant {if leftover.isEmpty then "MISSED a site" else "over-counted"})"
      -- Cross-check (c): the machine's own labeled records.
      let mine := stepRecords a from_
      let a := if mine == ev.picks then a
        else a.alarm s!"pick-record mismatch: machine emitted {ev.picks.length} record(s), tracer has {mine.length} for the pool-recorded sites at consumption #{from_}"
      let a := { a with steps := a.steps + 1 }
      match raceUpdate m.shared m.threads ev m' r with
      | .error .raceDetected => return { status := "race", acc := a }
      | .error e => throw s!"race-detector update failed: {e.status}: {e.message}"
      | .ok r' => poolLoop fuel m' r' a

end

partial def initLoop (fuel : Nat) (σ : ExecState) (c : Config) (a : Acc) :
    Except String (Sum (ExecState × Acc) RunOutcome) := do
  match c with
  | .next .stop => return .inl (σ, a)
  | .panicked _ => return .inr { status := "panic", acc := a }
  | .blockedSend _ _ _ | .blockedRecv _ _ _ _ _ | .blockedSelect _ _ _ =>
      return .inr { status := "deadlock", acc := a }
  | c =>
    match fuel with
    | 0 => return .inr { status := "fuel-out", acc := a }
    | fuel' + 1 =>
      let tagged := seqSite σ c
      let acct := CLI.stepNeedsSeq σ c
      let a := match tagged, acct with
        | none, none => a
        | some (_, b, _), some b' => if b == b' then a
            else a.alarm s!"init mirror/accountant drift: {b} vs {b'}"
        | some (site, b, _), none => a.alarm s!"init mirror/accountant drift: mirror {siteName site} bound {b}, stepNeedsSeq none"
        | none, some b => a.alarm s!"init mirror/accountant drift: mirror none, stepNeedsSeq {b}"
      let (picks, a) := match tagged with
        | some (site, b, facts) =>
            let (raw, a) := a.draw site b facts
            ([raw], a)
        | none => ([], a)
      match stepFn σ c (picks ++ [0]) with
      | .error e => return .inr { status := (markInitPhase e).status, acc := a }
      | .ok (c', σ', leftover) =>
          let a := if leftover == [0] then a
            else a.alarm s!"init sentinel drift: step left {leftover}"
          initLoop fuel' σ' c' { a with steps := a.steps + 1 }

/-- One traced run of the whole program under `stream`. -/
def traceProgram (ep : CLI.EnumProgram) (fuel : Nat) (stream : List Nat) :
    Except String RunOutcome := do
  let a₀ : Acc := { stream }
  let (σ₁, a₁) ←
    match ep.initBody? with
    | none => pure (ep.σ₀, a₀)
    | some body =>
        match ← initLoop fuel ep.σ₀ (.exec body [] (.frame [] [] [] [] .stop)) a₀ with
        | .inl r => pure r
        | .inr out => return out
  let a₁ := { a₁ with phase := "pool" }
  match bindParams [] σ₁ ep.func.args.toList ep.args.toList with
  | .error e => return { status := e.status, acc := a₁ }
  | .ok (env, s₂) =>
    match allocDecls env s₂ ep.func.results.toList with
    | .error e => return { status := e.status, acc := a₁ }
    | .ok (frameEnv, s₃) =>
      poolLoop fuel ⟨#[.exec ep.func.body frameEnv (.frame [] [] [] [] .stop)], s₃, 0⟩ {} a₁

/-! ## Streams -/

/-- A deterministic pseudo-random stream (64-bit LCG, values in
[0, 65536)) — the "long random stream" instrument for the depth
experiment; `rand:<seed>:<len>` on the command line. -/
def randomStream (seed len : Nat) : List Nat :=
  let m := 2 ^ 64
  let step := fun (x : Nat) => (x * 6364136223846793005 + 1442695040888963407) % m
  let rec go (x : Nat) (n : Nat) (acc : Array Nat) : Array Nat :=
    match n with
    | 0 => acc
    | n + 1 =>
        let x' := step x
        go x' n (acc.push ((x' / 2 ^ 33) % 65536))
  (go (seed % m) len #[]).toList

def parseStream (spec : String) : Except String (List Nat) :=
  if spec == "" || spec == "default" then .ok []
  else if spec.startsWith "rand:" then
    match spec.splitOn ":" with
    | ["rand", seedS, lenS] =>
        match String.toNat? seedS, String.toNat? lenS with
        | some seed, some len => .ok (randomStream seed len)
        | _, _ => .error s!"bad random stream spec: {spec}"
    | _ => .error s!"bad random stream spec: {spec}"
  else
    let parts := (spec.splitOn ",").filter (· ≠ "")
    match parts.mapM String.toNat? with
    | some xs => .ok xs
    | none => .error s!"bad stream spec: {spec}"

/-! ## Reporting -/

structure StreamReport where
  streamSpec : String
  status : String
  consumed : Nat
  /-- Consumptions with bound ≥ 2 (the only ones that carry latitude). -/
  wide : Nat
  /-- Index of the first EXHAUSTED consumption, if any. -/
  exhaustedAt : Option Nat
  /-- Bound-≥-2 consumptions drawn AFTER exhaustion — the invisible
  order-sensitivity the strict lane's three streams cannot see. -/
  wideAfterExhaustion : Nat
  perSite : List (ChoiceSite × Nat)
  maxBound : Nat
  violations : List String
  alarms : List String
  /-- The enumerator-driver observation (compressed JSON) — for
  variance comparison across streams. -/
  observation : String
  driverAgreement : String

def summarize (spec : String) (out : RunOutcome) (obs : String) (agree : String) : StreamReport :=
  let cs := out.acc.consumed.toList
  let exhaustedAt := (cs.find? fun c => c.streamValue.isNone).map (·.idx)
  { streamSpec := spec, status := out.status, consumed := cs.length
    wide := (cs.filter fun c => c.bound ≥ 2).length
    exhaustedAt
    wideAfterExhaustion := (cs.filter fun c => c.streamValue.isNone && c.bound ≥ 2).length
    perSite := allSites.filterMap fun s =>
      let n := (cs.filter fun c => c.site == s).length
      if n == 0 then none else some (s, n)
    maxBound := cs.foldl (fun m c => max m c.bound) 0
    violations := cs.flatMap (·.violations)
    alarms := out.acc.alarms.toList
    observation := obs
    driverAgreement := agree }

def perSiteString (ps : List (ChoiceSite × Nat)) : String :=
  if ps.isEmpty then "-" else ";".intercalate (ps.map fun (s, n) => s!"{siteName s}={n}")

def optNat : Option Nat → String
  | none => "-"
  | some n => toString n

def firstOrDash (l : List String) : String :=
  match l.head? with
  | none => "-"
  | some s => (s.replace "\t" " ").replace "\n" " "

def tsvHeader : String :=
  "\t".intercalate ["id", "stream", "status", "consumed", "wide", "exhaustedAt",
    "wideAfterExhaustion", "perSite", "maxBound", "violations", "firstViolation",
    "alarms", "firstAlarm", "obsHash", "driverAgreement"]

def StreamReport.tsvLine (id : String) (r : StreamReport) : String :=
  "\t".intercalate [id, (if r.streamSpec == "" then "default" else r.streamSpec), r.status,
    toString r.consumed, toString r.wide, optNat r.exhaustedAt, toString r.wideAfterExhaustion,
    perSiteString r.perSite, toString r.maxBound, toString r.violations.length,
    firstOrDash r.violations, toString r.alarms.length, firstOrDash r.alarms,
    toString r.observation.hash, r.driverAgreement]

/-- Trace one stream and run the driver-agreement cross-checks:
`CLI.enumRunProgram`'s status/leftover meter and the real engine's
observation. -/
def traceStream (program : Program) (functionName : String) (args : Array Int)
    (ep : CLI.EnumProgram) (fuel : Nat) (spec : String) : Except String StreamReport := do
  let stream ← parseStream spec
  let out ← traceProgram ep fuel stream
  -- Enumerator driver: observation + leftover meter. The meter is
  -- three-valued: `none` = no leftover available (the enumerator driver
  -- threw — deadlock/fuel-out/diagnostic — so nothing to compare);
  -- `some none` = the stream was fully consumed (count ≥ |stream|);
  -- `some (some n)` = exactly n consumed.
  let (enumStatus, enumObs, meter) :=
    match CLI.enumRunProgram ep fuel stream with
    | .ok (st, j, leftover) => (st, j.compress,
        (some (if leftover.isEmpty then (none : Option Nat) else some (stream.length - leftover.length)) : Option (Option Nat)))
    | .error e => (e.status, (CLI.observationOfRun (.error e)).compress, none)
  let realObs := (CLI.observationOfRun (runProgramPoolIntsM fuel program functionName args stream)).compress
  let mut agree : List String := []
  if enumStatus != out.status then
    agree := agree ++ [s!"status: tracer {out.status} vs enumerator {enumStatus}"]
  match meter with
  | some (some n) => if n != out.acc.consumed.size then
      agree := agree ++ [s!"meter: leftover says {n} consumed, tracer counted {out.acc.consumed.size}"]
  | some none => if out.acc.consumed.size < stream.length then
      agree := agree ++ [s!"meter: stream fully consumed per leftover, tracer counted only {out.acc.consumed.size} of {stream.length}"]
  | none => pure ()
  if realObs != enumObs then
    agree := agree ++ ["engine/enumerator observation mismatch"]
  let agreeS := if agree.isEmpty then "ok" else "MISMATCH: " ++ "; ".intercalate agree
  return summarize spec out enumObs agreeS

structure CaseSpec where
  id : String
  wire : String
  functionName : String
  args : Array Int
  streams : List String

def loadProgram (wire : String) : IO (Except String Program) := do
  let contents ← IO.FS.readFile wire
  match Lean.Json.parse contents with
  | .error err => return .error s!"{wire}: JSON parse error: {err}"
  | .ok json =>
      match GoLean.NativeToIR.decodeProgram json with
      | .error err => return .error s!"{wire}: {err}"
      | .ok program => return .ok program

/-- Run one case's streams; TSV lines out (a failing setup/run yields a
single `status=ERROR` line naming the cause — never a silent skip). -/
def runCase (spec : CaseSpec) (fuel : Nat) : IO (List String) := do
  let errLine := fun (what : String) =>
    "\t".intercalate [spec.id, "-", "ERROR", "-", "-", "-", "-", "-", "-", "0", (what.replace "\t" " ").replace "\n" " ", "0", "-", "-", "-"]
  match ← loadProgram spec.wire with
  | .error e => return [errLine e]
  | .ok program =>
    match CLI.enumSetup program spec.functionName (spec.args.map GoValue.int) with
    | .error e => return [errLine s!"setup failed: {e.status}: {e.message}"]
    | .ok ep =>
        let mut lines : List String := []
        for st in spec.streams do
          match traceStream program spec.functionName spec.args ep fuel st with
          | .error e => lines := lines ++ [errLine s!"stream {st}: {e}"]
          | .ok r => lines := lines ++ [r.tsvLine spec.id]
        return lines

/-- Manifest line: `id \t wire \t function \t args(csv or -) \t streams(;-separated;
"default" for the empty stream)`. -/
def parseCaseLine (line : String) : Except String CaseSpec :=
  match line.splitOn "\t" with
  | [id, wire, fn, argsS, streamsS] => do
      let args ← if argsS == "-" then pure #[] else
        match (argsS.splitOn ",").mapM String.toInt? with
        | some xs => pure xs.toArray
        | none => throw s!"{id}: bad args {argsS}"
      let streams := (streamsS.splitOn ";").map fun s => if s == "default" then "" else s
      return { id, wire, functionName := fn, args, streams }
  | _ => throw s!"bad manifest line (expected 5 tab-separated fields): {line}"

/-- Batch mode: append one TSV line per (case, stream) to `outPath` as it
goes (partial results survive an interrupted run); the header is written
when the file is created. -/
def runBatch (manifestPath outPath : String) (fuel : Nat) (skip take : Nat) : IO Nat := do
  let contents ← IO.FS.readFile manifestPath
  let lines := (contents.splitOn "\n").filter (fun l => l != "" && !l.startsWith "#")
  let lines := (lines.drop skip).take take
  let exists_ ← System.FilePath.pathExists outPath
  -- RESUMABLE: ids already present in the output are skipped, so an
  -- interrupted/restarted batch continues instead of duplicating (a
  -- case's lines are appended in one write, so presence = complete).
  let done : List String ←
    if exists_ then do
      let prior ← IO.FS.readFile outPath
      pure ((prior.splitOn "\n").filterMap fun l =>
        match l.splitOn "\t" with
        | id :: _ => if id == "id" || id == "" then none else some id
        | [] => none)
    else do
      IO.FS.writeFile outPath (tsvHeader ++ "\n")
      pure []
  let mut n := 0
  for line in lines do
    match parseCaseLine line with
    | .ok spec => if done.contains spec.id then continue
    | .error _ => pure ()
    match parseCaseLine line with
    | .error e => IO.FS.withFile outPath .append fun h => h.putStrLn ("\t".intercalate ["?", "-", "ERROR", "-", "-", "-", "-", "-", "-", "0", e, "0", "-", "-", "-"])
    | .ok spec =>
        let out ← runCase spec fuel
        IO.FS.withFile outPath .append fun h => for l in out do h.putStrLn l
    n := n + 1
  return n

/-! ## CLI -/

private def usage : String :=
  "usage:\n" ++
  "  golean choice-trace --input <wire.json> --function <name> [--arg-int <n> ...] [--fuel <n>]\n" ++
  "      [--stream <spec>]...      spec: default | n,n,... | rand:<seed>:<len>   (default: the empty stream)\n" ++
  "      [--trace]                 also print every consumption (idx phase site bound streamValue pick violations)\n" ++
  "  golean choice-trace --batch <manifest.tsv> --out <results.tsv> [--fuel <n>] [--skip <k>] [--take <n>]\n" ++
  "      manifest: id \\t wire \\t function \\t args(csv|-) \\t streams(;-separated)\n"

structure Args where
  input : Option String := none
  functionName : Option String := none
  args : Array Int := #[]
  fuel : Nat := 10000000
  streams : List String := []
  trace : Bool := false
  batch : Option String := none
  out : Option String := none
  skip : Nat := 0
  take : Nat := 1000000000
  help : Bool := false

private def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--help" :: _, a => .ok { a with help := true }
  | "-h" :: _, a => .ok { a with help := true }
  | "--input" :: p :: rest, a => parseArgs rest { a with input := some p }
  | "--function" :: f :: rest, a => parseArgs rest { a with functionName := some f }
  | "--arg-int" :: v :: rest, a =>
      match v.toInt? with
      | some i => parseArgs rest { a with args := a.args.push i }
      | none => .error s!"--arg-int: not an integer: {v}"
  | "--fuel" :: v :: rest, a =>
      match v.toNat? with
      | some n => parseArgs rest { a with fuel := n }
      | none => .error s!"--fuel: not a natural: {v}"
  | "--stream" :: s :: rest, a => parseArgs rest { a with streams := a.streams ++ [if s == "default" then "" else s] }
  | "--trace" :: rest, a => parseArgs rest { a with trace := true }
  | "--batch" :: p :: rest, a => parseArgs rest { a with batch := some p }
  | "--out" :: p :: rest, a => parseArgs rest { a with out := some p }
  | "--skip" :: v :: rest, a =>
      match v.toNat? with
      | some n => parseArgs rest { a with skip := n }
      | none => .error s!"--skip: not a natural: {v}"
  | "--take" :: v :: rest, a =>
      match v.toNat? with
      | some n => parseArgs rest { a with take := n }
      | none => .error s!"--take: not a natural: {v}"
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv {} with
  | .error e =>
      IO.eprintln e
      return 2
  | .ok a =>
    if a.help then
      IO.println usage
      return 0
    match a.batch with
    | some manifest =>
        match a.out with
        | none =>
            IO.eprintln s!"--batch needs --out <results.tsv>\n{usage}"
            return 2
        | some out =>
            let n ← runBatch manifest out a.fuel a.skip a.take
            IO.eprintln s!"choice-trace: {n} case(s) traced into {out}"
            return 0
    | none =>
      match a.input, a.functionName with
      | some input, some fn =>
          match ← loadProgram input with
          | .error e =>
              IO.eprintln s!"choice-trace: {e}"
              return 1
          | .ok program =>
            match CLI.enumSetup program fn (a.args.map GoValue.int) with
            | .error e =>
                IO.eprintln s!"choice-trace: setup failed: {e.status}: {e.message}"
                return 1
            | .ok ep =>
                let streams := if a.streams.isEmpty then [""] else a.streams
                let mut rc : UInt32 := 0
                IO.println tsvHeader
                for st in streams do
                  match traceStream program fn a.args ep a.fuel st with
                  | .error e =>
                      IO.eprintln s!"choice-trace: stream [{st}]: {e}"
                      rc := 1
                  | .ok r =>
                      IO.println (r.tsvLine input)
                      if a.trace then
                        match traceProgram ep a.fuel (← IO.ofExcept (parseStream st)) with
                        | .error e => IO.eprintln s!"choice-trace: {e}"
                        | .ok out =>
                            for c in out.acc.consumed do
                              IO.eprintln s!"  #{c.idx} {c.phase} {siteName c.site} bound={c.bound} stream={optNat c.streamValue} pick={c.pick}{if c.violations.isEmpty then "" else " VIOLATION: " ++ "; ".intercalate c.violations}"
                      if !r.violations.isEmpty || !r.alarms.isEmpty || r.driverAgreement != "ok" then
                        rc := 1
                return rc
      | _, _ =>
          IO.eprintln s!"provide --input <file> and --function <name>, or --batch\n{usage}"
          return 2

end GoLean.ChoiceTrace
