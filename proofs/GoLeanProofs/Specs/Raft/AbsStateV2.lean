import GoLeanProofs.Specs.Raft.LensInst
import GoLeanProofs.Specs.Raft.AllocEqWave1
import GoLeanProofs.Specs.Raft.BfFixture

/-!
# absState v2 — the raftLog / message / outbox projections (A4-U8
slice D; the seam's layer-(A) growth, lens-consuming from birth)

The wave-2 message handlers read and write the log view (raftLog =
stable storage ⊕ the unstable overlay), message fields, and the
outboxes. v1 (`AbsState.lean`, untouched) projects one node's scalars;
this module adds, per the U6 wave-2 charter item 3 and the lens design
§4:

- `absRaftLog` (CLOSES **GAP-V1-1b**): the log view — `absStorageEnts`
  (U4, reused) through the storage interface + the unstable overlay
  (`unstable` is an EMBEDDED value field, U7 contact) + the
  `committed`/`applying`/`applied` scalars. The offset arithmetic is
  re-grounded from `log_unstable.go` in the derived views
  (`AbsLog.lastIndex`, `AbsLog.view`), kept as PURE functions beside
  the reader.
- `absMessage`: the `raftpb.Message` projection (plainpb
  pointer-scalars, `Reject : *bool`, entries + context slices).
  **GAP-V2-1 (RESOLVED BY CENSUS, recorded not guessed):**
  `Responses : slice (*Message)` is read ONLY by `util.go`'s printer
  and `rawnode.go`'s Ready/Advance plumbing (wave 3) — never by the
  wave-2 handlers (`grep -n Responses raftsubject/raft/*.go`,
  2026-08-24) — so v2 deliberately does NOT project it and the reader
  needs NO fuel/structural bound. A wave-3 extension owes the fueled
  recursive form. `Snapshot : *raftpb.Snapshot` is likewise
  deliberately unprojected (the wave-2 handlers do not read it;
  `handleSnapshot` is out of wave-2 scope) — **GAP-V2-2**, recorded.
- `absOutbox` (feeds **GAP-V1-3**): `r.msgs` / `r.msgsAfterAppend`
  via `sliceRead ∘ absMessage`. A nil outbox slice reads as the empty
  list (the lens's nil-slice arm — Go's nil slice IS the empty
  slice).

Every access goes through the lens combinators, so **L4 gives each
new reader's placement transport below** (`absRaftLog_ren`,
`absMessage_ren`, `absOutbox_ren`) by composition — no hand `_ren`
re-derivation against the heap walk (charter item 1,
symbolic-from-birth, holds by construction).

GAP-V1-2 (tracker) and -4 (AbstractNet) remain open; -5 stays by
design.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.Lens GoLean.Frame

/-! ## Target-side deref shims (the plainpb getter semantics:
nil pointer → the zero value, exactly `derefU64`'s pattern from U4) -/

/-- `*bool` dereference: nil → `false` (`GetReject` on a nil field). -/
def derefBool (σ : ExecState) : GoValue → Option Bool
  | .nil => some false
  | .addr l => (Heap.lookup σ.heap l).bind fun c => readBool c.value
  | _ => none

/-- `*int32`-kinded dereference: nil → `0` (`GetType` on a nil field —
`raftpb.MessageType`'s underlying kind is `int32`, LensInst's
`message_Type_ty`). -/
def derefI32 (σ : ExecState) : GoValue → Option Int
  | .nil => some 0
  | .addr l => (Heap.lookup σ.heap l).bind fun c => readIntK .int32 c.value
  | _ => none

/-- The base address behind an interface value (the storage field's
shape: `.interface tid (.addr (.base a))`). Fail closed on nil
interfaces and non-base inner locs. -/
def ifaceBaseAddr : GoValue → Option Addr
  | .interface _ (.addr (.base a)) => some a
  | _ => none

/-! ## `absRaftLog` -/

/-- The abstract log view: the stable half (MemoryStorage `ents`,
dummy-entry convention included), the unstable overlay, and the
raftLog scalars. -/
structure AbsLog where
  stable : List (Int × Int)
  unstableEnts : List (Int × Int)
  offset : Int
  committed : Int
  applying : Int
  applied : Int
  deriving Repr, DecidableEq

/-- The unstable half, read from the EMBEDDED `raft.unstable` value
(one cell hop above; `fieldOfValue` — the U7 contact's layout). -/
def absUnstableV (σ : ExecState) (uv : GoValue) :
    Option (List (Int × Int) × Int) := do
  let entsv ← fieldOfValue uv ⟨"raft.unstable"⟩ "entries"
  let es ← sliceRead σ entsv (fun σ v => absEntry σ v)
  let offv ← fieldOfValue uv ⟨"raft.unstable"⟩ "offset"
  let off ← readU64 offv
  pure (es, off)

/-- **THE LOG READER** (total, first-order, fail-closed; every access
through the lens): the raftLog cell at `Loc.base a`. -/
def absRaftLog (σ : ExecState) (a : Addr) : Option AbsLog := do
  let committed ← fieldReadU64 σ a ⟨"raft.raftLog"⟩ "committed"
  let applying ← fieldReadU64 σ a ⟨"raft.raftLog"⟩ "applying"
  let applied ← fieldReadU64 σ a ⟨"raft.raftLog"⟩ "applied"
  let stv ← fieldRead σ a ⟨"raft.raftLog"⟩ "storage"
  let ms ← ifaceBaseAddr stv
  let stable ← absStorageEnts σ ms
  let uv ← fieldRead σ a ⟨"raft.raftLog"⟩ "unstable"
  let u ← absUnstableV σ uv
  pure { stable, unstableEnts := u.1, offset := u.2,
         committed, applying, applied }

/-- `raftLog.lastIndex`, re-grounded (`log_unstable.go:maybeLastIndex`
— the unstable half wins when non-empty: `offset + len - 1`;
`log.go:lastIndex` falls back to `storage.LastIndex()` =
`ents[0].index + len(ents) - 1`, `storage.go`). The unstable SNAPSHOT
branch is unprojected (nil in every wave-2 fixture; part of
GAP-V2-2's scope). `none` on an empty storage (the dummy entry is an
invariant — `specFirstIndex`'s note). -/
def AbsLog.lastIndex (L : AbsLog) : Option Int :=
  if L.unstableEnts.length ≠ 0 then
    some (L.offset + L.unstableEnts.length - 1)
  else
    L.stable.head?.map (fun hd => hd.1 + L.stable.length - 1)

/-- The combined entry view: stable entries strictly below the
unstable offset, then the overlay (`log.go`: unstable entries shadow
storage from `offset` up). -/
def AbsLog.view (L : AbsLog) : List (Int × Int) :=
  L.stable.filter (fun p => p.1 < L.offset) ++ L.unstableEnts

/-! ## `absMessage` -/

/-- One abstract message. Field map: `typ`=Type (MessageType numeral),
`dst`=To, `src`=From (renamed — `from` is a Lean keyword); the rest
1:1. `Responses`/`Snapshot` deliberately absent (GAP-V2-1 and
GAP-V2-2, module docstring). -/
structure AbsMessage where
  typ : Int
  dst : Int
  src : Int
  term : Int
  logTerm : Int
  index : Int
  commit : Int
  vote : Int
  rejectHint : Int
  reject : Bool
  entries : List (Int × Int)
  context : List Int
  deriving Repr, DecidableEq

/-- **THE MESSAGE READER**: project one `*raftpb.Message` (the outbox
element shape — `absEntry`'s pattern, one deref to the message cell,
then value-level lens reads). -/
def absMessage (σ : ExecState) : GoValue → Option AbsMessage
  | .addr l => do
      let cell ← Heap.lookup σ.heap l
      let mv := cell.value
      let typ ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "Type").bind (derefI32 σ)
      let dst ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "To").bind (derefU64 σ)
      let src ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "From").bind (derefU64 σ)
      let term ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "Term").bind (derefU64 σ)
      let logTerm ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "LogTerm").bind
        (derefU64 σ)
      let index ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "Index").bind
        (derefU64 σ)
      let commit ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "Commit").bind
        (derefU64 σ)
      let vote ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "Vote").bind (derefU64 σ)
      let rejectHint ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "RejectHint").bind
        (derefU64 σ)
      let reject ← (fieldOfValue mv ⟨"raftpb.Message"⟩ "Reject").bind
        (derefBool σ)
      let entsv ← fieldOfValue mv ⟨"raftpb.Message"⟩ "Entries"
      let entries ← sliceRead σ entsv (fun σ v => absEntry σ v)
      let ctxv ← fieldOfValue mv ⟨"raftpb.Message"⟩ "Context"
      let context ← sliceRead σ ctxv (fun _ v => readIntK .uint8 v)
      pure { typ, dst, src, term, logTerm, index, commit, vote,
             rejectHint, reject, entries, context }
  | _ => none

/-! ## `absOutbox` -/

/-- **THE OUTBOX READER**: an outbox field of the raft cell at
`Loc.base a` (`f` ∈ {"msgs", "msgsAfterAppend"}), each element
projected by `absMessage`. -/
def absOutbox (σ : ExecState) (a : Addr) (f : String) :
    Option (List AbsMessage) := do
  let base ← fieldRead σ a ⟨"raft.raft"⟩ f
  sliceRead σ base (fun σ v => absMessage σ v)

/-! ## L4 transports — every v2 reader's placement invariance BY
COMPOSITION of the lens laws (this section is the demonstration that
the hand `_ren` pattern is retired for lens-stated readers: no heap
walk is re-derived below, only lens/`_ren` lemmas compose) -/

theorem derefBool_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {b : Bool} (h : derefBool σ v = some b) :
    derefBool σF (renameValue r v) = some b := by
  cases v with
  | nil => simpa [derefBool, renameValue] using h
  | addr l =>
      simp only [derefBool, renameValue]
      simp only [derefBool] at h
      cases hc : Heap.lookup σ.heap l with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some c =>
          rw [hc] at h
          rw [hF.lookup_some hc]
          show readBool (renameCell r c).value = some b
          rw [show (renameCell r c).value = renameValue r c.value from rfl,
            readBool_ren]
          simpa using h
  | _ => simp [derefBool] at h

theorem derefI32_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {i : Int} (h : derefI32 σ v = some i) :
    derefI32 σF (renameValue r v) = some i := by
  cases v with
  | nil => simpa [derefI32, renameValue] using h
  | addr l =>
      simp only [derefI32, renameValue]
      simp only [derefI32] at h
      cases hc : Heap.lookup σ.heap l with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some c =>
          rw [hc] at h
          rw [hF.lookup_some hc]
          show readIntK .int32 (renameCell r c).value = some i
          rw [show (renameCell r c).value = renameValue r c.value from rfl,
            readIntK_ren]
          simpa using h
  | _ => simp [derefI32] at h

theorem ifaceBaseAddr_ren (r : Nat → Nat) {v : GoValue} {a : Addr}
    (h : ifaceBaseAddr v = some a) :
    ifaceBaseAddr (renameValue r v) = some ⟨r a.id⟩ := by
  cases v with
  | interface t inner =>
      cases inner with
      | addr l =>
          cases l with
          | base b =>
              have hb : b = a := by simpa [ifaceBaseAddr] using h
              subst hb
              rfl
          | _ => simp [ifaceBaseAddr] at h
      | _ => simp [ifaceBaseAddr] at h
  | _ => simp [ifaceBaseAddr] at h

theorem absUnstableV_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {uv : GoValue} {p : List (Int × Int) × Int}
    (h : absUnstableV σ uv = some p) :
    absUnstableV σF (renameValue r uv) = some p := by
  unfold absUnstableV at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨entsv, hentsv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨es, hes, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨offv, hoffv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨off, hoff, h⟩ := Option.bind_eq_some_iff.mp h
  rw [fieldOfValue_ren, hentsv]
  simp only [Option.map_some, Option.bind_some]
  rw [sliceRead_ren hF (fun v x hx => absEntry_ren hF hx) hes]
  simp only [Option.bind_some]
  rw [fieldOfValue_ren, hoffv]
  simp only [Option.map_some, Option.bind_some]
  rw [readU64_ren, hoff]
  simpa using h

/-- **Log-projection rename-invariance** (loc-free output, transports
verbatim). -/
theorem absRaftLog_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {L : AbsLog} (h : absRaftLog σ a = some L) :
    absRaftLog σF ⟨r a.id⟩ = some L := by
  unfold absRaftLog at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨committed, hcm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨applying, hap, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨applied, had, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨stv, hstv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ms, hms, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨stable, hstable, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨uv, huv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
  rw [fieldReadU64_ren hF hcm]
  simp only [Option.bind_some]
  rw [fieldReadU64_ren hF hap]
  simp only [Option.bind_some]
  rw [fieldReadU64_ren hF had]
  simp only [Option.bind_some]
  rw [fieldRead_ren hF hstv]
  simp only [Option.bind_some]
  rw [ifaceBaseAddr_ren r hms]
  simp only [Option.bind_some]
  rw [absStorageEnts_ren hF hstable]
  simp only [Option.bind_some]
  rw [fieldRead_ren hF huv]
  simp only [Option.bind_some]
  rw [absUnstableV_ren hF hu]
  simpa using h

/-- **Message-projection rename-invariance**. -/
theorem absMessage_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {m : AbsMessage} (h : absMessage σ v = some m) :
    absMessage σF (renameValue r v) = some m := by
  cases v with
  | addr l =>
      simp only [absMessage, renameValue, Option.bind_eq_bind] at h ⊢
      cases hc : Heap.lookup σ.heap l with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some c =>
          rw [hc] at h
          rw [hF.lookup_some hc]
          simp only [Option.bind_some] at h ⊢
          rw [show (renameCell r c).value = renameValue r c.value from rfl]
          obtain ⟨typ, htyp, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨tv, htv, hdt⟩ := Option.bind_eq_some_iff.mp htyp
          obtain ⟨dst, hdst, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨dv, hdv, hdd⟩ := Option.bind_eq_some_iff.mp hdst
          obtain ⟨src, hsrc, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨sv, hsv, hds⟩ := Option.bind_eq_some_iff.mp hsrc
          obtain ⟨term, hterm, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨tmv, htmv, hdtm⟩ := Option.bind_eq_some_iff.mp hterm
          obtain ⟨logTerm, hlt, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨ltv, hltv, hdlt⟩ := Option.bind_eq_some_iff.mp hlt
          obtain ⟨index, hix, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨ixv, hixv, hdix⟩ := Option.bind_eq_some_iff.mp hix
          obtain ⟨commit, hcmt, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨cmv, hcmv, hdcm⟩ := Option.bind_eq_some_iff.mp hcmt
          obtain ⟨vote, hvt, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨vtv, hvtv, hdvt⟩ := Option.bind_eq_some_iff.mp hvt
          obtain ⟨rejectHint, hrh, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨rhv, hrhv, hdrh⟩ := Option.bind_eq_some_iff.mp hrh
          obtain ⟨reject, hrj, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨rjv, hrjv, hdrj⟩ := Option.bind_eq_some_iff.mp hrj
          obtain ⟨entsv, hentsv, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨entries, hents, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨ctxv, hctxv, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨context, hctx, h⟩ := Option.bind_eq_some_iff.mp h
          rw [fieldOfValue_ren, htv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefI32_ren hF hdt]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hdv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hdd]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hsv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hds]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, htmv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hdtm]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hltv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hdlt]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hixv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hdix]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hcmv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hdcm]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hvtv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hdvt]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hrhv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefU64_ren hF hdrh]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hrjv]
          simp only [Option.map_some, Option.bind_some]
          rw [derefBool_ren hF hdrj]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hentsv]
          simp only [Option.map_some, Option.bind_some]
          rw [sliceRead_ren hF (fun v x hx => absEntry_ren hF hx) hents]
          simp only [Option.bind_some]
          rw [fieldOfValue_ren, hctxv]
          simp only [Option.map_some, Option.bind_some]
          rw [sliceRead_ren hF
            (fun v x hx => by rw [readIntK_ren]; exact hx) hctx]
          simpa using h
  | _ => simp [absMessage] at h

/-- **Outbox-projection rename-invariance**. -/
theorem absOutbox_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {f : String} {ms : List AbsMessage}
    (h : absOutbox σ a f = some ms) :
    absOutbox σF ⟨r a.id⟩ f = some ms := by
  unfold absOutbox at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨base, hbase, h⟩ := Option.bind_eq_some_iff.mp h
  rw [fieldRead_ren hF hbase]
  simp only [Option.bind_some]
  exact sliceRead_ren hF (fun v x hx => absMessage_ren hF hx) h

/-! ## Discharge witnesses (§3.3; every value below #eval-checked
first — probe `artifacts/probe/AbsV2Probe.lean`) -/

/-- The log reader, live on the U3 populated fixture (`uσ`,
BfFixture): stable `[(1,1)]` through the storage interface, empty
unstable overlay at offset 2, scalars 1/1/1. -/
theorem absV2_witness_log :
    absRaftLog (uσ 7 2 1 5) ⟨1⟩ = some ⟨[(1, 1)], [], 2, 1, 1, 1⟩ := by
  kernel_rfl

theorem absV2_witness_lastIndex :
    (absRaftLog (uσ 7 2 1 5) ⟨1⟩).map AbsLog.lastIndex
      = some (some 1) := by
  rw [absV2_witness_log]
  rfl

/-- The outbox reader, live on the same fixture: the init-state nil
`msgs` slice reads as the EMPTY outbox (the lens's nil-slice arm,
exercised). -/
theorem absV2_witness_outbox :
    absOutbox (uσ 7 2 1 5) ⟨0⟩ "msgs" = some [] := by
  kernel_rfl

private def tyMsg : Ty := .defined ⟨"raftpb.Message"⟩

/-- The machine's own default `raftpb.Message` with the `Term` field
pointed at a real cell (value 9) — every other plainpb pointer nil. -/
private def wMsgVal : GoValue :=
  match defaultValue wBase tyMsg with
  | .ok (.struct tid fs) =>
      match StructFields.set fs "Term" (.addr (.base ⟨1⟩)) with
      | .ok fs2 => .struct tid fs2
      | .error _ => .nil
  | _ => .nil

private def σMsg : ExecState :=
  { wBase with heap := [(.base ⟨0⟩, ⟨some tyMsg, wMsgVal⟩),
                        (.base ⟨1⟩, ⟨some (.int .uint64), .int 9 .uint64⟩)],
               nextAddr := 2 }

/-- The message reader, live: nil pointers read as zeros (the plainpb
getter semantics), the populated `Term` reads 9, the nil slices read
empty. -/
theorem absV2_witness_message :
    absMessage σMsg (.addr (.base ⟨0⟩))
      = some ⟨0, 0, 0, 9, 0, 0, 0, 0, 0, false, [], []⟩ := by
  kernel_rfl

/-- The L4 transport, live at the zero-shift seed on the populated
fixture (`absRaftLog_ren` consumed exactly as a wave-2 alloc-form
equation will consume it). -/
theorem absV2_witness_L4 :
    absRaftLog (uσ 7 2 1 5) ⟨ρT 21 0 1⟩ = some ⟨[(1, 1)], [], 2, 1, 1, 1⟩ :=
  absRaftLog_ren
    (frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 21 f.body))
    absV2_witness_log

end GoLean.RaftSeam
