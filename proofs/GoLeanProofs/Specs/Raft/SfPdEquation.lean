import GoLeanProofs.Specs.Raft.SfPdLit
import GoLeanProofs.Specs.Raft.AbsStateV2

/-!
# A4-U16: THE stepFollower × MsgProp DROP-ARM EQUATION — the
choice-free arm, and the dispatch-complement extension's first
PROVED consumer

**LINEAGE: the SfHbEquation template (§4c arm conventions) at the
degenerate chain: ONE window, ZERO crossings, ZERO atoms** — the
cheapest possible arm equation, and the first whose fixture carries
the FULL static block (`staticComplementFull`, U12 + U15-ext) as a
live proof dependency: the walk derefs static cell 17
(`ErrProposalDropped`, census read at step 232) and the er conclusion
is the error box over payload 65.

Census (U15 slice-1 re-census, `StepDispatchProbe2`): **254 steps,
ZERO choices**, na 98→112, `.next .stop`; the U14 finding stands that
WITHOUT the extension this walk STICKS at cell 17 step 235 — the
fail-closed control. Fixture-family preconditions (§4c form):
- `m.Type = 2` (MsgProp) CONCRETE — the switch driver;
- **`r.lead = 0` CONCRETE — the no-leader DROP branch** (the arm
  branches on it; lead ≠ 0 is the forward-arm family, censused
  1,272/1); the fixture forces bf31's symbolic x₂ to `lit 0`;
- Vote (x₁) / state (x₃) / leadTransferee (x₄) ride symbolic; **the
  drop path never stores the raft struct, so Vote survives as RAW
  `var 1` (wrap depth ZERO — generator-probed per the §4c rule) and
  the readout needs NO range side condition.**

Statement conventions per §4c: er readout mandatory (here the arm's
POINT: `er` = the ErrProposalDropped box, whose payload address 65 is
BELOW every na₀ so it rides renaming unchanged); conclusions via
absState v2 / lens / renameCell-fixed lookups; ∀-stream with the
stream UNTOUCHED (choice-free); alloc PRIMARY + identity + witness.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/SfPdGen.lean` — the
window link re-checks the literal against these defs). -/

def sfpdMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- bf31SymHeap with the lead field FORCED to concrete 0 — the drop
branch's precondition (x₂ is not free in this family). -/
def sfpdRaftHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨31⟩ then
      (p.1, match p.2 with
        | .mk dty (.struct tid fs) =>
            .mk dty (.struct tid (fs.map (fun (q : String × SymValue) =>
              if q.1 == "lead" then (q.1, .int (.lit 0) .uint64) else q)))
        | c => c)
    else p)

def sfpdS0 : SymState :=
  { heap := sfpdRaftHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) sfpdMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 2) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)] ++
      staticComplementSym ++ staticComplementExtSym,
    nextAddr := staticComplementNa }

def sfpdEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

/-- The drained caller shape: `er := raft.stepFollower(r, m)`. -/
def sfpdC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepFollower"⟩ #[Expr.var "r", Expr.var "m"])
    sfpdEnv .stop

/-- The er conclusion's value: the `ErrProposalDropped` error box —
an interface over the static payload cell 65 ("raft proposal
dropped"). Every address it carries (65) is below every consumer
na₀, so `renameCell` fixes it. -/
def errProposalDroppedBox : GoValue :=
  .interface (.pointer (.defined ⟨"raft.goleanShimErrorString"⟩))
    (.addr (.base ⟨65⟩))

/-! ## The window LINK theorem (kernel-checked; also the LIVE proof
that the static complement suffices for this path — without the
extension this evaluation sticks at cell 17, U14/U15-measured). -/

theorem sfpdW1_out :
    symEvalWindowTB bfTB sfpdW1n sfpdS0 sfpdC0 = (sfpdW1n, sfpdS1, .next .stop) := by
  kernel_rfl

/-- The transported window IS the full span (choice-free: the stream
rides untouched — ∀ ch, no prefix). -/
theorem sfpd_full_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter sfpdW1n (γS ρ σ sfpdS0) (γC ρ sfpdC0) ch
      = .ok (.next .stop, γS ρ σ sfpdS1, ch) := by
  have h := symEvalWindowTB_refines sfpdW1_out ρ σ ch hag
  have hstop : γC ρ (.next .stop) = Machine.Config.next .stop := rfl
  rw [hstop] at h
  exact h

/-! ## Projection facts at the literals. -/

theorem sfpd_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ sfpdS0) (.addr (.base ⟨52⟩))
      = some ⟨2, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem sfpd_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ sfpdS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem sfpd_post_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ sfpdS1) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

/-- THE ARM'S POINT: er = ErrProposalDropped (the box over static
payload 65 — the extension's cells live in a shipped conclusion). -/
theorem sfpd_post_er (ρ : Valuation) (σ : ExecState) :
    GoCore.Heap.lookup (γS ρ σ sfpdS1).heap (.base ⟨68⟩)
      = some ⟨some (.interface ⟨"error"⟩), errProposalDroppedBox⟩ := by
  kernel_rfl

theorem sfpd_post_msgs (ρ : Valuation) (σ : ExecState) :
    absOutbox (γS ρ σ sfpdS1) ⟨31⟩ "msgs" = some [] := by
  kernel_rfl

theorem sfpd_post_maa (ρ : Valuation) (σ : ExecState) :
    absOutbox (γS ρ σ sfpdS1) ⟨31⟩ "msgsAfterAppend" = some [] := by
  kernel_rfl

theorem sfpd_post_lead (ρ : Valuation) (σ : ExecState) :
    fieldReadU64 (γS ρ σ sfpdS1) ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 0 := by
  kernel_rfl

/-- Vote rides RAW (wrap depth ZERO — the drop path never stores the
raft struct; generator-probed). No range side condition needed. -/
theorem sfpd_post_vote (ρ : Valuation) (σ : ExecState) :
    fieldReadU64 (γS ρ σ sfpdS1) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (ρ.ints 1) := by
  kernel_rfl

theorem sfpd_post_term (ρ : Valuation) (σ : ExecState) :
    fieldReadU64 (γS ρ σ sfpdS1) ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic). -/

/-- **THE stepFollower × MsgProp DROP-ARM EQUATION** (no-leader
family): from the drained `er := stepFollower(r, m)` call at ANY
placement (FrameSim premise), on EVERY choice stream (the arm is
CHOICE-FREE — the stream rides untouched, the first proved arm with
this property), the run returns in exactly **254 steps** and:
the message projects with typ 2 (MsgProp); **er = the
ErrProposalDropped error box** (the proposal is dropped, not
forwarded — the arm's whole meaning; the extension's static cells in
a shipped conclusion); both outboxes stay EMPTY (nothing sent); the
log view, lead (= 0), Vote (raw — no store on this path), and Term
are all preserved. -/
theorem stepFollower_propDrop_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ sfpdS0) σF) :
    ∃ σFfin,
      stepFnIter 254 σF (renameConfig r (γC ρ sfpdC0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ sfpdS1) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨2, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σFfin.heap (.base ⟨r 68⟩)
          = some ⟨some (.interface ⟨"error"⟩), renameValue r errProposalDroppedBox⟩
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some []
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some 0
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hrun : stepFnIter 254 (γS ρ σ sfpdS0) (γC ρ sfpdC0) ch
      = .ok (.next .stop, γS ρ σ sfpdS1, ch) := sfpd_full_span ρ σ ch hag
  obtain ⟨σFfin, htF, hs⟩ := span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := sfpd_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (sfpd_pre_absRaftLog ρ σ)
  · exact hs.lookup_some (sfpd_post_er ρ σ)
  · exact absOutbox_ren hs (sfpd_post_msgs ρ σ)
  · exact absOutbox_ren hs (sfpd_post_maa ρ σ)
  · exact absRaftLog_ren hs (sfpd_post_absRaftLog ρ σ)
  · exact fieldReadU64_ren hs (sfpd_post_lead ρ σ)
  · exact fieldReadU64_ren hs (sfpd_post_vote ρ σ)
  · exact fieldReadU64_ren hs (sfpd_post_term ρ σ)

/-- The identity-placement corollary (the concrete equation; the
error box appears VERBATIM — identity renaming fixes payload 65). -/
theorem stepFollower_propDrop_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ σfin,
      stepFnIter 254 (γS ρ σ sfpdS0) (γC ρ sfpdC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ sfpdS0) (.addr (.base ⟨52⟩))
          = some ⟨2, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ sfpdS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), errProposalDroppedBox⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 0
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT staticComplementNa 0) staticComplementNa
      staticComplementNa [] (γS ρ σ sfpdS0) (γS ρ σ sfpdS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero staticComplementNa f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, her, hob, hmaa, hlog1, hl, hv, ht⟩ :=
    stepFollower_propDrop_eq_alloc ρ σ hag ch hF
  have hcall : renameConfig (ρT staticComplementNa 0) (γC ρ sfpdC0)
      = γC ρ sfpdC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h52 : (⟨ρT staticComplementNa 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h31 : (⟨ρT staticComplementNa 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT staticComplementNa 0 32⟩ : Addr) = ⟨32⟩ := rfl
  have h68 : (⟨ρT staticComplementNa 0 68⟩ : Addr) = ⟨68⟩ := rfl
  have hbox : renameValue (ρT staticComplementNa 0) errProposalDroppedBox
      = errProposalDroppedBox := by
    with_unfolding_all rfl
  rw [h52] at hmsg
  rw [h32] at hlog0 hlog1
  rw [h68, hbox] at her
  rw [h31] at hob hmaa hl hv ht
  exact ⟨σfin, hrun, hmsg, hlog0, her, hob, hmaa, hlog1, hl, hv, ht⟩

/-! ## §3.3 discharge witness (Vote 7; empty stream — choice-free). -/

def sfpdρw : Valuation :=
  { ints := fun i => [0, 7, 0, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem stepFollower_propDrop_eq_witness :
    ∃ σfin,
      stepFnIter 254 (γS sfpdρw wBase sfpdS0) (γC sfpdρw sfpdC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS sfpdρw wBase sfpdS0) (.addr (.base ⟨52⟩))
          = some ⟨2, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS sfpdρw wBase sfpdS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), errProposalDroppedBox⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 0
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  stepFollower_propDrop_eq sfpdρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

end GoLean.RaftSeam
