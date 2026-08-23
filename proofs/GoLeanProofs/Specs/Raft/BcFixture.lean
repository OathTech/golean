import GoLeanProofs.Specs.Raft.BpcEquation
import GoLeanProofs.Specs.Raft.BcLit

/-!
# A4-U4 wave 1: the becomeCandidate fixture and its 7-window chain

The reset-family's TERM-CHANGE member (`raftsubject/raft/raft.go:921-934`;
`reset(r.Term + 1)` always takes the term-change branch — Term 0 → 1,
Vote cleared then set to `r.id` — the second fixture family the U3
exit named). Fixture = the U3 populated heap with `state` CONCRETE 0
(the panic guard branches on it) and Vote/lead/leadTransferee symbolic
(x₁/x₂/x₄); every pre-symbolic scalar is OVERWRITTEN by the handler,
so the equation carries NO range side conditions.

**Probe provenance** (`artifacts/probe/BcProbe.lean`, the
#eval-before-rfl rule): machine phase 1 completes in **3,282 steps
consuming exactly 4 choices** (steps 686/870/899/928) with
`absRaftNode post = specBecomeCandidate pre 1`; mirror phase 2
reproduces it as **7 windows [686, 183, 28, 28, 28, 3, 2320] + 6
crossings** (pick x₅ at the Intn map base 30, picks x₆/x₇/x₈ at the
Progress map base 2, range-STOP, sortSlice), γ-image == machine heap
(nextAddr 186 both). Post scalars are norm-wrapped LITERALS
(Term/Vote/lead depths 16/15/12 over lits — they reduce closed).

Slice-0 pattern (the reset-span REUSE, instantiated): window-output
states/configs are `BcLit` literals; the crossing constructions
(`uCrossPick`/`uCrossStop`/`uCrossSort`) and the pick-key derivations
(`uρ`, `uKey1/2/3`) are REUSED from the Bf modules verbatim — the
factored composite the U3 verdict called for. The `bcW*_out` links
(kernel `rfl`) are the literals' correctness proofs and drift alarms.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

/-- The symbolic fixture: state CONCRETE 0, Vote/lead/ldT symbolic. -/
def bcSymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (uRaftVal 0 0 0 0))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def bcSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy bcSymRaft)
    else (l, .mk c.declaredTy (embedGo c.value)))

def bcS0 : SymState := { heap := bcSymHeap, nextAddr := 21 }

/-- The drained call configuration of `becomeCandidate()` (receiver
only). -/
def bcC0 : SymConfig :=
  .retV (.addr (.base ⟨0⟩))
    (.callArgsK ⟨"raft.raft.becomeCandidate"⟩ [] [] [] [] .stop)

/-! ## The crossing outputs (even indices; the crossings reduce in one
step from the `BcLit` literals) -/

def bcP2 : SymState × SymConfig := uCrossPick 5 .int bcS1 bcC1
def bcS2 : SymState := bcP2.1
def bcC2 : SymConfig := bcP2.2
def bcP4 : SymState × SymConfig := uCrossPick 6 .uint64 bcS3 bcC3
def bcS4 : SymState := bcP4.1
def bcC4 : SymConfig := bcP4.2
def bcP6 : SymState × SymConfig := uCrossPick 7 .uint64 bcS5 bcC5
def bcS6 : SymState := bcP6.1
def bcC6 : SymConfig := bcP6.2
def bcP8 : SymState × SymConfig := uCrossPick 8 .uint64 bcS7 bcC7
def bcS8 : SymState := bcP8.1
def bcC8 : SymConfig := bcP8.2
def bcP10 : SymState × SymConfig := uCrossStop bcS9 bcC9
def bcS10 : SymState := bcP10.1
def bcC10 : SymConfig := bcP10.2
def bcP12 : SymState × SymConfig := uCrossSort bcS11 bcC11
def bcS12 : SymState := bcP12.1
def bcC12 : SymConfig := bcP12.2

set_option maxRecDepth 4000000

/-! ## The window LINK theorems (full-output form; kernel-checked
against the evaluator — the literals' correctness proofs). -/

theorem bcW1_out : symEvalWindowTB bfTB 686 bcS0 bcC0 = (686, bcS1, bcC1) := by
  kernel_rfl
theorem bcW2_out : symEvalWindowTB bfTB 183 bcS2 bcC2 = (183, bcS3, bcC3) := by
  kernel_rfl
theorem bcW3_out : symEvalWindowTB bfTB 28 bcS4 bcC4 = (28, bcS5, bcC5) := by
  kernel_rfl
theorem bcW4_out : symEvalWindowTB bfTB 28 bcS6 bcC6 = (28, bcS7, bcC7) := by
  kernel_rfl
theorem bcW5_out : symEvalWindowTB bfTB 28 bcS8 bcC8 = (28, bcS9, bcC9) := by
  kernel_rfl
theorem bcW6_out : symEvalWindowTB bfTB 3 bcS10 bcC10 = (3, bcS11, bcC11) := by
  kernel_rfl
theorem bcW7_out : symEvalWindowTB bfTB 2320 bcS12 bcC12 = (2320, bcS13, bcC13) := by
  kernel_rfl

/-- The chain lands at the function's return. -/
theorem bcC13_stop : bcC13 = .next .stop := by kernel_rfl

/-! ## The transported windows (γ-level, literal endpoints). -/

theorem bcWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 686 (γS ρ σ bcS0) (γC ρ bcC0) ch
      = .ok (γC ρ bcC1, γS ρ σ bcS1, ch) :=
  symEvalWindowTB_refines bcW1_out ρ σ ch hag

theorem bcWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 183 (γS ρ σ bcS2) (γC ρ bcC2) ch
      = .ok (γC ρ bcC3, γS ρ σ bcS3, ch) :=
  symEvalWindowTB_refines bcW2_out ρ σ ch hag

theorem bcWin3 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ bcS4) (γC ρ bcC4) ch
      = .ok (γC ρ bcC5, γS ρ σ bcS5, ch) :=
  symEvalWindowTB_refines bcW3_out ρ σ ch hag

theorem bcWin4 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ bcS6) (γC ρ bcC6) ch
      = .ok (γC ρ bcC7, γS ρ σ bcS7, ch) :=
  symEvalWindowTB_refines bcW4_out ρ σ ch hag

theorem bcWin5 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ bcS8) (γC ρ bcC8) ch
      = .ok (γC ρ bcC9, γS ρ σ bcS9, ch) :=
  symEvalWindowTB_refines bcW5_out ρ σ ch hag

theorem bcWin6 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 3 (γS ρ σ bcS10) (γC ρ bcC10) ch
      = .ok (γC ρ bcC11, γS ρ σ bcS11, ch) :=
  symEvalWindowTB_refines bcW6_out ρ σ ch hag

theorem bcWin7 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 2320 (γS ρ σ bcS12) (γC ρ bcC12) ch
      = .ok (γC ρ bcC13, γS ρ σ bcS13, ch) :=
  symEvalWindowTB_refines bcW7_out ρ σ ch hag

end GoLean.RaftSeam
