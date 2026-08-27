import GoLeanProofs.Specs.RaftPilot.Reloc
import GoLeanProofs.Specs.RaftPilot.CBfLit

/-!
# W2 unit 4: the COMPLIANT-layout becomeFollower fixture (the re-laid
pilot — W1 unit-6 proposal, executed)

The compliant chain: globals region `[0,31)` reserved (the one
touched true static, `raft.globalRand ⟨18⟩`, at its true address);
fixture cells from `⟨31⟩` (raft cell at `⟨31⟩`, nextAddr 52). The
ground literals live in the GENERATED `CBfLit.lean`, emitted by the
tracked `tools/relayout/CBfLitGen.lean` as the `Reloc` image of the
tracked W1 literals (provenance chain in both files). The window LINK
theorems below re-run the evaluator over the compliant chain (kernel
`rfl`, open caller context) — NOTHING is assumed from the
generation: these links are the literals' correctness proofs, exactly
as `BfFixture`'s links are the original's. (A first attempt defined
the compliant chain as `relocS`/`relocC` APPLICATIONS instead of
ground literals; the kernel re-reduced the relocation inside every
window check and blew past 10 minutes — ground literals restore the
original 88 s-class wall. Recorded so nobody re-simplifies the
generator away.)

Scaffolding status: PRIVATE proof-body content (the W1 convention —
count-bearing, fixture-anchored; consumed only by the compliant
`CallSpec`'s proof and the W2 gate). Retirement per BfLit.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

/-- The drained call configuration at the compliant receiver —
caller env and continuation OPEN. -/
def cC0 (tenv : LocalEnv) (k : SymCont) : SymConfig :=
  .retV (.int (.var 9) .uint64)
    (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
      [.addr (.base ⟨31⟩), .int (.lit 0) .uint64] [] tenv k)

/-! ## The crossing outputs (even indices) — the same crossing
constructions, applied to the compliant chain. -/

def cP2 (tenv : LocalEnv) (k : SymCont) : SymState × SymConfig :=
  uCrossPick 5 .int cS1 (cC1 tenv k)
def cS2 : SymState := (cP2 [] .stop).1
def cC2 (tenv : LocalEnv) (k : SymCont) : SymConfig := (cP2 tenv k).2
def cP4 (tenv : LocalEnv) (k : SymCont) : SymState × SymConfig :=
  uCrossPick 6 .uint64 cS3 (cC3 tenv k)
def cS4 : SymState := (cP4 [] .stop).1
def cC4 (tenv : LocalEnv) (k : SymCont) : SymConfig := (cP4 tenv k).2
def cP6 (tenv : LocalEnv) (k : SymCont) : SymState × SymConfig :=
  uCrossPick 7 .uint64 cS5 (cC5 tenv k)
def cS6 : SymState := (cP6 [] .stop).1
def cC6 (tenv : LocalEnv) (k : SymCont) : SymConfig := (cP6 tenv k).2
def cP8 (tenv : LocalEnv) (k : SymCont) : SymState × SymConfig :=
  uCrossPick 8 .uint64 cS7 (cC7 tenv k)
def cS8 : SymState := (cP8 [] .stop).1
def cC8 (tenv : LocalEnv) (k : SymCont) : SymConfig := (cP8 tenv k).2
def cP10 (tenv : LocalEnv) (k : SymCont) : SymState × SymConfig :=
  uCrossStop cS9 (cC9 tenv k)
def cS10 : SymState := (cP10 [] .stop).1
def cC10 (tenv : LocalEnv) (k : SymCont) : SymConfig := (cP10 tenv k).2
def cP12 (tenv : LocalEnv) (k : SymCont) : SymState × SymConfig :=
  uCrossSort cS11 (cC11 tenv k)
def cS12 : SymState := (cP12 [] .stop).1
def cC12 (tenv : LocalEnv) (k : SymCont) : SymConfig := (cP12 tenv k).2

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The window LINK theorems at the compliant layout (kernel `rfl`
against the evaluator — the relocated chain's correctness proofs). -/

theorem cW1_out (tenv : LocalEnv) (k : SymCont) :
    symEvalWindowTB bfTB 642 cS0 (cC0 tenv k) = (642, cS1, cC1 tenv k) := by
  kernel_rfl
theorem cW2_out (tenv : LocalEnv) (k : SymCont) :
    symEvalWindowTB bfTB 183 cS2 (cC2 tenv k) = (183, cS3, cC3 tenv k) := by
  kernel_rfl
theorem cW3_out (tenv : LocalEnv) (k : SymCont) :
    symEvalWindowTB bfTB 28 cS4 (cC4 tenv k) = (28, cS5, cC5 tenv k) := by
  kernel_rfl
theorem cW4_out (tenv : LocalEnv) (k : SymCont) :
    symEvalWindowTB bfTB 28 cS6 (cC6 tenv k) = (28, cS7, cC7 tenv k) := by
  kernel_rfl
theorem cW5_out (tenv : LocalEnv) (k : SymCont) :
    symEvalWindowTB bfTB 28 cS8 (cC8 tenv k) = (28, cS9, cC9 tenv k) := by
  kernel_rfl
theorem cW6_out (tenv : LocalEnv) (k : SymCont) :
    symEvalWindowTB bfTB 3 cS10 (cC10 tenv k) = (3, cS11, cC11 tenv k) := by
  kernel_rfl
theorem cW7_out (tenv : LocalEnv) (k : SymCont) :
    symEvalWindowTB bfTB 2316 cS12 (cC12 tenv k)
      = (2316, cS13, cC13 tenv k) := by
  kernel_rfl

/-- The compliant chain lands at `.next k`. -/
theorem cC13_next (tenv : LocalEnv) (k : SymCont) :
    cC13 tenv k = .next k := by
  kernel_rfl

/-! ## The transported windows (γ-level). -/

theorem cWin1 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (ch : Choices) (hag : bfTB.Agrees σ) :
    stepFnIter 642 (γS ρ σ cS0) (γC ρ (cC0 tenv k)) ch
      = .ok (γC ρ (cC1 tenv k), γS ρ σ cS1, ch) :=
  symEvalWindowTB_refines (cW1_out tenv k) ρ σ ch hag

theorem cWin2 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (ch : Choices) (hag : bfTB.Agrees σ) :
    stepFnIter 183 (γS ρ σ cS2) (γC ρ (cC2 tenv k)) ch
      = .ok (γC ρ (cC3 tenv k), γS ρ σ cS3, ch) :=
  symEvalWindowTB_refines (cW2_out tenv k) ρ σ ch hag

theorem cWin3 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (ch : Choices) (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ cS4) (γC ρ (cC4 tenv k)) ch
      = .ok (γC ρ (cC5 tenv k), γS ρ σ cS5, ch) :=
  symEvalWindowTB_refines (cW3_out tenv k) ρ σ ch hag

theorem cWin4 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (ch : Choices) (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ cS6) (γC ρ (cC6 tenv k)) ch
      = .ok (γC ρ (cC7 tenv k), γS ρ σ cS7, ch) :=
  symEvalWindowTB_refines (cW4_out tenv k) ρ σ ch hag

theorem cWin5 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (ch : Choices) (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ cS8) (γC ρ (cC8 tenv k)) ch
      = .ok (γC ρ (cC9 tenv k), γS ρ σ cS9, ch) :=
  symEvalWindowTB_refines (cW5_out tenv k) ρ σ ch hag

theorem cWin6 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (ch : Choices) (hag : bfTB.Agrees σ) :
    stepFnIter 3 (γS ρ σ cS10) (γC ρ (cC10 tenv k)) ch
      = .ok (γC ρ (cC11 tenv k), γS ρ σ cS11, ch) :=
  symEvalWindowTB_refines (cW6_out tenv k) ρ σ ch hag

theorem cWin7 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (ch : Choices) (hag : bfTB.Agrees σ) :
    stepFnIter 2316 (γS ρ σ cS12) (γC ρ (cC12 tenv k)) ch
      = .ok (γC ρ (cC13 tenv k), γS ρ σ cS13, ch) :=
  symEvalWindowTB_refines (cW7_out tenv k) ρ σ ch hag

end GoLean.RaftSeam
