import GoLeanProofs.Frame.Plug
import GoLeanProofs.Sym.KernelRfl

/-! W2 probe (2026-08-27), TRACKED IN-BUILD so the finding is
re-checked every build (the W1 open-tail convention; working copy
`artifacts/w2/ProbePlug.lean`): the plug rule's barrier recognition,
concretely, BEFORE the general walk (design note §7 probe plan).

Question: does `plugC env' k'` commute with the machine step-for-step
on successful resultless call spans — at open `env'/k'` — including
through defer registration, nested frames, and a recover-on-the-
panic-path drain? Three probes:
- P1: simple callee (assign + return), simple site.
- P2: callee with a defer AND a nested call (frames above the
  barrier; pushDefer walk), consumed under a DEEP concrete caller
  context (seq/labelK glue over the caller's own frame over .stop —
  the driver shape, including a second frame-over-.stop BELOW the
  plug point).
- P3: callee that panics and RECOVERS in a deferred function
  (panicResumeK + recoverResult exercising the walk that stops at
  the deferred fn's non-wrapper frame — never below the barrier).

Method: #eval-first (find span lengths, check outcomes), then `rfl`
examples: (a) end-to-end — the plugged run lands `.next k'` at the
same fuel/state/stream; (b) mid-span commutation at chosen i —
`stepFnIter i (plugged) = (stepFnIter i (canonical)).map (plugC)`,
with env'/k' OPEN. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface GoLean.Frame

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

namespace PlugProbe

def gFunc : Func :=
  { id := ⟨"p.g"⟩, args := #[⟨"y", .int .int⟩], results := #[],
    body := .seqn #[.assign (.var "y") (.intLit 9 .int), .returnStmt] }

def hFunc : Func :=
  { id := ⟨"p.h"⟩, args := #[⟨"z", .int .int⟩], results := #[],
    body := .seqn #[.assign (.var "z") .recoverCall, .returnStmt] }

def fFunc : Func :=
  { id := ⟨"p.f"⟩, args := #[⟨"x", .int .int⟩], results := #[],
    body := .seqn #[
      .deferCall (.funcVal ⟨"p.g"⟩ #[]) #[.intLit 1 .int],
      .call #[] ⟨"p.g"⟩ #[.intLit 3 .int],
      .assign (.var "x") (.intLit 7 .int),
      .returnStmt] }

def pFunc : Func :=
  { id := ⟨"p.p"⟩, args := #[⟨"x", .int .int⟩], results := #[],
    body := .seqn #[
      .deferCall (.funcVal ⟨"p.h"⟩ #[]) #[.intLit 0 .int],
      .panicStmt (.intLit 42 .int),
      .returnStmt] }

def σ0 : ExecState := { functions := #[gFunc, hFunc, fFunc, pFunc] }

/-- The drained-call configuration at caller context (env', k'). -/
def callCfg (fid : FuncId) (env' : LocalEnv) (k' : Cont) : Config :=
  .retV (.int 5 .int) (.callArgsK fid [] [] [] env' k')

def isDoneStop : Except GoError (Config × ExecState × Choices) → Bool
  | .ok (.next .stop, _, _) => true
  | _ => false

-- The span lengths (#eval-found in the working copy: f = 54, p = 30),
-- build-enforced here.
example : isDoneStop (stepFnIter 54 σ0 (callCfg ⟨"p.f"⟩ [] .stop) []) = true := by kernel_rfl
example : isDoneStop (stepFnIter 30 σ0 (callCfg ⟨"p.p"⟩ [] .stop) []) = true := by kernel_rfl

/-- The commutation claim at step `i`, env'/k' OPEN: the plugged run's
prefix is the `plugC`-image of the canonical prefix (state and stream
verbatim). -/
def commutesAt (fid : FuncId) (i : Nat) : Prop :=
  ∀ (env' : LocalEnv) (k' : Cont),
    stepFnIter i σ0 (callCfg fid env' k') []
      = (stepFnIter i σ0 (callCfg fid [] .stop) []).map
          (fun r => (plugC env' k' r.1, r.2.1, r.2.2))

-- P1/P2 (the f span: defer registration at step ~5, nested g frame
-- mid-span, defer drain + exit at the tail): end-to-end at 54 and
-- mid-span commutation at a spread of prefixes.
example : commutesAt ⟨"p.f"⟩ 1 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.f"⟩ 3 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.f"⟩ 8 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.f"⟩ 15 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.f"⟩ 25 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.f"⟩ 40 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.f"⟩ 53 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.f"⟩ 54 := by intro _ _; kernel_rfl  -- the exit: .next k'

-- P3 (the panic-recover span: panicArgK, panic drain, h's frame on
-- the panicResumeK marker, recoverResult stopping at h's non-wrapper
-- frame, recovered resume, frame exit).
example : commutesAt ⟨"p.p"⟩ 1 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.p"⟩ 5 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.p"⟩ 10 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.p"⟩ 20 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.p"⟩ 29 := by intro _ _; kernel_rfl
example : commutesAt ⟨"p.p"⟩ 30 := by intro _ _; kernel_rfl  -- the exit

-- P2's deep-context composition: a CONCRETE driver-shaped caller
-- context (glue + labelK + the caller's own frame over .stop — a
-- second frame-over-.stop strictly BELOW the plug point), with a
-- caller local at cell 90 the continuation then writes. The plugged
-- span must exit into k'₂ and the CALLER's continuation then run.
def σ90 : ExecState :=
  { functions := #[gFunc, hFunc, fFunc, pFunc],
    heap := [(.base ⟨90⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 91 }

def env2 : LocalEnv := [[("w", .base ⟨90⟩)]]

def k2 : Cont :=
  .seq [.assign (.var "w") (.intLit 1 .int)] env2
    (.labelK "L" (.frame [] [] [] [] .stop false))

-- The composed length (#eval-found: 66) and the caller's write
-- LANDING after the plugged span (cell 90 = 1), build-enforced.
example : isDoneStop (stepFnIter 66 σ90 (callCfg ⟨"p.f"⟩ env2 k2) []) = true := by
  kernel_rfl
example :
    (match stepFnIter 66 σ90 (callCfg ⟨"p.f"⟩ env2 k2) [] with
      | .ok (_, σf, _) => Heap.lookup σf.heap (.base ⟨90⟩)
      | _ => none)
    = some ⟨some (.int .int), .int 1 .int⟩ := by
  kernel_rfl

end PlugProbe
