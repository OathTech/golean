import GoLeanIris.SharedRecovery

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryRuntime
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

def flipDefer (root : Nat) : GoValue × List GoValue :=
  (.funcVal ⟨"Shared$lit0"⟩ [.addr (.base ⟨root⟩)], [])

def recoverDefer (root : Nat) : GoValue × List GoValue :=
  (.funcVal ⟨"Shared$lit1"⟩ [.addr (.base ⟨root⟩)], [])

def sharedFrame (ds : List (GoValue × List GoValue)) : Cont :=
  .frame [] [] [] ds .stop false

theorem wp_shared_last_handler {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = sharedState heap) (root : Nat) (b : Bool) :
    (root ↦ (.value .bool (.bool b))) ⊢
    WP (Config.next (sharedFrame [flipDefer root])) @ Stuckness.NotStuck; ⊤
      {{ _v, root ↦ (.value .bool (.bool (!b))) }} := by
  have values : ParamsValues (Array.replicate (root + 1) .boolean)
      sharedProgram.funcs[2].args.toList [.addr (.base ⟨root⟩)] :=
    .cons ⟨.root, .root, .root (by simp)⟩ .nil
  iintro Hroot
  simp only [sharedFrame, flipDefer]
  iapply wp_call (fid := ⟨"Shared$lit0"⟩) (f := sharedProgram.funcs[2]) (zeros := [])
    shared_typed (by rw [hctx]; rfl) (by rfl) values .nil
    (.deferFall (caps := [.addr (.base ⟨root⟩)]) (args := []))
  inext
  iintro %capture
  rw [show callCells sharedProgram.funcs[2] [.addr (.base ⟨root⟩)] [] =
    [.value (.pointer .bool) (.addr (.base ⟨root⟩))] from rfl]
  simp only [ownsCells]
  iintro ⟨Hcapture, _⟩
  rw [show callEnv sharedProgram.funcs[2] capture = [[("result$cap", .base ⟨capture⟩)]] from rfl]
  simp only [show sharedProgram.funcs[2].wrapper = false from rfl]
  iapply wp_shared_flip_handler hctx b
  isplitl [Hcapture]
  · iexact Hcapture
  isplitl [Hroot]
  · iexact Hroot
  iintro ⟨_, Hroot⟩
  iapply wp_frame_empty .fall
  inext
  iapply wp_value' (v := ())
  iexact Hroot

def drainConfig (active : Bool) (root : Nat) (bytes : GoString) : Config :=
  if active then
    .panicking [⟨.interface .string (.string bytes), false⟩]
      (sharedFrame [recoverDefer root, flipDefer root])
  else .signal .ret (sharedFrame [recoverDefer root, flipDefer root])

def drainTail (active recovered : Bool) (root : Nat) (bytes : GoString) : Cont :=
  if active then
    .panicResumeK [⟨.interface .string (.string bytes), recovered⟩] (sharedFrame [flipDefer root])
  else sharedFrame [flipDefer root]

theorem drain_frame_recovery (active : Bool) (root : Nat) (bytes : GoString) :
    FrameRecovery (drainTail active false root bytes) (recoveredValue active bytes)
      (drainTail active true root bytes) := by
  cases active with
  | false =>
    right
    refine ⟨?_, rfl, rfl⟩
    unfold drainTail sharedFrame recoverThroughWrappers
    rw [Cont.rebuild_act (by rfl)]
    rfl
  | true =>
    left
    unfold drainTail recoverThroughWrappers
    rw [Cont.rebuild_act (by rfl)]
    rfl

/-- Both registered closures retain the same semantic root address. The
single root resource passes through the effective recovery handler and then
the flip handler; the result therefore depends on LIFO order. -/
theorem wp_shared_drain {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = sharedState heap) (root : Nat) (b active : Bool)
    (bytes : GoString) :
    (root ↦ (.value .bool (.bool b))) ⊢
    WP (drainConfig active root bytes) @ Stuckness.NotStuck; ⊤
      {{ _v, root ↦ (.value .bool (.bool (!(if active then true else b)))) }} := by
  have values : ParamsValues (Array.replicate (root + 1) .boolean)
      sharedProgram.funcs[3].args.toList [.addr (.base ⟨root⟩)] :=
    .cons ⟨.root, .root, .root (by simp)⟩ .nil
  have site : CallSite ⟨"Shared$lit1"⟩ [.addr (.base ⟨root⟩)]
      (drainConfig active root bytes)
      (fun _ w => .frame [] [] [] [] (drainTail active false root bytes) w) := by
    cases active
    · exact .deferReturn (caps := [.addr (.base ⟨root⟩)]) (args := [])
    · exact .deferPanic (caps := [.addr (.base ⟨root⟩)]) (args := [])
  iintro Hroot
  iapply wp_call (fid := ⟨"Shared$lit1"⟩) (f := sharedProgram.funcs[3]) (zeros := [])
    shared_typed (by rw [hctx]; rfl) (by rfl) values .nil site
  inext
  iintro %capture
  rw [show callCells sharedProgram.funcs[3] [.addr (.base ⟨root⟩)] [] =
    [.value (.pointer .bool) (.addr (.base ⟨root⟩))] from rfl]
  simp only [ownsCells]
  iintro ⟨Hcapture, _⟩
  rw [show callEnv sharedProgram.funcs[3] capture = [[("result$cap", .base ⟨capture⟩)]] from rfl]
  simp only [show sharedProgram.funcs[3].wrapper = false from rfl]
  iapply wp_shared_recover_handler hctx b active bytes (drain_frame_recovery active root bytes)
  isplitl [Hcapture]
  · iexact Hcapture
  isplitl [Hroot]
  · iexact Hroot
  iintro ⟨_, Hroot⟩
  cases active with
  | false =>
    simp only [drainTail, Bool.false_eq_true, ↓reduceIte]
    iapply wp_shared_last_handler hctx root b $$ Hroot
  | true =>
    simp only [drainTail, ↓reduceIte]
    iapply wp_resume_recovered (by rfl)
    inext
    iapply wp_shared_last_handler hctx root true $$ Hroot

end GoLean.IrisCustomer
