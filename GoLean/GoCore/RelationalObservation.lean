import GoLean.GoCore.RelationalControl

/-!
# Body-entry and normal-return observations

The first entry contract covers the seven sequential call/defer entry sites.
It preserves supplied arguments and the pre-store; resolved identity comes
from actual body entry, not the syntactic callee. Re-dispatch is not entry.

The foundational return contract covers targetless/resultless frames. It includes
deferred-call and top-level frames: both report `[]`, independently of the
function signature. Final driver readback is separate.
`RelationalEvent` adds all normal exit descriptors; `RelationalEventSound`
proves exhaustive structural entry/exit coverage, and `RelationalHistory`
composes finite successful histories. This module supplies their foundations.

The semantic site inventory is adapted from the logic's `Call.lean` at
`f0afcbf`, with all ownership, Iris and evaluator-equation dependencies removed.
-/

namespace GoLean.GoCore.Relational

open Machine

inductive EntrySite (fid : FuncId) :
    List GoValue → Config → (List Loc → FuncId → Cont) → Prop where
  | direct {targets args plans env k} : targetsPlan targets.toList = some plans → args.toList = [] →
      EntrySite fid [] (.exec (.call targets fid args) env k) (fun roots f => .frame plans env roots [] k f)
  | arguments {done v plans env k} :
      EntrySite fid (done ++ [v]) (.retV v (.callArgsK fid plans done [] env k))
        (fun roots f => .frame plans env roots [] k f)
  | closure {caps plans env k} :
      EntrySite fid caps (.retV (.funcVal fid caps) (.callValCalleeK plans [] env k))
        (fun roots f => .frame plans env roots [] k f)
  | closureArguments {caps done v plans env k} :
      EntrySite fid (caps ++ done ++ [v])
        (.retV v (.callValArgsK (.funcVal fid caps) plans done [] env k))
        (fun roots f => .frame plans env roots [] k f)
  | deferFall {caps args plans env roots ds k w} :
      EntrySite fid (caps ++ args) (.next (.frame plans env roots ((.funcVal fid caps, args) :: ds) k w))
        (fun _ f => .frame [] [] [] [] (.frame plans env roots ds k w) f)
  | deferReturn {caps args plans env roots ds k w} :
      EntrySite fid (caps ++ args) (.signal .ret (.frame plans env roots ((.funcVal fid caps, args) :: ds) k w))
        (fun _ f => .frame [] [] [] [] (.frame plans env roots ds k w) f)
  | deferPanic {caps args plans env roots ds k w chain} :
      EntrySite fid (caps ++ args) (.panicking chain (.frame plans env roots ((.funcVal fid caps, args) :: ds) k w))
        (fun _ f => .frame [] [] [] [] (.panicResumeK chain (.frame plans env roots ds k w)) f)

theorem EntrySite.transition {ctx : ProgramCtx} {fid : FuncId} {args : List GoValue}
    {c : Config} {frame : List Loc → FuncId → Cont} (site : EntrySite fid args c frame)
    {s t : Store} {f : Func} {env : LocalEnv} {roots : List Loc} {tr : AccessTrace}
    (entry : enterFrame ctx s fid args = .ok (.run f env roots, t, tr)) :
    Transition ctx ⟨c, s⟩ ⟨tr, [], []⟩ ⟨.exec f.body env (frame roots f.id), t⟩ := by
  have he := enterFramePick_ok (ch := []) entry
  cases site with
  | direct hp ha => exact Step.callImmediate hp ha he rfl
  | arguments => exact Step.callArgsDoneEnter he rfl
  | closure => exact Step.callValCalleeEnter he rfl
  | closureArguments => exact Step.callValArgsEnter he rfl
  | deferFall => exact Step.frameDeferFall he rfl
  | deferReturn => exact Step.frameDeferReturn he rfl
  | deferPanic => exact Step.panicFrameDefer he rfl

structure EntryEvent where
  function : FuncId
  supplied : List GoValue
  before : Store

/-- A successful actual body entry, retaining its pre-store and input
payload. Receiver adjustment may bind different values inside the frame. -/
def Enters (ctx : ProgramCtx) (a b : State) (l : StepLabel) (event : EntryEvent) : Prop :=
  ∃ fid frame f env roots tr,
    EntrySite fid event.supplied a.control frame ∧
    enterFrame ctx a.store fid event.supplied = .ok (.run f env roots, b.store, tr) ∧
    b.control = .exec f.body env (frame roots f.id) ∧
    event.function = f.id ∧ event.before = a.store ∧ l = ⟨tr, [], []⟩

theorem Enters.transition {ctx : ProgramCtx} {a b : State} {l : StepLabel} {event : EntryEvent}
    (h : Enters ctx a b l event) : Transition ctx a l b := by
  obtain ⟨fid, frame, f, env, roots, tr, site, he, hc, _, _, rfl⟩ := h
  have hs := site.transition he
  change Step ctx a.control a.store b.control b.store _
  rw [hc]
  exact hs

/-- All successful successors at a witnessed entry coincide, including their
complete labels. The entry cannot have a different successful pick path. -/
theorem Enters.all_successors {ctx : ProgramCtx} {a b d : State} {l m : StepLabel}
    {event : EntryEvent} (h : Enters ctx a b l event) (hs : Transition ctx a m d) :
    b = d ∧ l = m := by
  have hp : l.picks = [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    rfl
  exact h.transition.unique_of_no_picks hp hs

/-- Normal return of a frame whose results are deliberately not delivered
to caller targets, after its deferred calls have drained. -/
def returning (fid : FuncId) (k : Continuation) (s : Store)
    (caller : LocalEnv := []) : State :=
  ⟨.signal .ret (.frame [] caller [] [] k.toMachine fid), s⟩

def falling (fid : FuncId) (k : Continuation) (s : Store)
    (caller : LocalEnv := []) : State :=
  ⟨.next (.frame [] caller [] [] k.toMachine fid), s⟩

structure ReturnEvent where
  function : FuncId
  values : List GoValue
  before : Store

inductive ReturnsDiscarded : State → State → ReturnEvent → Prop where
  | returning {fid k s caller} :
      ReturnsDiscarded (returning fid k s caller) (resumed k s) ⟨fid, [], s⟩
  | falling {fid k s caller} :
      ReturnsDiscarded (falling fid k s caller) (resumed k s) ⟨fid, [], s⟩

theorem ReturnsDiscarded.pure {ctx : ProgramCtx} {a b : State} {event : ReturnEvent}
    (h : ReturnsDiscarded a b event) : Pure ctx a b := by
  cases h
  · exact ⟨Step.frameReturn, rfl⟩
  · exact ⟨Step.frameFall, rfl⟩

end GoLean.GoCore.Relational
