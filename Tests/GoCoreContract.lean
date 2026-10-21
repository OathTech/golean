import GoLean.GoCore.Trace
import GoLean.GoCore.Multi

/-! Core contract regressions, re-homed 2026-09-16 (lane `park-lane/typed-profiles-0916`,
`docs/2026-09-16_typed-profiles-parked.md` §3) when the typed-admission profile family
and its facade `GoLean/Interface.lean` were parked.

§A — origin `Tests/InterfaceContract.lean` at main `62fc8073` (landed `a6a068ce`, chunk
L3): the proofs are byte-identical; only the imports (the deleted facade → the two core
trace modules), the namespace (`GoLean.GateA1` → `GoLean.GoCore.ContractTests`) and this
header changed. Every fact is about the CORE: `recoverResult`/`recoverAtDeferred` (G-P S2) on
frames, `stepFn` at the `probeK` choice site, `Trace`, `StateWf`, the `run_ok_iff` bridge,
`execProgLoopOut` and `runProgramPoolOutM`. §B — interpreter facts moved out of the deleted
typed test libraries. RETIREMENT (2026-10-20, lane `core/retire-relation-1020`): the facts
stated over the relation (`both_relational_successors`, `fixed_stream_not_existential_path`),
the pool traces (`print_before_panic_trace`, `both_pool_traces`) and §C, the config-level
abort observer (`AbortObservation.lean`), left the build with the relational layer (tag
`relational/last-main-2026-10-20`); the theorems named in `Tests/GoCoreAudit.lean`'s export
list are the required ones, the rest are regression facts (audit fix F2). -/

namespace GoLean.GoCore.ContractTests
open GoCore GoCore.Machine Semantics
/-- B6 (2026-09-30): a spelling interned injectively into a `VarId` (test-local). -/
def vid (s : String) : GoLean.GoCore.VarId := s.toUTF8.foldl (fun n b => n * 256 + b.toNat) 0

-- B7 (2026-09-17): the ∀-state facts take the program context implicitly;
-- the concrete runs use `exampleCtx` (the old `{ types := TypeEnv.reserved }`).
variable {ctx : ProgramCtx}

-- G-P S2 (2026-09-28): `Cont.frame`'s trailing wrapper `Bool` became the frame's callee
-- `FuncId` (the audit frame names its subject); `recoverThroughWrappers` became the direct
-- `recoverAtDeferred` (design §2 S6), so the two recover facts unfold that.
def auditFid : FuncId := ⟨"audit.subject"⟩
def bareFrame : Cont := .frame [] [] [] [] .stop auditFid
def panicFrame : Cont := .frame [] [] [] [] (.panicResumeK [panicEntry "audit"] .stop) auditFid

theorem recover_bare : recoverResult bareFrame = (.nil, bareFrame) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  rfl
def recoveredFrame : Cont := .frame [] [] [] []
  (.panicResumeK [{ panicEntry "audit" with recovered := true }] .stop) auditFid
theorem recover_handler : recoverResult panicFrame = ((panicEntry "audit").value, recoveredFrame) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  rfl
theorem recover_changes_value : (recoverResult bareFrame).1 ≠ (recoverResult panicFrame).1 := by
  intro h
  rw [recover_bare, recover_handler] at h
  cases h

theorem recover_changes_handler : (recoverResult panicFrame).2 ≠ panicFrame := by
  intro h
  rw [recover_handler] at h
  have hb := congrArg (fun k => match k with
    | .frame _ _ _ _ (.panicResumeK (e :: _) _) _ => e.recovered
    | _ => false) h
  cases hb

theorem recover_stepFn (s : Store) (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn ctx s (.evalE .recoverCall env k) ch =
      .ok (.retV (recoverResult k).1 (recoverResult k).2, s, ch, ⟨[], [], []⟩) := rfl

/-- Transporting the bare-frame recover successor under the added handler
is not a step. This refutes the concrete instance of the proposed fill law. -/
theorem recover_step_does_not_transport (s : Store) :
    Step ctx (.evalE .recoverCall [] bareFrame) s (.retV .nil bareFrame) s ⟨[], [], []⟩ ∧
    ¬ ∃ tr, Step ctx (.evalE .recoverCall [] panicFrame) s (.retV .nil panicFrame) s tr := by
  refine ⟨.evalRecover recover_bare, ?_⟩
  rintro ⟨tr, h⟩
  obtain ⟨ch, ch', he⟩ := step_complete h
  rw [recover_stepFn, recover_handler] at he
  have hc := (Prod.mk.inj (Except.ok.inj he)).1
  cases hc

def illTyped : Store := { heap := #[.value .bool (.int 7)] }
/-- Still admitted under `HeapNormal` (C1 S1): the normalizer does not coerce at a
`.bool` slot (`isNormalForTyTy`'s catch-all), so the address bound remains the only
thing `StateWf` says about this cell. -/
theorem address_bound_admits_ill_typed :
    StateWf (ProgramCtx.ofTables (types := #[])) illTyped := by decide

/-! A path write THROUGH an identity-normalized root (C1 audit fix round F3,
2026-09-18). `isNormalForTyTy (.interface _) _ = true`, so an `.interface`-declared
cell holding an ARRAY or a STRUCT is `HeapNormal`; main `68b261e6`'s leaf-first
`storeLoc` (load base → set → store root → normalize at `.interface` = identity)
ACCEPTED a path write into it, and the C1 S1 root-first write REFUSED it
(`Ty.stepDown` had no arm for the identity types) — an undisclosed refusal-class
change on a state the invariant admits, unreachable from Go as far as the audit
could construct (interface contents are not addressable). Pinned to main's
behaviour: the descent returns the identity type itself and the leaf is
normalized there (no masking — exactly what the whole-root identity did). The
`#eval`s ran first (`docs/evidence/2026-09-18_c1-memory-module/probe-IfaceCell.log`). -/
def ifaceArrayStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.array #[.int 0 .int, .int 1 .int])] }
def ifaceStructStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.struct ⟨"main.A"⟩ #[("f", .int 0 .int)])] }
def sliceArrayStore : Store :=
  { heap := #[.value (.slice .int) (.array #[.int 0 .int, .int 1 .int])] }
def leaf0 : Loc := .index (.base ⟨0⟩) 0
def leafF : Loc := .field (.base ⟨0⟩) ⟨"main.A"⟩ "f"

theorem iface_cell_path_write_normal :
    HeapNormal (ProgramCtx.ofTables (types := #[])) ifaceArrayStore ∧
    HeapNormal (ProgramCtx.ofTables (types := #[])) ifaceStructStore ∧
    HeapNormal (ProgramCtx.ofTables (types := #[])) sliceArrayStore := by decide

theorem iface_cell_path_write_array :
    (storeLoc (ProgramCtx.ofTables (types := #[])) ifaceArrayStore leaf0 (.int 5 .int)).map
        (fun s => loadLoc (ProgramCtx.ofTables (types := #[])) s leaf0)
      = .ok (.ok (.int 5 .int)) := rfl

theorem iface_cell_path_write_struct :
    (storeLoc (ProgramCtx.ofTables (types := #[])) ifaceStructStore leafF (.int 5 .int)).map
        (fun s => loadLoc (ProgramCtx.ofTables (types := #[])) s leafF)
      = .ok (.ok (.int 5 .int)) := rfl

theorem slice_cell_path_write_array :
    (storeLoc (ProgramCtx.ofTables (types := #[])) sliceArrayStore leaf0 (.int 5 .int)).map
        (fun s => loadLoc (ProgramCtx.ofTables (types := #[])) s leaf0)
      = .ok (.ok (.int 5 .int)) := rfl

/-- The written store is still `HeapNormal` (the identity arm of the check). -/
theorem iface_cell_path_write_preserves_normal :
    (storeLoc (ProgramCtx.ofTables (types := #[])) ifaceArrayStore leaf0 (.int 5 .int)).map
        (fun s => decide (HeapNormal (ProgramCtx.ofTables (types := #[])) s))
      = .ok true := rfl

/-- An actual choice site of the current machine, not a toy transition system. -/
def forkPoint : Config := .panicking [panicEntry "audit"] (.probeK .stop)
def raised : Config := .panicking [panicEntry "audit"] .stop

theorem choose_defer (s : Store) (tail : Choices) :
    stepFn ctx s forkPoint (0 :: tail) = .ok (.next .stop, s, tail, ⟨[], [⟨.unseqPanic, 2, 0⟩], []⟩) := rfl
theorem choose_raise (s : Store) (tail : Choices) :
    stepFn ctx s forkPoint (1 :: tail) = .ok (raised, s, tail, ⟨[], [⟨.unseqPanic, 2, 1⟩], []⟩) := rfl

theorem defer_trace (s : Store) (tail : Choices) :
    Trace ctx 1 s forkPoint (0 :: tail) s (.next .stop) tail :=
  .step (choose_defer s tail) .done
theorem raise_trace (s : Store) (tail : Choices) :
    Trace ctx 1 s forkPoint (1 :: tail) s raised tail :=
  .step (choose_raise s tail) .done

end GoLean.GoCore.ContractTests

namespace GoLean.GoCore.ContractTests
open GoCore GoCore.Machine Semantics

-- B7 (2026-09-17): the ∀-state facts take the program context implicitly;
-- the concrete runs use `exampleCtx` (the old `{ types := TypeEnv.reserved }`).
variable {ctx : ProgramCtx}

/-- B7: the old `{ types := TypeEnv.reserved }` state, as the run's context plus an
empty store. -/
def exampleCtx : ProgramCtx := ProgramCtx.ofTables (types := TypeEnv.reserved)
def exampleState : Store := {}
def choicePool : MultiConfig := ⟨#[Thread.running forkPoint none], exampleState, 0⟩

/-- Hand-authored GoCore; no claim of a certified Go frontend translation. -/
def printPanicProgram : Program := { funcs := #[{
  id := ⟨"main.audit"⟩, args := #[], results := #[],
  body := .seqn #[.print true #[.stringLit (GoString.fromLeanString "before")],
    .panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) .string
      (.stringLit (GoString.fromLeanString "boom")))] }] }

def recoverBranch (k : Cont) : Cont :=
  .ifK (.seqn #[]) (.unsupported "recovery did not happen") [] k
def recoverCompare (k : Cont) : Cont :=
  .strictK (.neqCmp (.interface ⟨"empty_interface"⟩)) [.nil] [] [] (recoverBranch k)
def recoverCheck : Config := .evalE .recoverCall [] (recoverCompare panicFrame)

/-- An injective readout for panic results, to make kernel computation
avoid equality instances for unrelated successful result values. -/
def panicObservation : RunResult → Option (String × Array UInt8)
  | .error (.terminal (.panic msg), out) => some (msg, out.bytes)
  | _ => none

theorem panicObservation_sound {r : RunResult} {msg : String} {bytes : Array UInt8}
    (h : panicObservation r = some (msg, bytes)) :
    r = .error (.panic msg, ⟨bytes⟩) := by
  cases r with
  | ok v => cases h
  | error e =>
    obtain ⟨stop, ⟨out⟩⟩ := e
    cases stop with
    | refusal e => cases h
    | fuelOut => cases h
    | terminal t => cases t with
      | panic m =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rfl
      | fatal m => cases h
      | deadlock => cases h
      | raceDetected => cases h

set_option maxRecDepth 4096 in
/-- Full entry, actual print event, abort, and the retained byte prefix. -/
theorem print_before_panic :
    runProgramPoolOutM 20 printPanicProgram "main.audit" #[] [] =
      .error (.panic "boom", GoString.fromLeanString "before\n") := by
  apply panicObservation_sound
  decide +kernel

/-- Terminal checking precedes exhaustion. One step suffices for DEFER. -/
theorem defer_completes (s : Store) (tail : Choices) :
    execStmtLoop ctx 1 s forkPoint (0 :: tail) = .ok (s, tail) :=
  run_ok_iff.mpr ⟨1, Nat.le_refl _, defer_trace s tail⟩

theorem raise_needs_abort_fuel (s : Store) (tail : Choices) :
    execStmtLoop ctx 1 s forkPoint (1 :: tail) = .error .fuelOut := by
  rw [execStmtLoop_step (choose_raise s tail)]
  rfl

theorem raise_aborts :
    execStmtLoop exampleCtx 2 exampleState forkPoint [1] = .error (.panic "audit") := by
  rw [execStmtLoop_step (choose_raise exampleState [])]
  with_unfolding_all rfl

/-- Both directions of the corrected bridge at the actual choice site. -/
theorem defer_run_iff :
    execStmtLoop exampleCtx 1 exampleState forkPoint [0] = .ok (exampleState, []) ↔
      ∃ n, n ≤ 1 ∧ Trace exampleCtx n exampleState forkPoint [0] exampleState (.next .stop) [] :=
  run_ok_iff

theorem pool_defer (acc : GoString) :
    execProgLoopOut exampleCtx 2 choicePool {} [0] acc = (acc, .ok (exampleState, [])) := by
  with_unfolding_all rfl

theorem pool_raise (acc : GoString) :
    execProgLoopOut exampleCtx 2 choicePool {} [1] acc = (acc, .error (.panic "audit")) := by
  with_unfolding_all rfl

theorem two_choice_pool_bridge (acc : GoString) :
    (∃ ch, execProgLoopOut exampleCtx 2 choicePool {} ch acc = (acc, .error (.panic "audit"))) ∧
    execProgLoopOut exampleCtx 2 choicePool {} [0] acc ≠ (acc, .error (.panic "audit")) := by
  refine ⟨⟨[1], pool_raise acc⟩, ?_⟩
  rw [pool_defer]
  intro h
  cases (Prod.mk.inj h).2


end GoLean.GoCore.ContractTests

/-! ## B. Interpreter facts re-homed from the typed-profile test libraries
Statements and proofs are unchanged; the surrounding profile material (admission checkers,
typed invariants, `programState`) stayed with the family. Origins are files at main
`62fc8073` (landed `f70ea4bf`, chunk L1). -/
namespace GoLean.GoCore.ContractTests.Interpreter
open Machine

-- The origins' elaboration options (`Tests/RecoveryInvariant.lean`, `Tests/BooleanProgram.lean`).
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Origin `Tests/BooleanProgram.lean` (`terminal_at_zero_fuel`): the pool driver retains an
existing byte prefix, including NUL and SOH, and the entire choice tape when classifying an
already normal terminal. -/
theorem terminal_at_zero_fuel (ch : Choices) :
    execProgLoopOut emptyCtx 0 ⟨#[.running (.next .stop) none], {}, 0⟩ {} ch
      ⟨#[0, 1, 10, 13]⟩ = (⟨#[0, 1, 10, 13]⟩, .ok ({}, ch)) := by rfl

/-- Origin `Tests/BooleanRuntime.lean` (`duplicate_readout_preserves_alias`). -/
theorem duplicate_readout_preserves_alias (b : Bool) :
    loadMany emptyCtx { heap := #[.value .bool (.bool b)] } [.base ⟨0⟩, .base ⟨0⟩] =
      .ok [.bool b, .bool b] := by rfl

-- Origin `Tests/BooleanInvariant.lean` (`actual_scope_restoration`, `actual_new_local_zero`).
def barrier : Cont := .frame [] [] [] [] .stop auditFid
/-- B7: the old `({} : ExecState)` — an empty context beside the empty store. -/
def emptyCtx : ProgramCtx := ProgramCtx.ofTables (types := #[])
def fresh : Store := {}
def scopeEnv : LocalEnv := [[(vid "result", .base ⟨0⟩), (vid "x", .base ⟨1⟩)]]
def scopeState (b : Bool) : Store :=
  {fresh with heap := #[.value .bool (.bool false), .value .bool (.bool b)]}
def scopeBody : Stmt := .seqn #[
  .block #[⟨vid "x", .bool⟩] #[.assign (.var (vid "x")) (.not (.var (vid "x")))],
  .assign (.var (vid "result")) (.var (vid "x")), .returnStmt]

/-- The inner zero-initialized shadow is changed to true; after its block,
the read resolves the outer input. Both inputs distinguish different errors. -/
theorem actual_scope_restoration (b : Bool) :
    (do let (s, _) ← runConfig emptyCtx 40 (scopeState b) (.exec scopeBody scopeEnv barrier) []
        loadMany emptyCtx s [.base ⟨0⟩]) = .ok [.bool b] := by
  cases b <;> with_unfolding_all rfl

-- C4 (2026-10-01): the declaration is the block's entry allocation (was `.initialization`).
def zeroBody : Stmt := .block #[⟨vid "zero", .bool⟩] #[
  .assign (.var (vid "result")) (.var (vid "zero")), .returnStmt]

theorem actual_new_local_zero (b : Bool) :
    (do let (s, _) ← runConfig emptyCtx 30 (scopeState b) (.exec zeroBody scopeEnv barrier) []
        loadMany emptyCtx s [.base ⟨0⟩]) = .ok [.bool false] := by
  cases b <;> with_unfolding_all rfl

-- Origin `Tests/RecoveryInvariant.lean` (`registration_is_lifo`,
-- `equal_repanic_keeps_history`, `scope_and_zero_execution`).
/-- Registration prepends each fully evaluated call; it does not run or
copy its captured pointees. This equation holds for arbitrary closures. -/
theorem registration_is_lifo (first second : GoValue × List GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv) (roots : List Loc)
    (ds : List (GoValue × List GoValue)) (k : Cont) (fid : FuncId) :
    pushDefer first (.frame plans env roots ds k fid) =
      some (.frame plans env roots (first :: ds) k fid) ∧
    pushDefer second (.frame plans env roots (first :: ds) k fid) =
      some (.frame plans env roots (second :: first :: ds) k fid) := by
  constructor <;> unfold pushDefer <;> rw [Cont.rebuild_act (by rfl)] <;> rfl

/-- Equal re-panic payloads are distinct chain entries. Recovery marks the
newest entry while retaining the older recovered history, for any bytes. -/
theorem equal_repanic_keeps_history (bytes : GoString) :
    markNewestRecovered [{ value := .interface .string (.string bytes), recovered := true },
      { value := .interface .string (.string bytes), recovered := false }] =
      some (.interface .string (.string bytes),
        [{ value := .interface .string (.string bytes), recovered := true },
          { value := .interface .string (.string bytes), recovered := true }]) := rfl

def scopedFunction : Func := {
  id := ⟨"scoped"⟩, args := #[⟨vid "x", .bool⟩], results := #[⟨vid "result", .bool⟩]
  -- C4 (2026-10-01): `payload` is the outer block's declaration (was an `.initialization`
  -- mid-sequence), allocated at the block's entry; its initializer stays where it was.
  body := .block #[⟨vid "zero", .bool⟩, ⟨vid "payload", .interface ⟨"any"⟩⟩] #[
    .block #[⟨vid "x", .interface ⟨"any"⟩⟩] #[
      .assign (.var (vid "x")) (.toInterface (.interface ⟨"any"⟩) .string
        (.stringLit (.fromLeanString "shadow")))],
    .seqn #[],
    .assign (.var (vid "payload")) (.nil none),
    .assign (.var (vid "result")) (.and (.var (vid "x")) (.not (.var (vid "zero")))), .returnStmt]
}
def scopedProgram : Program := { typeDefs := TypeEnv.reserved, funcs := #[scopedFunction] }

/-- The actual interpreter restores the Boolean outer x after a payload
shadow, sees the same-scope sequence declaration, and zero-initializes zero. -/
theorem scope_and_zero_execution (b : Bool) :
    runProgramM 60 scopedProgram "scoped" #[.bool b] [] = .ok { values := #[.bool b] } := by
  cases b <;> with_unfolding_all rfl

-- Origin `Tests/RecoveryStorage.lean` (`write_keeps_both_actual_aliases`).
def aliasState (b : Bool) : Store := { heap := #[
  .value .bool (.bool b),
  .value (.pointer .bool) (.addr (.base ⟨0⟩)),
  .value (.pointer .bool) (.addr (.base ⟨0⟩))] }

/-- Both stored captures keep the original shared target while its value
changes; the machine does not copy the pointee at capture or at store. -/
theorem write_keeps_both_actual_aliases (before after : Bool) :
    storeLoc emptyCtx (aliasState before) (.base ⟨0⟩) (.bool after) = .ok (aliasState after) ∧
    loadMany emptyCtx (aliasState after) [.base ⟨1⟩, .base ⟨2⟩] =
      .ok [.addr (.base ⟨0⟩), .addr (.base ⟨0⟩)] ∧
    loadLoc emptyCtx (aliasState after) (.base ⟨0⟩) = .ok (.bool after) := by
  constructor
  · with_unfolding_all rfl
  constructor <;> with_unfolding_all rfl

end GoLean.GoCore.ContractTests.Interpreter
