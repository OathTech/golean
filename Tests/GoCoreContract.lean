import GoLean.GoCore.EnumDedupSound
import GoLean.GoCore.Trace
import GoLean.GoCore.Multi
import GoLean.GoCore.InitDriverFacts
import GoLean.GoCore.TableMonotonicity

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
stated over the relation (`recover_step_does_not_transport`, `both_relational_successors`,
`fixed_stream_not_existential_path`),
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

def illTyped : Store := { heap := #[.value .bool (.int 7)] }
/-- REFUSED by `HeapNormal` since G21 (raft-proofs' ask of 2026-10-26, landed 2026-10-27):
`isNormalForTyTy` at `.bool` admits only a `.bool` value — the arm was the catch-all
`| _, _ => true`, and the pin that stood here (`address_bound_admits_ill_typed`, C1 S1)
asserted the WEAKNESS: this store was `StateWf` because the address bound was the only
thing the invariant said about a `.bool` cell. Inverted, same store: a cell holding a
value no typed run stores is not well-formed. -/
theorem ill_typed_cell_refused :
    ¬ StateWf (ProgramCtx.ofTables (types := #[])) illTyped := by decide

/-! An INTERFACE-declared cell holds the nil interface or a box (raft-proofs' G23, 2026-11-10).
History of this pin: until G23 `isNormalForTyTy (.interface _) _ = true`, so an
`.interface`-declared cell holding an ARRAY or a STRUCT was `HeapNormal` and a path write into
it was accepted (C1 audit fix round F3, 2026-09-18: `Ty.stepDown`'s identity arm, pinned as
`iface_cell_path_write_normal` / `_array` / `_struct` / `_preserves_normal`). The arm is closed:
those two stores are not `HeapNormal`, and on them the leaf normalization at the descended type
(`.interface`, the identity arm kept) refuses by name (`stuck`, «expected interface value») —
the same inversion G21 made at `.slice`. -/
def ifaceArrayStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.array #[.int 0 .int, .int 1 .int])] }
def ifaceStructStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.struct ⟨"main.A"⟩ #[("f", .int 0 .int)])] }
def sliceArrayStore : Store :=
  { heap := #[.value (.slice .int) (.array #[.int 0 .int, .int 1 .int])] }
def leaf0 : Loc := .index (.base ⟨0⟩) 0
def leafF : Loc := .field (.base ⟨0⟩) ⟨"main.A"⟩ "f"

theorem iface_cell_not_normal :
    ¬ HeapNormal (ProgramCtx.ofTables (types := #[])) ifaceArrayStore ∧
    ¬ HeapNormal (ProgramCtx.ofTables (types := #[])) ifaceStructStore := by decide

/-! G23 (2026-11-10): what an interface cell may hold, kernel-decided on small stores. A raw
value is refused; the nil interface and a box whose payload is normal at the box's dynamic type
are admitted — the payload's own boxes included, at any depth (`GoValue.boxesNormal`); a box
whose payload is not normal at its dynamic type is refused, at the top or nested; so is a box
of interface dynamic type (Go never double-boxes); the machine's runtime-error payload (a
`.string` under the reserved index) is admitted. -/
def ifaceRawStore : Store := { heap := #[.value (.interface ⟨"any"⟩) (.int 7 .int)] }
def ifaceBoxStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) .nil,
              .value (.interface ⟨"any"⟩) (.interface .bool (.bool true)),
              .value (.interface ⟨"any"⟩)
                (.interface (.array 1 (.interface ⟨"any"⟩))
                  (.array #[.interface (.int .int) (.int 3 .int)])),
              .value (.interface ⟨"error"⟩)
                (.interface (.defined runtimeErrorTypeIdx) (.string GoString.empty))] }
def ifaceBadPayloadStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.interface .bool (.int 7 .int))] }
def ifaceNestedBadPayloadStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩)
      (.interface (.array 1 (.interface ⟨"any"⟩)) (.array #[.interface .bool (.int 7 .int)]))] }
def ifaceDoubleBoxStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩)
      (.interface (.interface ⟨"any"⟩) (.interface .bool (.bool true)))] }

theorem iface_raw_value_refused :
    ¬ StateWf (ProgramCtx.ofTables (types := #[])) ifaceRawStore := by decide
theorem iface_boxes_admitted :
    StateWf (ProgramCtx.ofTables (types := #[])) ifaceBoxStore := by decide
theorem iface_box_payload_refused :
    ¬ StateWf (ProgramCtx.ofTables (types := #[])) ifaceBadPayloadStore ∧
    ¬ StateWf (ProgramCtx.ofTables (types := #[])) ifaceNestedBadPayloadStore ∧
    ¬ StateWf (ProgramCtx.ofTables (types := #[])) ifaceDoubleBoxStore := by decide

/-- G21 (2026-10-27): a `[]int`-declared cell holding an ARRAY is no longer `HeapNormal`
(`isNormalForTyTy` at `.slice` admits only a `.slice` value), so a path write INTO such a
cell — the shape `slice_cell_path_write_array` pinned as accepted — is impossible under the
invariant, and on the non-normal store the leaf normalization at the descended type
(`.slice .int`, `Ty.stepDown`'s identity arm) refuses by name (`stuck`, «expected slice
value»). (The interface pins above were unchanged by G21; G23 inverted them the same way.) -/
theorem slice_cell_not_normal :
    ¬ HeapNormal (ProgramCtx.ofTables (types := #[])) sliceArrayStore := by decide

/-! G22 (2026-10-27; raft-proofs' ask of 2026-10-26): a map payload's entry stamps are DISTINCT
and BELOW its counter — `HeapCell.normal`'s `.mapPayload` arm is `mapPayloadWf`, so `HeapNormal`,
hence `StateWf`, refuses a hand-built payload with a repeated stamp (the shape on which the range
iterator's candidate filter would skip a key) or with a stamp at the counter, and admits the
shape every run builds: distinct stamps below the counter, gaps included (a deleted stamp is
never reused). The map value cell of the admitted store points at the payload. -/
def repeatedStampStore : Store :=
  { heap := #[.mapPayload #[(0, .int 1, .bool true), (0, .int 2, .bool false)] 2] }
def stampAtCounterStore : Store :=
  { heap := #[.mapPayload #[(0, .int 1, .bool true), (2, .int 2, .bool false)] 2] }
def distinctStampStore : Store :=
  { heap := #[.value (.map .int .bool) (.map { base := some (.base ⟨1⟩) }),
              .mapPayload #[(0, .int 1, .bool true), (3, .int 2, .bool false)] 4] }

theorem repeated_stamp_refused :
    ¬ StateWf (ProgramCtx.ofTables (types := #[])) repeatedStampStore := by decide
theorem stamp_at_counter_refused :
    ¬ StateWf (ProgramCtx.ofTables (types := #[])) stampAtCounterStore := by decide
theorem distinct_stamps_admitted :
    StateWf (ProgramCtx.ofTables (types := #[])) distinctStampStore := by decide

theorem iface_cell_path_write_refuses :
    (match storeLoc (ProgramCtx.ofTables (types := #[])) ifaceArrayStore leaf0 (.int 5 .int) with
      | .error (.stuck _) => true
      | _ => false) = true ∧
    (match storeLoc (ProgramCtx.ofTables (types := #[])) ifaceStructStore leafF (.int 5 .int) with
      | .error (.stuck _) => true
      | _ => false) = true := by decide

theorem slice_cell_path_write_refuses :
    (match storeLoc (ProgramCtx.ofTables (types := #[])) sliceArrayStore leaf0 (.int 5 .int) with
      | .error (.stuck _) => true
      | _ => false) = true := by decide

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

-- The `with_unfolding_all rfl` runs the interpreter (60 fuel) inside the elaborator's
-- definitional unfolding, whose recursion nests deeper than the default `maxRecDepth`
-- (512): fails at 1024, passes at 2048 (measured 2026-10-26, lane
-- core/dc12-warnings-1026); 2x the measured need, for this one theorem. The origins'
-- file-wide `maxRecDepth 8192` / `maxHeartbeats 800000` covered nothing else in §B.
set_option maxRecDepth 4096 in
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

/-! ## D. Pinned statements for the raft-proofs customer (backlog row 47, 2026-10-21)

[AGENT lane core/g11-init-driver-1021]. Each theorem below restates VERBATIM the type of a theorem
of `GoLean/GoCore/InitDriverFacts.lean` (G11: the initialiser's driver `runInitConfig` against
`execStmtLoop` and `Prefix`) or of `GoLean/GoCore/Multi.lean`/`PoolFacts.lean` (G9: the CLI's
output-folding driver `execProgLoopOut` against `execProgLoop`), and is proved by that theorem
alone — a drift in a pinned statement's MEANING fails this build (a non-defeq change such as
`n < fuel` for `n ≤ fuel` or a dropped conjunct); a defeq-preserving respelling (`fuel ≥ n` for
`n ≤ fuel`) still elaborates, so the pin freezes meaning, not text (the limit `BridgeSet.lean` had
too; the `Pin.<name>` convention of `Tests/EquationClient.lean`). Each pin is required by name in
`Tests/GoCoreAudit.lean`. The controls at the end show the premise-free dichotomy's second arm
inhabited: at a print position the init loop refuses where the entry loop steps on (the retired
`SetupStatement.lean`'s negative control, kept). Fix round F2/F5 (2026-10-21): the `Prefix`
determinism laws, the apply-position lemmas, the silent-run converse and the init loop's one-step
rewriting surface (`runInitConfig_unfold`/`_blocked`/`_nonZero`/`_refused`,
`initPrintRefusal?_zeroCost`) are frozen here too. The G16 table-monotonicity statements of
`GoLean/GoCore/TableMonotonicity.lean` (backlog row 48) close the section: pinned here and in the
contract since 2026-10-25 (lane `gate/contract-pins-1025`), after the relation was ruled final. -/

namespace GoLean.GoCore.ContractTests.Pin
open GoCore GoCore.Machine GoCore.ExecutionStatement

/-- The generic certificate theorem, with only sound node equality assumed. -/
theorem checkCert_slowObs
    {ctx : ProgramCtx} {nodeEqb : DedupNode → DedupNode → Bool}
    (hEqb : ∀ a b, nodeEqb a b = true → a = b)
    {resultLocs : List Loc} {m₀ : MultiConfig} {r₀ : RaceState}
    {cert : DedupCert}
    (hc : checkCert ctx nodeEqb resultLocs m₀ r₀ cert = true) :
    ∀ o : Obs, o ∈ cert.obsSet ↔ SlowObs ctx resultLocs m₀ r₀ o :=
  GoCore.Machine.checkCert_slowObs hEqb hc

/-- The concrete node equality used by the CLI discharges that premise. -/
theorem checkCertM_slowObs
    {ctx : ProgramCtx} {resultLocs : List Loc} {m₀ : MultiConfig}
    {r₀ : RaceState} {cert : DedupCert}
    (hc : checkCert ctx dedupNodeEqb resultLocs m₀ r₀ cert = true) :
    ∀ o : Obs, o ∈ cert.obsSet ↔ SlowObs ctx resultLocs m₀ r₀ o :=
  GoCore.Machine.checkCertM_slowObs hc

theorem runInitConfig_cases :
    ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    ((∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
        Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) ∧
      runInitConfig ctx fuel s c ch = execStmtLoop ctx fuel s c ch) ∨
    (∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices) (e : Stop),
      n ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧ ¬ ZeroCost cf ∧
        initPrintRefusal? cf = some e ∧ runInitConfig ctx fuel s c ch = .error e) :=
  GoCore.ExecutionStatement.runInitConfig_cases

theorem runInitConfig_ok_execStmtLoop :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s sf : Store} {c : Config} {ch chf : Choices},
    runInitConfig ctx fuel s c ch = .ok (sf, chf) →
    execStmtLoop ctx fuel s c ch = .ok (sf, chf) :=
  GoCore.ExecutionStatement.runInitConfig_ok_execStmtLoop

theorem runInitConfig_ok_noPrint :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s sf : Store} {c : Config} {ch chf : Choices},
    runInitConfig ctx fuel s c ch = .ok (sf, chf) →
    ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none :=
  GoCore.ExecutionStatement.runInitConfig_ok_noPrint

theorem runInitConfig_ok_prefix :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s sf : Store} {c : Config} {ch chf : Choices},
    runInitConfig ctx fuel s c ch = .ok (sf, chf) →
    ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf :=
  GoCore.ExecutionStatement.runInitConfig_ok_prefix

theorem runInitConfig_eq_execStmtLoop :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices},
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    runInitConfig ctx fuel σ c ch = execStmtLoop ctx fuel σ c ch :=
  GoCore.ExecutionStatement.runInitConfig_eq_execStmtLoop

theorem runInitConfig_ok_iff_execStmtLoop :
    ∀ (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config) (ch chf : Choices),
    runInitConfig ctx fuel s c ch = .ok (sf, chf) ↔
      (execStmtLoop ctx fuel s c ch = .ok (sf, chf) ∧
        ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
          Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) :=
  GoCore.ExecutionStatement.runInitConfig_ok_iff_execStmtLoop

theorem runInitConfig_ok_iff :
    ∀ (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config) (ch chf : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf) :=
  GoCore.ExecutionStatement.runInitConfig_ok_iff

theorem runInitConfig_panic_iff :
    ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) (t : String),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error (.terminal (.panic t)) ↔
      ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf ch'' : Choices)
        (rec : List PickRecord),
        n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧
          Finish ctx sf cf chf rec (.aborted t sf ch'') 1) :=
  GoCore.ExecutionStatement.runInitConfig_panic_iff

theorem runInitConfig_deadlock_iff :
    ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error (.terminal .deadlock) ↔
      ∃ n, n ≤ fuel ∧ ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf [] (.deadlock sf chf) 0) :=
  GoCore.ExecutionStatement.runInitConfig_deadlock_iff

theorem runInitConfig_fuelOut_iff :
    ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (runInitConfig ctx fuel s c ch = .error .fuelOut ↔
      ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf) :=
  GoCore.ExecutionStatement.runInitConfig_fuelOut_iff

theorem runPkgInitM_some :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {ch : Choices} {initF : Func},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    initF.args.size = 0 → initF.results.size = 0 →
    runPkgInitM ctx fuel s ch
      = (runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch).mapError
          markInitPhase :=
  GoCore.ExecutionStatement.runPkgInitM_some

theorem runPkgInitM_ok_iff :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices} {initF : Func},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    initF.args.size = 0 → initF.results.size = 0 →
    (runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) ↔
      runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch
        = .ok (s₁, ch₁)) :=
  GoCore.ExecutionStatement.runPkgInitM_ok_iff

theorem runPkgInitM_ok_prefix :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices} {initF : Func},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) →
    ∃ n, n ≤ fuel ∧ ∃ ls,
      Prefix ctx n s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch ls s₁ (.next .stop) ch₁ :=
  GoCore.ExecutionStatement.runPkgInitM_ok_prefix

theorem runPkgInitM_ok_cases :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices},
    runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) →
    (findFunctionIn? ctx.functions pkgInitFuncId = none ∧ s₁ = s ∧ ch₁ = ch) ∨
    ∃ initF, findFunctionIn? ctx.functions pkgInitFuncId = some initF ∧
      ∃ n, n ≤ fuel ∧ ∃ ls,
        Prefix ctx n s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch ls s₁ (.next .stop) ch₁ :=
  GoCore.ExecutionStatement.runPkgInitM_ok_cases

theorem execProgLoopOut_snd :
    ∀ {ctx : ProgramCtx} (fuel : Nat) (m : MultiConfig) (r : RaceState) (choices : Choices) (acc : GoString),
    (execProgLoopOut ctx fuel m r choices acc).2 = execProgLoop ctx fuel m r choices :=
  GoCore.Machine.execProgLoopOut_snd

theorem execProgLoopOut_acc :
    ∀ {ctx : ProgramCtx} (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices) (acc : GoString),
    (execProgLoopOut ctx fuel m r ch acc).1
      = acc.append (execProgLoopOut ctx fuel m r ch GoString.empty).1 :=
  GoCore.Machine.execProgLoopOut_acc

theorem execProgLoopOut_eq_execProgLoop :
    ∀ {ctx : ProgramCtx} (fuel : Nat) (m : MultiConfig) (r : RaceState) (ch : Choices) (acc : GoString),
    execProgLoopOut ctx fuel m r ch acc
      = (acc.append (execProgLoopOut ctx fuel m r ch GoString.empty).1,
         execProgLoop ctx fuel m r ch) :=
  GoCore.Machine.execProgLoopOut_eq_execProgLoop

theorem prefix_det :
    ∀ {ctx : ProgramCtx} {n : Nat} {s σ₁ σ₂ : Store} {c c₁ c₂ : Config}
    {ch ch₁ ch₂ : Choices} {ls ls' : List StepLabel},
    Prefix ctx n s c ch ls σ₁ c₁ ch₁ → Prefix ctx n s c ch ls' σ₂ c₂ ch₂ →
    ls = ls' ∧ σ₁ = σ₂ ∧ c₁ = c₂ ∧ ch₁ = ch₂ :=
  GoCore.ExecutionStatement.prefix_det

theorem prefix_det_le :
    ∀ {ctx : ProgramCtx} {m n : Nat} {s σ₁ σ₂ : Store} {c c₁ c₂ : Config}
    {ch ch₁ ch₂ : Choices} {ls ls' : List StepLabel},
    Prefix ctx m s c ch ls σ₁ c₁ ch₁ → Prefix ctx n s c ch ls' σ₂ c₂ ch₂ → m ≤ n →
    ∃ ls₂, ls' = ls ++ ls₂ ∧ Prefix ctx (n - m) σ₁ c₁ ch₁ ls₂ σ₂ c₂ ch₂ :=
  GoCore.ExecutionStatement.prefix_det_le

theorem applyStmtOp_print :
    ∀ {ctx : ProgramCtx} {s : Store} {ch : Choices} {newline : Bool} {nt : Nat}
    {vs : List GoValue} {bytes : GoString},
    renderPrint newline vs = .ok bytes →
    applyStmtOp ctx s ch (.print newline) nt vs = .ok (s, ch, [], []) :=
  GoCore.ExecutionStatement.applyStmtOp_print

theorem stepFn_out_of_printOut? :
    ∀ {ctx : ProgramCtx} {s s' : Store} {c c' : Config} {ch ch' : Choices}
    {l : StepLabel} {bytes : GoString},
    printOut? c = some bytes → stepFn ctx s c ch = .ok (c', s', ch', l) → l.out = [bytes] :=
  GoCore.ExecutionStatement.stepFn_out_of_printOut?

theorem initPrintRefusal?_eq_none_iff :
    ∀ {c : Config}, initPrintRefusal? c = none ↔ printOut? c = none :=
  GoCore.ExecutionStatement.initPrintRefusal?_eq_none_iff

theorem noPrint_of_prefix_silent :
    ∀ {ctx : ProgramCtx} {n : Nat} {s sf : Store} {c : Config} {ch chf : Choices} {ls : List StepLabel},
    Prefix ctx n s c ch ls sf (.next .stop) chf → (∀ l ∈ ls, l.out = []) →
    ∀ (m : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls' : List StepLabel),
      Prefix ctx m s c ch ls' σ' c' ch' → initPrintRefusal? c' = none :=
  GoCore.ExecutionStatement.noPrint_of_prefix_silent

theorem runInitConfig_ok_of_prefix_silent :
    ∀ {ctx : ProgramCtx} {fuel n : Nat} {s sf : Store} {c : Config} {ch chf : Choices} {ls : List StepLabel},
    Prefix ctx n s c ch ls sf (.next .stop) chf → n ≤ fuel → (∀ l ∈ ls, l.out = []) →
    runInitConfig ctx fuel s c ch = .ok (sf, chf) :=
  GoCore.ExecutionStatement.runInitConfig_ok_of_prefix_silent

theorem runPkgInitM_ok_of_prefix_silent :
    ∀ {ctx : ProgramCtx} {fuel n : Nat} {s s₁ : Store} {ch ch₁ : Choices} {initF : Func} {ls : List StepLabel},
    findFunctionIn? ctx.functions pkgInitFuncId = some initF →
    initF.args.size = 0 → initF.results.size = 0 →
    Prefix ctx n s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch ls s₁ (.next .stop) ch₁ →
    n ≤ fuel → (∀ l ∈ ls, l.out = []) →
    runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) :=
  GoCore.ExecutionStatement.runPkgInitM_ok_of_prefix_silent

-- F5: the init loop's one-step rewriting surface, frozen.
theorem runInitConfig_unfold :
    ∀ (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices),
    runInitConfig ctx fuel s c ch
      = (match c with
         | .next .stop => .ok (s, ch)
         | .blockedSend _ _ _ => throw .deadlock
         | .blockedRecv _ _ _ _ _ => throw .deadlock
         | .blockedSelect _ _ _ => throw .deadlock
         | .blockedSync _ _ _ _ => throw .deadlock
         | c =>
             match initPrintRefusal? c with
             | some e => throw e
             | none =>
               match fuel with
               | 0 => throw .fuelOut
               | fuel + 1 => do
                   let (c', s', choices', _) ← stepFn ctx s c ch
                   runInitConfig ctx fuel s' c' choices') :=
  GoCore.ExecutionStatement.runInitConfig_unfold

theorem runInitConfig_blocked :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config} {ch : Choices},
    Blocked c → runInitConfig ctx fuel s c ch = .error (.terminal .deadlock) :=
  GoCore.ExecutionStatement.runInitConfig_blocked

theorem runInitConfig_nonZero :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config} {ch : Choices},
    ¬ ZeroCost c → initPrintRefusal? c = none →
    runInitConfig ctx fuel s c ch =
      (match fuel with
       | 0 => .error .fuelOut
       | f + 1 => (stepFn ctx s c ch).bind fun r => runInitConfig ctx f r.2.1 r.1 r.2.2.1) :=
  GoCore.ExecutionStatement.runInitConfig_nonZero

theorem runInitConfig_refused :
    ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config} {ch : Choices} {e : Stop},
    ¬ ZeroCost c → initPrintRefusal? c = some e → runInitConfig ctx fuel s c ch = .error e :=
  GoCore.ExecutionStatement.runInitConfig_refused

theorem initPrintRefusal?_zeroCost :
    ∀ {c : Config}, ZeroCost c → initPrintRefusal? c = none :=
  GoCore.ExecutionStatement.initPrintRefusal?_zeroCost

/-- The initialiser of the control program: `g = 7` (global cell 0). -/
def initControlBody : Stmt := .assign (.addr (.global 0)) (.intLit 7 .int)

/-- `var g int`; `func init() { g = 7 }`; `func F() (z int) { z = g }` — one global, one
initializer writing it, the subject reading it. -/
def initControl : Program := {
  funcs := #[
    { id := ⟨"F"⟩, args := #[], results := #[{ id := 1, typ := .int }],
      body := .assign (.var 1) (.deref (.global 0) .int) },
    { id := pkgInitFuncId, args := #[], results := #[], body := initControlBody } ],
  globals := #[{ name := "g", typ := .int }] }

/-- A `println(1)` at its apply position: the one operand delivered, no targets, nothing pending. -/
def printPosition : Config := .retV (.int 1 .int) (.stmtOpK (.print true) 0 [] [] [] .stop)

/-- The dichotomy's second arm, inhabited: at the print position the guard FIRES by name. -/
theorem init_print_refused_control :
    initPrintRefusal? printPosition = some (Stop.unsupported "print/println during package initialization: the init phase runs on the sequential driver, which has no output event channel (the pool driver folds StepEvent.out) — refused rather than dropping the bytes (stdlib slice 3; row builtins/print/in-init)") :=
  rfl

/-- The init loop at the print position: the guard's refusal (at fuel 4, with steps to spare). -/
theorem init_print_loop_refuses_control :
    runInitConfig ⟨initControl⟩ 4 {} printPosition []
      = .error ((initPrintRefusal? printPosition).getD .fuelOut) :=
  rfl

/-- The entry loop at the same position steps through to `.next .stop` (the print's bytes ride the
step label, which this driver drops — exactly what the init guard exists to refuse). -/
theorem init_print_entry_loop_completes_control :
    execStmtLoop ⟨initControl⟩ 4 {} printPosition [] = .ok ({}, []) :=
  rfl

/-- So the two loops DIFFER there and no premise-free EQUATION holds; the dichotomy
`runInitConfig_cases` is the statement. -/
theorem init_print_loops_differ_control :
    runInitConfig ⟨initControl⟩ 4 {} printPosition [] ≠ execStmtLoop ⟨initControl⟩ 4 {} printPosition [] := by
  rw [init_print_loop_refuses_control, init_print_entry_loop_completes_control]
  intro h
  cases h

/-! The phase's mark of a NON-CARRIER payload (lane `core/g16-raise-mark-1023`, review fix round F2,
2026-10-23; `GoLean/GoCore/Equations.lean`): the premise the customer's symbolic route discharges at
the decision step (`panicking_stop_raised`) for a `string` payload or any non-carrier type. -/
theorem phaseMark_nonCarrier :
    ∀ {ctx : ProgramCtx} {t : Ty} (v : GoValue), (∀ e, t ≠ .pointer e) → methodCarrierKey? ctx t = none →
    ctx.methods.all (fun m => methodRecvDynamicTy? m != some t) = true →
    phaseMark ctx (.interface t v) = .ok .none :=
  GoCore.Equations.phaseMark_nonCarrier

theorem phaseMark_string :
    ∀ {ctx : ProgramCtx} (v : GoValue),
    ctx.methods.all (fun m => methodRecvDynamicTy? m != some .string) = true →
    phaseMark ctx (.interface .string v) = .ok .none :=
  GoCore.Equations.phaseMark_string

/-! raft-proofs G19 (backlog row 50, [USER]-ruled 2026-10-25, option 1; lane
`frontend/g19-sort-intercept-1025`; `GoLean/GoCore/Equations.lean`): the `sortSlice` machine op —
`slices.Sort(s)` at an integer element kind — and its SPECIFICATION. The plan arm, the apply written
out over the memory primitives, the apply and the apply step read back as «the run written from
visible index 0 is a `List.Perm` of the run read, ascending by value, the tape untouched, no pick,
the label the reads then the writes», and the integer sort laws they rest on. -/
theorem exec_sortSlice :
    ∀ {ctx : ProgramCtx} (s : Store) (base : Expr) (elem : Ty) (env : LocalEnv) (k : Cont) (ch : Choices),
    stepFn ctx s (.exec (.sortSlice base elem) env k) ch
      = .ok (.evalE base env (.stmtOpK (.sortSlice elem) 0 [] [] env k), s, ch, ⟨[], [], []⟩) :=
  GoCore.Equations.exec_sortSlice

theorem applyStmtOp_sortSlice :
    ∀ {ctx : ProgramCtx} {s s' : Store} {baseV : GoValue} {sl : SliceValue} {vs : Array GoValue}
      {trR trW : AccessTrace} {pairs : List (Int × IntKind)} (elem : Ty) (ch : Choices),
    valueAsSlice baseV = .ok sl → Mem.loadSlice ctx s sl = .ok (vs, trR) → intElems vs.toList = .ok pairs →
    Mem.storeRun ctx s sl 0 ((sortLe (fun a b => a.1 ≤ b.1) pairs).map fun p => GoValue.int p.1 p.2)
      = .ok (s', trW) →
    applyStmtOp ctx s ch (.sortSlice elem) 0 [baseV] = .ok (s', ch, [], trR ++ trW) :=
  GoCore.Equations.applyStmtOp_sortSlice

theorem applyStmtOp_sortSlice_spec :
    ∀ {ctx : ProgramCtx} {s s' : Store} {ch ch' : Choices} {ps : List PickRecord} {tr : AccessTrace}
      {elem : Ty} {baseV : GoValue},
    applyStmtOp ctx s ch (.sortSlice elem) 0 [baseV] = .ok (s', ch', ps, tr) →
    ∃ (sl : SliceValue) (vs : Array GoValue) (trR : AccessTrace) (pairs sorted : List (Int × IntKind))
      (trW : AccessTrace),
      valueAsSlice baseV = .ok sl ∧ Mem.loadSlice ctx s sl = .ok (vs, trR) ∧ intElems vs.toList = .ok pairs ∧
      List.Perm sorted pairs ∧ sorted.Pairwise (fun a b => a.1 ≤ b.1) ∧
      Mem.storeRun ctx s sl 0 (sorted.map fun p => GoValue.int p.1 p.2) = .ok (s', trW) ∧
      ch' = ch ∧ ps = [] ∧ tr = trR ++ trW :=
  GoCore.Equations.applyStmtOp_sortSlice_spec

theorem retV_stmtOpK_sortSlice :
    ∀ {ctx : ProgramCtx} {s s' : Store} {baseV : GoValue} {sl : SliceValue} {vs : Array GoValue}
      {trR trW : AccessTrace} {pairs : List (Int × IntKind)} (elem : Ty) (env : LocalEnv) (k' : Cont)
      (ch : Choices),
    valueAsSlice baseV = .ok sl → Mem.loadSlice ctx s sl = .ok (vs, trR) → intElems vs.toList = .ok pairs →
    Mem.storeRun ctx s sl 0 ((sortLe (fun a b => a.1 ≤ b.1) pairs).map fun p => GoValue.int p.1 p.2)
      = .ok (s', trW) →
    stepFn ctx s (.retV baseV (.stmtOpK (.sortSlice elem) 0 [] [] env k')) ch
      = .ok (.next k', s', ch, ⟨trR ++ trW, [], []⟩) :=
  GoCore.Equations.retV_stmtOpK_sortSlice

theorem retV_stmtOpK_sortSlice_spec :
    ∀ {ctx : ProgramCtx} {s s' : Store} {ch ch' : Choices} {lbl : StepLabel} {elem : Ty} {baseV : GoValue}
      (env : LocalEnv) (k' : Cont),
    stepFn ctx s (.retV baseV (.stmtOpK (.sortSlice elem) 0 [] [] env k')) ch = .ok (.next k', s', ch', lbl) →
    ∃ (sl : SliceValue) (vs : Array GoValue) (trR : AccessTrace) (pairs sorted : List (Int × IntKind))
      (trW : AccessTrace),
      valueAsSlice baseV = .ok sl ∧ Mem.loadSlice ctx s sl = .ok (vs, trR) ∧ intElems vs.toList = .ok pairs ∧
      List.Perm sorted pairs ∧ sorted.Pairwise (fun a b => a.1 ≤ b.1) ∧
      Mem.storeRun ctx s sl 0 (sorted.map fun p => GoValue.int p.1 p.2) = .ok (s', trW) ∧
      ch' = ch ∧ lbl = ⟨trR ++ trW, [], []⟩ :=
  GoCore.Equations.retV_stmtOpK_sortSlice_spec

theorem sortLe_int_perm :
    ∀ (ps : List (Int × IntKind)), List.Perm (sortLe (fun a b => a.1 ≤ b.1) ps) ps :=
  GoCore.Equations.sortLe_int_perm

theorem sortLe_int_pairwise :
    ∀ (ps : List (Int × IntKind)), (sortLe (fun a b => a.1 ≤ b.1) ps).Pairwise (fun a b => a.1 ≤ b.1) :=
  GoCore.Equations.sortLe_int_pairwise

/-! Review fix round F5 (2026-10-25): the EXACT stored run — `sortLe` of the pairs read, no premise beyond
the apply's / the step's success — and the sorted-permutation uniqueness bridge (kind-uniform pairs) that
takes a consumer's own sorted list to it. -/
theorem applyStmtOp_sortSlice_exact :
    ∀ {ctx : ProgramCtx} {s s' : Store} {ch ch' : Choices} {ps : List PickRecord} {tr : AccessTrace}
      {elem : Ty} {baseV : GoValue},
    applyStmtOp ctx s ch (.sortSlice elem) 0 [baseV] = .ok (s', ch', ps, tr) →
    ∃ (sl : SliceValue) (vs : Array GoValue) (trR : AccessTrace) (pairs : List (Int × IntKind))
      (trW : AccessTrace),
      valueAsSlice baseV = .ok sl ∧ Mem.loadSlice ctx s sl = .ok (vs, trR) ∧ intElems vs.toList = .ok pairs ∧
      Mem.storeRun ctx s sl 0 ((sortLe (fun a b => a.1 ≤ b.1) pairs).map fun p => GoValue.int p.1 p.2)
        = .ok (s', trW) ∧
      ch' = ch ∧ ps = [] ∧ tr = trR ++ trW :=
  GoCore.Equations.applyStmtOp_sortSlice_exact

theorem retV_stmtOpK_sortSlice_exact :
    ∀ {ctx : ProgramCtx} {s s' : Store} {ch ch' : Choices} {lbl : StepLabel} {elem : Ty} {baseV : GoValue}
      (env : LocalEnv) (k' : Cont),
    stepFn ctx s (.retV baseV (.stmtOpK (.sortSlice elem) 0 [] [] env k')) ch = .ok (.next k', s', ch', lbl) →
    ∃ (sl : SliceValue) (vs : Array GoValue) (trR : AccessTrace) (pairs : List (Int × IntKind))
      (trW : AccessTrace),
      valueAsSlice baseV = .ok sl ∧ Mem.loadSlice ctx s sl = .ok (vs, trR) ∧ intElems vs.toList = .ok pairs ∧
      Mem.storeRun ctx s sl 0 ((sortLe (fun a b => a.1 ≤ b.1) pairs).map fun p => GoValue.int p.1 p.2)
        = .ok (s', trW) ∧
      ch' = ch ∧ lbl = ⟨trR ++ trW, [], []⟩ :=
  GoCore.Equations.retV_stmtOpK_sortSlice_exact

theorem sortedPairs_unique :
    ∀ {l₁ l₂ : List (Int × IntKind)} (k : IntKind), (∀ p ∈ l₁, p.2 = k) →
    l₁.Pairwise (fun a b => a.1 ≤ b.1) → l₂.Pairwise (fun a b => a.1 ≤ b.1) → List.Perm l₁ l₂ → l₁ = l₂ :=
  GoCore.Equations.sortedPairs_unique

theorem sortLe_int_eq_of_pairwise :
    ∀ {pairs : List (Int × IntKind)} (k : IntKind), (∀ p ∈ pairs, p.2 = k) →
    pairs.Pairwise (fun a b => a.1 ≤ b.1) → sortLe (fun a b => a.1 ≤ b.1) pairs = pairs :=
  GoCore.Equations.sortLe_int_eq_of_pairwise




/-! raft-proofs G16 (backlog row 48, 2026-10-23; `GoLean/GoCore/TableMonotonicity.lean`, lanes
`core/g16-table-monotonicity-1023` and `core/g16-raise-mark-1023`; pinned in the former §E
Provisional while the relation was being redesigned, moved here and into the comparator contract
(family `g16`, `scripts/contract-names.lean`) by lane `gate/contract-pins-1025` on the [USER] ruling
of 2026-10-25 that the per-key relation of train 17 is final): a successful step under a
SLICE of the function, method, method-set and promotion tables (`ProgramCtx.SubTables`: same
`typeDefs`/`globals`/`typeDisplays`, sublists of the four tables, the whole's key discipline, the
slice's PER-KEY closure — a kept record's carrier keeps its methods and promotions with their
`Func`s, a kept `Func` its `MethodInfo`) is the step under the whole, lifted to `Prefix`, the
abort's `Finish` and the sequential driver's completion and panic; the first-match lookups and
the frame-entry funnel it rests on. -/

theorem stepFn_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b →
    ∀ {s : Store} {c : Config} {ch : Choices} {r : Config × Store × Choices × StepLabel},
    stepFn a s c ch = .ok r → stepFn b s c ch = .ok r :=
  GoCore.ProgramCtx.SubTables.stepFn_mono

theorem prefix_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b →
    ∀ {n : Nat} {s sf : Store} {c cf : Config} {ch chf : Choices} {ls : List StepLabel},
    Prefix a n s c ch ls sf cf chf → Prefix b n s c ch ls sf cf chf :=
  GoCore.ProgramCtx.SubTables.prefix_mono

theorem finish_aborted_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b →
    ∀ {s : Store} {c : Config} {ch ch'' : Choices} {rec : List PickRecord} {t : String},
    Finish a s c ch rec (.aborted t s ch'') 1 → Finish b s c ch rec (.aborted t s ch'') 1 :=
  GoCore.ProgramCtx.SubTables.finish_aborted_mono

theorem execStmtLoop_ok_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b →
    ∀ {fuel : Nat} {s sf : Store} {c : Config} {ch chf : Choices},
    execStmtLoop a fuel s c ch = .ok (sf, chf) → execStmtLoop b fuel s c ch = .ok (sf, chf) :=
  GoCore.ProgramCtx.SubTables.execStmtLoop_ok_mono

theorem execStmtLoop_panic_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b →
    ∀ {fuel : Nat} {s : Store} {c : Config} {ch : Choices} {t : String},
    execStmtLoop a fuel s c ch = .error (.terminal (.panic t)) →
      execStmtLoop b fuel s c ch = .error (.terminal (.panic t)) :=
  GoCore.ProgramCtx.SubTables.execStmtLoop_panic_mono

theorem findFunctionIn?_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b → ∀ {fid : FuncId} {f : Func},
    findFunctionIn? a.functions fid = some f → findFunctionIn? b.functions fid = some f :=
  GoCore.ProgramCtx.SubTables.findFunctionIn?_mono

theorem methodInfoByFuncId?_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b → ∀ {fid : FuncId} {m : MethodInfo},
    methodInfoByFuncId? a fid = some m → methodInfoByFuncId? b fid = some m :=
  GoCore.ProgramCtx.SubTables.methodInfoByFuncId?_mono

theorem methodDecl?_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b → ∀ {t : Ty} {M : Declaration.MemberId} {m : MethodInfo},
    methodDecl? a t M = some m → methodDecl? b t M = some m :=
  GoCore.ProgramCtx.SubTables.methodDecl?_mono

theorem promotion?_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b → ∀ {c : TypeId} {M : Declaration.MemberId} {p : Promotion},
    promotion? a c M = some p → promotion? b c M = some p :=
  GoCore.ProgramCtx.SubTables.promotion?_mono

/-- Added at the fix round of 2026-10-25 (the coordinator's decision, relayed): the method-set record
lookup is a first-match lookup of the same kind as the six above, and the customer's ask names it. -/
theorem methodSetCoverage?_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b → ∀ {key : String} {cov : MethodSetCoverage},
    methodSetCoverage? a key = some cov → methodSetCoverage? b key = some cov :=
  GoCore.ProgramCtx.SubTables.methodSetCoverage?_mono

theorem resolveMethod?_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b →
    ∀ {t : Ty} {M : Declaration.MemberId} {r : MethodResolution},
    resolveMethod? a t M = some r → resolveMethod? b t M = some r :=
  GoCore.ProgramCtx.SubTables.resolveMethod?_mono

theorem callee?_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b → ∀ {fid : FuncId} {c : Callee},
    callee? a fid = some c → callee? b fid = some c :=
  GoCore.ProgramCtx.SubTables.callee?_mono

theorem enterFramePickV_mono :
    ∀ {a b : ProgramCtx}, a.SubTables b →
    ∀ {s : Store} {fid : FuncId} {args : List GoValue} {ch : Choices}
      {x : Result (Commit (Entry × Store × AccessTrace)) × Choices × List PickRecord},
    enterFramePickV a s fid args ch = .ok x → enterFramePickV b s fid args ch = .ok x :=
  GoCore.ProgramCtx.SubTables.enterFramePickV_mono

end GoLean.GoCore.ContractTests.Pin
