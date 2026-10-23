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
`initPrintRefusal?_zeroCost`) are frozen here too. -/

namespace GoLean.GoCore.ContractTests.Pin
open GoCore GoCore.Machine GoCore.ExecutionStatement

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

end GoLean.GoCore.ContractTests.Pin

/-! ## §E Provisional statements (pinned for build-time drift; NOT in the comparator contract)

The G16 table-monotonicity statements below are proved and pinned like §D, but they are kept
OUT of `comparator.json`'s frozen surface until backlog row 48's ruling settles the relation
`ProgramCtx.SubTables` (the review of 2026-10-23 measured that its premises defeat the
customer's slicing; a redesign would change these statements). `scripts/gen-contract --check`
reads §D only, so a pin here does not demand a contract entry. Move a statement to §D when it
is settled. -/
namespace GoLean.GoCore.ContractTests.Provisional

open GoCore GoCore.Machine GoCore.ExecutionStatement

/-! raft-proofs G16 (backlog row 48, 2026-10-23; `GoLean/GoCore/TableMonotonicity.lean`, lane
`core/g16-table-monotonicity-1023`): a successful step under a SLICE of the function, method and
promotion tables (`ProgramCtx.SubTables`: same `typeDefs`/`globals`/`typeDisplays`/`methodSets`,
sublists of the three tables, the whole's key discipline, the slice's closures) is the step under
the whole, lifted to `Prefix`, the abort's `Finish` and the sequential driver's completion and
panic; the first-match lookups and the frame-entry funnel it rests on. -/

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

end GoLean.GoCore.ContractTests.Provisional
