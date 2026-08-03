import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Laws.Range
import GoLeanProofs.Laws.Call
import GoLeanProofs.Specs.GoldenQuorum

/-!
# The quorum pin — projections and witnesses on the pinned lowering

TARGET-SPECIFIC by design (the layering doctrine,
`docs/2026-08-01_tcb-and-layering-doctrine.md` §2): everything here is
about `GoldenQuorum.quorumLowered`, the frontend's pinned lowering of
the real etcd-io/raft `quorum` driver. The GENERAL laws these witnesses
instantiate live in `Laws/StmtOps.lean` (the wide-op walk), `Laws/Range.lean`
and `Laws/Call.lean`; nothing in this module is a law.

Contents:

- **`QuorumPin`** — the pin projections: statements, function bodies,
  type-environment entries and the method table, each `rfl`-checked
  against `quorumLowered` so that editing the pin breaks the build here
  rather than silently invalidating a walk.
- **The non-vacuity witnesses** on the pinned lowering, one per law
  family the `CommittedIndex`/`AckedIndex` walks consume:
  `wp_map_range_snapshot_committed`, `wp_sort_slice_srt`,
  `wp_map_lookup_ackedIndex_entries` (+ the registered one-entry
  specialization `wp_map_lookup_ackedIndex`), `wp_make_slice_c2`,
  `wp_call_dynamic_enter_ackedIndex`, `wp_call_enter_ackedIndexImpl`.
- **`typeEnv_pin_is_load_bearing`** — the kernel-checked regression
  guard on the `σ.types` ghost pin (quorum pilot phase 4, 2026-07-31):
  frame entry into this program resolves `.defined` names through
  `TypeEnv.lookup σ.types` (`bindParams`, `allocDecls`,
  `concreteMethodForDynamic?`), so without `GoCoreGS.types` every
  `∀ σ`-premise about them was FALSE and the dispatch laws vacuous. A
  second blocker fixed in the same slice: `Ty`'s derived `BEq` was
  opaque (nested inductive), replaced by the total transparent `Ty.eqb`
  (`GoLean/GoCore/Value.lean`).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

set_option linter.unusedSimpArgs false

/-! ## The witness subjects, EXTRACTED FROM THE PIN

Each witness below runs on a statement *projected out of*
`GoldenQuorum.quorumLowered` — the frontend's actual lowering — so the
`rfl`-checked `*_eq` lemmas are what tie the laws to the real code (edit
the pin and these stop being `rfl`). -/

namespace QuorumPin

open GoLean.Iris.GoldenQuorum

/-- The pinned `main.MajorityConfig.CommittedIndex`'s statement list. -/
def committedIndexStmts : Array Stmt :=
  match findFunctionIn? quorumLowered.funcs ⟨"main.MajorityConfig.CommittedIndex"⟩ with
  | some f => match f.body with
    | .block _ ss => ss
    | _ => #[]
  | none => #[]

/-- The pinned `main.mapAckIndexer.AckedIndex`'s statement list. -/
def ackedIndexStmts : Array Stmt :=
  match findFunctionIn? quorumLowered.funcs ⟨"main.mapAckIndexer.AckedIndex"⟩ with
  | some f => match f.body with
    | .block _ ss => ss
    | _ => #[]
  | none => #[]

/-- `slices.Sort(srt)` — the sort of the acked-index scratch slice. -/
def sortStmt : Stmt := (committedIndexStmts[6]?).getD (.seqn #[])

/-- `for id := range c` — the voter loop. -/
def rangeStmt : Stmt :=
  match (committedIndexStmts[5]?).getD (.seqn #[]) with
  | .block _ inner => (inner[1]?).getD (.seqn #[])
  | _ => .seqn #[]

/-- The voter loop's body (whatever the pin says it is). -/
def rangeBody : Stmt :=
  match rangeStmt with
  | .mapRange _ _ _ _ _ b => b
  | _ => .seqn #[]

/-- `idx, ok := m[id]` — the comma-ok read inside `AckedIndex`. -/
def mapLookupStmt : Stmt :=
  match (ackedIndexStmts[0]?).getD (.seqn #[]) with
  | .seqn arr => (arr[2]?).getD (.seqn #[])
  | _ => .seqn #[]

/-- Fallback for the projections below — never selected on the pin (each
`*_find` lemma below is `rfl`-checked against `quorumLowered`). -/
def missingFunc : Func :=
  { id := ⟨"$absent"⟩, args := #[], results := #[], body := .seqn #[] }

/-- The interface ANCHOR `Func` — `main.AckedIndexer.AckedIndex`, the
bodiless dispatch target the callsite names. -/
def ackedIndexAnchor : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"main.AckedIndexer.AckedIndex"⟩).getD
    missingFunc

/-- The CONCRETE implementation `main.mapAckIndexer.AckedIndex`. -/
def ackedIndexImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"main.mapAckIndexer.AckedIndex"⟩).getD
    missingFunc

theorem ackedIndexAnchor_find :
    findFunctionIn? quorumLowered.funcs ⟨"main.AckedIndexer.AckedIndex"⟩
      = some ackedIndexAnchor := rfl

theorem ackedIndexImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"main.mapAckIndexer.AckedIndex"⟩
      = some ackedIndexImpl := rfl

theorem ackedIndexAnchor_args : ackedIndexAnchor.args.size = 2 := rfl

theorem ackedIndexImpl_args :
    ackedIndexImpl.args = #[⟨"m", .defined ⟨"main.mapAckIndexer"⟩⟩,
                            ⟨"id", .int .uint64⟩] := rfl

/-! The pinned program's TYPE ENVIRONMENT entries, `rfl`-projected. These
keep `simp` off the 1400-line program literal: every resolution of a named
type in a witness goes through one of these. -/

theorem typeEnv_Index :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"main.Index"⟩
      = some (.defined (.int .uint64)) := rfl

theorem typeEnv_mapAckIndexer :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"main.mapAckIndexer"⟩
      = some (.defined (.map (.int .uint64) (.defined ⟨"main.Index"⟩))) := rfl

theorem typeEnv_structEmpty :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"struct{}"⟩
      = some (.struct #[]) := rfl

theorem typeEnv_MajorityConfig :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"main.MajorityConfig"⟩
      = some (.defined (.map (.int .uint64) (.defined ⟨"struct{}"⟩))) := rfl

/-- The pinned METHOD TABLE, as a literal (so `simp` can run the
`methodInfoByFuncId?`/`concreteMethodForDynamic?` folds). -/
theorem quorumMethods_eq :
    quorumLowered.methods =
      #[{ name := "AckedIndex", funcId := ⟨"main.AckedIndexer.AckedIndex"⟩,
          recv := .interface ⟨"main.AckedIndexer"⟩ },
        { name := "AckedIndex", funcId := ⟨"main.mapAckIndexer.AckedIndex"⟩,
          recv := .defined ⟨"main.mapAckIndexer"⟩ },
        { name := "Slice", funcId := ⟨"main.MajorityConfig.Slice"⟩,
          recv := .defined ⟨"main.MajorityConfig"⟩ },
        { name := "CommittedIndex", funcId := ⟨"main.MajorityConfig.CommittedIndex"⟩,
          recv := .defined ⟨"main.MajorityConfig"⟩ }] := rfl

/-- Reflexivity of `BEq Ty` at the receiver type the dispatch compares.

Docstring corrected 2026-07-31 (pre-merge audit, finding 11 — it was
stale at birth, written in the very commit that changed the fact): `Ty`
no longer `deriving BEq`. Its instance is the hand-written, TOTAL,
transparent `Ty.eqb` (`GoLean/GoCore/Value.lean`, see this file's module
header), so `rfl` closes this goal too — `decide` is no longer the only
route. `simp` still makes no progress on it, and generic reflexivity
`∀ t, t == t` is still not a theorem — but for a NEW reason: `Ty.eqb` is
FUEL-BOUNDED (`tyEqFuel`) and answers `false` on exhaustion, so
reflexivity holds only below the fuel depth, which is why the dispatch
facts stay per-instance. -/
theorem beq_mapAckIndexer_self :
    ((Ty.defined ⟨"main.mapAckIndexer"⟩) == (Ty.defined ⟨"main.mapAckIndexer"⟩))
      = true := by decide

theorem ackedIndexAnchor_id :
    ackedIndexAnchor.id = ⟨"main.AckedIndexer.AckedIndex"⟩ := rfl

theorem ackedIndexImpl_results :
    ackedIndexImpl.results = #[⟨"$res0", .defined ⟨"main.Index"⟩⟩,
                               ⟨"$res1", .bool⟩] := rfl

theorem sortStmt_eq : sortStmt = .sortSlice (.var "srt") (.int .uint64) := rfl

theorem rangeStmt_eq :
    rangeStmt = .mapRange (some "id") none (.var "c") (.int .uint64)
      (.defined ⟨"struct{}"⟩) rangeBody := rfl

theorem mapLookupStmt_eq :
    mapLookupStmt = .mapLookup (.var "idx") (.var "ok") (.var "m") (.var "id")
      (.int .uint64) (.defined ⟨"main.Index"⟩) := rfl

/-- The CONCRETE method's whole body, `rfl`-projected out of the pin: a
declaration-free block of two sequences — declare `idx : main.Index` and
`ok : bool`, the comma-ok read, then the two result writes and `return`.
Edit the pin and this stops being `rfl`. -/
theorem ackedIndexImpl_body_eq :
    ackedIndexImpl.body = .block #[]
      #[.seqn #[.initialization ⟨"idx", .defined ⟨"main.Index"⟩⟩,
                .initialization ⟨"ok", .bool⟩,
                mapLookupStmt],
        .seqn #[.assign (.var "$res0") (.var "idx"),
                .assign (.var "$res1") (.var "ok"),
                .returnStmt]] := rfl

/-! ### The whole driver chain, `rfl`-projected out of the pin

`committedOneKnown → run → main.MajorityConfig.CommittedIndex` — the three
function bodies the summit walk traverses, each split into the statements
the walk steps through. Every lemma below is `rfl` against
`GoldenQuorum.quorumLowered`: edit the pin and they stop compiling, which
is the whole point of naming them rather than inlining literals. -/

def committedIndexImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"main.MajorityConfig.CommittedIndex"⟩).getD
    missingFunc

def runImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"run"⟩).getD missingFunc

def oneKnownImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"committedOneKnown"⟩).getD missingFunc

theorem committedIndexImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"main.MajorityConfig.CommittedIndex"⟩
      = some committedIndexImpl := rfl

theorem runImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"run"⟩ = some runImpl := rfl

theorem oneKnownImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"committedOneKnown"⟩
      = some oneKnownImpl := rfl

theorem committedIndexImpl_args :
    committedIndexImpl.args = #[⟨"c", .defined ⟨"main.MajorityConfig"⟩⟩,
                                ⟨"l", .interface ⟨"main.AckedIndexer"⟩⟩] := rfl

theorem committedIndexImpl_results :
    committedIndexImpl.results = #[⟨"$res0", .defined ⟨"main.Index"⟩⟩] := rfl

theorem runImpl_args :
    runImpl.args = #[⟨"c", .defined ⟨"main.MajorityConfig"⟩⟩,
                     ⟨"l", .defined ⟨"main.mapAckIndexer"⟩⟩] := rfl

theorem runImpl_results :
    runImpl.results = #[⟨"$res0", .int .uint64⟩] := rfl

theorem oneKnownImpl_args : oneKnownImpl.args = #[] := rfl

theorem oneKnownImpl_results :
    oneKnownImpl.results = #[⟨"$res0", .int .uint64⟩] := rfl

theorem committedIndexImpl_body_eq :
    committedIndexImpl.body = .block #[] committedIndexStmts := rfl

/-! The nine statements of `CommittedIndex`, in order. -/

def ciLenStmt : Stmt := (committedIndexStmts[0]?).getD (.seqn #[])
def ciEmptyIf : Stmt := (committedIndexStmts[1]?).getD (.seqn #[])
def ciStkDecl : Stmt := (committedIndexStmts[2]?).getD (.seqn #[])
def ciSrtDecl : Stmt := (committedIndexStmts[3]?).getD (.seqn #[])
def ciFitIf : Stmt := (committedIndexStmts[4]?).getD (.seqn #[])
def ciLoopBlock : Stmt := (committedIndexStmts[5]?).getD (.seqn #[])
def ciPosStmt : Stmt := (committedIndexStmts[7]?).getD (.seqn #[])
def ciResStmt : Stmt := (committedIndexStmts[8]?).getD (.seqn #[])

theorem committedIndexStmts_toList :
    committedIndexStmts.toList =
      [ciLenStmt, ciEmptyIf, ciStkDecl, ciSrtDecl, ciFitIf, ciLoopBlock,
       sortStmt, ciPosStmt, ciResStmt] := rfl

theorem ciLenStmt_eq :
    ciLenStmt = .seqn #[.initialization ⟨"n", .int .int⟩,
      .assign (.var "n")
        (.length (.var "c") (some (.defined ⟨"main.MajorityConfig"⟩)))] := rfl

theorem ciEmptyIf_eq :
    ciEmptyIf = .ifThenElse (.eqCmp (.int .int) (.var "n") (.intLit 0 .int))
      (.block #[] #[.seqn #[.assign (.var "$res0")
        (.intLit 18446744073709551615 .uint64), .returnStmt]])
      (.seqn #[]) := rfl

theorem ciStkDecl_eq :
    ciStkDecl = .seqn #[.initialization ⟨"stk", .array 7 (.int .uint64)⟩] := rfl

theorem ciSrtDecl_eq :
    ciSrtDecl = .seqn #[.initialization ⟨"srt", .slice (.int .uint64)⟩] := rfl

/-- The `len(stk) >= n` fit test. The TAKEN branch reslices the on-stack
array (`srt = stk[:n]`); the other allocates (`make([]uint64, n)`). -/
theorem ciFitIf_eq :
    ciFitIf = .ifThenElse (.atLeastCmp (.intLit 7 .int) (.var "n"))
      (.block #[] #[.seqn #[.assign (.var "srt")
        (.slice (.ref "stk") (.intLit 0 .int) (.var "n") none)]])
      (.block #[]
        #[.seqn #[.initialization ⟨"$c2", .slice (.int .uint64)⟩,
                  .makeSlice (.var "$c2") (.int .uint64) (.var "n") none],
          .seqn #[.assign (.var "srt") (.var "$c2")]]) := rfl

/-- `$c2 = make([]uint64, n)` — the heap-allocating branch of the fit
test (`len(stk) >= n` false). Not on the `n = 1` path, which is exactly
why it is the right subject for the `makeSlice` witness: the law must be
discharged on a real statement even where the summit walk does not go. -/
def ciMakeSliceStmt : Stmt :=
  match ciFitIf with
  | .ifThenElse _ _ (.block _ inner) =>
      match (inner[0]?).getD (.seqn #[]) with
      | .seqn arr => (arr[1]?).getD (.seqn #[])
      | _ => .seqn #[]
  | _ => .seqn #[]

theorem ciMakeSliceStmt_eq :
    ciMakeSliceStmt = .makeSlice (.var "$c2") (.int .uint64) (.var "n") none :=
  rfl

def ciIDecl : Stmt :=
  .seqn #[.initialization ⟨"i", .int .int⟩,
          .assign (.var "i") (.sub (.var "n") (.intLit 1 .int))]

theorem ciLoopBlock_eq : ciLoopBlock = .block #[] #[ciIDecl, rangeStmt] := rfl

def ciCallSeq : Stmt :=
  .seqn #[.initialization ⟨"idx", .defined ⟨"main.Index"⟩⟩,
          .initialization ⟨"ok", .bool⟩,
          .call #[.var "idx", .var "ok"] ⟨"main.AckedIndexer.AckedIndex"⟩
            #[.var "l", .var "id"]]

def ciOkThen : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "srt") (.var "i")))
                (.convert (.int .uint64) (.var "idx"))],
      .assign (.var "i") (.sub (.var "i") (.intLit 1 .int))]

def ciOkIf : Stmt := .ifThenElse (.var "ok") ciOkThen (.seqn #[])

theorem rangeBody_eq :
    rangeBody = .block #[] #[.block #[] #[ciCallSeq, ciOkIf]] := rfl

theorem ciPosStmt_eq :
    ciPosStmt = .seqn #[.initialization ⟨"pos", .int .int⟩,
      .assign (.var "pos")
        (.sub (.var "n") (.add (.div (.var "n") (.intLit 2 .int))
          (.intLit 1 .int)))] := rfl

theorem ciResStmt_eq :
    ciResStmt = .seqn #[.assign (.var "$res0")
        (.convert (.defined ⟨"main.Index"⟩) (.indexGet (.var "srt") (.var "pos"))),
      .returnStmt] := rfl

/-! `run`, the two-statement wrapper the driver calls. -/

def runCallSeq : Stmt :=
  .seqn #[.initialization ⟨"$c3", .defined ⟨"main.Index"⟩⟩,
          .call #[.var "$c3"] ⟨"main.MajorityConfig.CommittedIndex"⟩
            #[.var "c",
              .toInterface (.interface ⟨"main.AckedIndexer"⟩)
                (.defined ⟨"main.mapAckIndexer"⟩) (.var "l")]]

def runResSeq : Stmt :=
  .seqn #[.assign (.var "$res0") (.convert (.int .uint64) (.var "$c3")),
          .returnStmt]

theorem runImpl_body_eq : runImpl.body = .block #[] #[runCallSeq, runResSeq] := rfl

/-! `committedOneKnown`, the driver: build `MajorityConfig{1:{}}` and
`mapAckIndexer{1:12}`, call `run`, return. -/

def okCfgSeq : Stmt :=
  .seqn #[.initialization ⟨"$c10", .map (.int .uint64) (.defined ⟨"struct{}"⟩)⟩,
          .makeMap (.var "$c10") (.int .uint64) (.defined ⟨"struct{}"⟩) none,
          .mapAssign (.var "$c10") (.intLit 1 .uint64)
            (.structLit (.defined ⟨"struct{}"⟩) #[])
            (.int .uint64) (.defined ⟨"struct{}"⟩)]

def okAckSeq : Stmt :=
  .seqn #[.initialization ⟨"$c11", .map (.int .uint64) (.defined ⟨"main.Index"⟩)⟩,
          .makeMap (.var "$c11") (.int .uint64) (.defined ⟨"main.Index"⟩) none,
          .mapAssign (.var "$c11") (.intLit 1 .uint64) (.intLit 12 .uint64)
            (.int .uint64) (.defined ⟨"main.Index"⟩)]

def okCallSeq : Stmt :=
  .seqn #[.initialization ⟨"$c12", .int .uint64⟩,
          .call #[.var "$c12"] ⟨"run"⟩ #[.var "$c10", .var "$c11"]]

def okResSeq : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c12"), .returnStmt]

theorem oneKnownImpl_body_eq :
    oneKnownImpl.body = .block #[] #[okCfgSeq, okAckSeq, okCallSeq, okResSeq] :=
  rfl

/-- `var stk [7]uint64` — the on-stack scratch array's zero value, the
declaration's default (`majority.go`'s "use an on-stack slice to keep us
off the heap" trick, verbatim in the pin). -/
def stkZero : GoValue :=
  .array #[.int 0 .uint64, .int 0 .uint64, .int 0 .uint64, .int 0 .uint64,
           .int 0 .uint64, .int 0 .uint64, .int 0 .uint64]

/-- The same array after the single voter's index has been written at
slot 0 — the state `slices.Sort` then sorts (over a length-1 window, so
it is the sorted image too). -/
def stkOne (v : Int) : GoValue :=
  .array #[.int v .uint64, .int 0 .uint64, .int 0 .uint64, .int 0 .uint64,
           .int 0 .uint64, .int 0 .uint64, .int 0 .uint64]

/-- The declaration default at `[7]uint64`, computed. -/
theorem defaultValue_stk (σ : ExecState) :
    defaultValue σ (.array 7 (.int .uint64)) = .ok stkZero := by
  simp only [defaultValue, defaultValueFuel, typeResolutionFuel, stkZero,
    Bind.bind, Except.bind]
  rfl

/-! The concrete cells the `sortSlice` witness sorts: a 3-element `uint64`
backing array, unsorted, and its sorted image. -/

def sortOldCell : HeapCell :=
  ⟨some (.array 3 (.int .uint64)),
   .array #[.int 3 .uint64, .int 1 .uint64, .int 2 .uint64]⟩

def sortNewCell : HeapCell :=
  ⟨some (.array 3 (.int .uint64)),
   .array #[.int 1 .uint64, .int 2 .uint64, .int 3 .uint64]⟩

end QuorumPin

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-! ## Non-vacuity witnesses, on the pinned lowering -/

/-- **Witness for `wp_map_range_snapshot`** on the REAL voter loop
(`QuorumPin.rangeStmt`, `rfl`-projected out of the pin): dispatch the
range, load `c`, snapshot its data cell — landing exactly on the
`mapIterK` that `Laws/Range`'s nondeterministic law consumes. Premise-free
beyond the environment resolution and the two owned cells. -/
theorem wp_map_range_snapshot_committed {ca mba : Addr}
    {entries : Array (GoValue × GoValue)} {env k}
    (hres : LocalEnv.lookup env "c" = some (.base ca)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                   .mapData entries⟩ : HeapCell)
      ∗ (ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                   .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                       .mapData entries⟩ : HeapCell)
          -∗ WP (Config.next (.mapIterK (some "id") none (.int .uint64)
                (.defined ⟨"struct{}"⟩) QuorumPin.rangeBody entries env k))
              @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.rangeStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hm, Hcont⟩
  rw [QuorumPin.rangeStmt_eq]
  iapply wp_map_range_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr1
  iapply (wp_eval_var (cell := ⟨some (.defined ⟨"main.MajorityConfig"⟩),
    .map ⟨some (.base mba)⟩⟩) hres)
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply wp_map_range_snapshot
  isplitl [Hm]
  · iexact Hm
  iintro Hm
  iapply Hcont $$ [$Hc $Hm]

/-- **Witness for `wp_sort_slice`** (and for `wp_stmt_op_first`) on the
REAL `slices.Sort(srt)` statement of the pinned `CommittedIndex`: the
whole statement walk — plan dispatch, the `srt` load, the sort step — on a
concrete 3-element `uint64` backing array, `[3,1,2] ↦ [1,2,3]`. Every
premise is discharged by computation; the sort's `happly` is the machine's
own `applyStmtOp` run. -/
theorem wp_sort_slice_srt {sa ba : Addr} {env k}
    (hres : LocalEnv.lookup env "srt" = some (.base sa)) :
    sa.id ↦ (⟨some (.slice (.int .uint64)),
              .slice ⟨some (.base ba), 0, 3, 3⟩⟩ : HeapCell)
      ∗ ba.id ↦ QuorumPin.sortOldCell
      ∗ (sa.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base ba), 0, 3, 3⟩⟩ : HeapCell)
          ∗ ba.id ↦ QuorumPin.sortNewCell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.sortStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hs, Hb, Hcont⟩
  rw [QuorumPin.sortStmt_eq]
  iapply (wp_stmt_op_first (op := .sortSlice (.int .uint64)) (nt := 0)
    (e := .var "srt") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcs1
  iapply (wp_eval_var (cell := ⟨some (.slice (.int .uint64)),
    .slice ⟨some (.base ba), 0, 3, 3⟩⟩) hres)
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply (wp_sort_slice (a := ba) (oldcell := QuorumPin.sortOldCell)
    (newcell := QuorumPin.sortNewCell)
    (happly := by
      intro σ ch _ht hlook
      have n1 : IntKind.uint64.normalize 1 = 1 := by rfl
      have n2 : IntKind.uint64.normalize 2 = 2 := by rfl
      have n3 : IntKind.uint64.normalize 3 = 3 := by rfl
      simp [applyStmtOp, valueAsSlice, validateSlice, sliceIndexLoc, loadLoc,
        hlook, QuorumPin.sortOldCell, QuorumPin.sortNewCell,
        heap_lookup_set_base_self, Bind.bind, Except.bind, List.range',
        List.forIn_cons, List.forIn_nil, arrayGet, arrayIndexNat, storeLoc,
        arraySet, coerceStoredValue, normalizeValueForTy,
        normalizeValueForTyFuel, typeResolutionFuel, normalizeListWith,
        sortLe, insertLe,
        heap_set_set_of_lookup hlook, Functor.map, Except.map, n1, n2, n3]))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  iapply Hcont $$ [$Hs $Hb]

/-- **Witness for `wp_map_lookup`** (and for the target/plain operand
shifts) on the REAL `idx, ok := m[id]` of the pinned
`main.mapAckIndexer.AckedIndex`: the whole statement walk on a ONE-ENTRY
`uint64 → Index` map, key present, the stored index delivered with
`ok = true`.

Generic in the entry (`q ↦ v`, any representable `uint64`s) and in the
data cell's declared type — deliberately, per the standing
over-specialization check: the earlier form hard-coded `3 ↦ 12` and a
`some (.map …)`-typed data cell, neither of which is a property of Go.
`makeMap` allocates the data cell with NO declared type, so a walk over
the real driver could not have used the pinned-type version at all.

FAITHFUL TO THE PIN as of the `σ.types` pin (quorum pilot phase 4): the
`idx` target cell is declared `.defined main.Index`, exactly as the
lowering declares it — the store's coercion at that named type resolves
through `σ.types`, dischargeable now that the ghost state pins it.

**Generalized twice, 2026-08-01 (proof-automation arc, phases 3 and 4)**:
first from a ONE-ENTRY receiver map to an ARBITRARY entry array plus a
`hpair` premise naming the lookup's answer, then (phase 4) from a FOUND
key to the comma-ok answer `(v, b)` at an arbitrary `b` — a voter with no
`AckedIndexer` entry is Go's "has not reported yet" and the `∀`-config
theorem must walk that iteration too (`hpair` then reads
`(defaultValue Index, false)`). Neither is a property of Go; both were
artefacts of the walks that came first — the machine's own computation, in the
`wp_assign_store`/`hstore` style. The one-entry map was not a property of
Go but of the n = 1 walk: at any config with more than one voter the
`AckedIndexer` holds several entries and the SAME statement must be
walked with the key found at an arbitrary position. `hpair` is exactly
`wp_map_lookup`'s, so the generalization adds no new obligation shape.

NOT in the `@[go_walk_law]` table, deliberately: its `hpair` is a
human-supplied semantic fact, exactly like `wp_map_iter_inv`'s invariant,
and a registered law whose premise happens to sit in the ambient context
would be discharged by `go_walk_side`'s `assumption` and fire where the
walk should hand back. The one-entry SPECIALIZATION below is the
registered law (its premises are all `rfl`/pin facts), and it is derived
from this one. -/
theorem wp_map_lookup_ackedIndex_entries {ma ida mba ta oa : Addr}
    {mty : Option Ty}
    {entries : Array (GoValue × GoValue)} {q v : Int} {b : Bool} {env k}
    (htypes : GoCoreGS.types GF = GoldenQuorum.quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v)
    (hpair : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base mba) = some ⟨mty, .mapData entries⟩ →
      mapLookupValue σ ⟨some (.base mba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int v .uint64, b))
    (hm : LocalEnv.lookup env "m" = some (.base ma))
    (hid : LocalEnv.lookup env "id" = some (.base ida))
    (hidx : LocalEnv.lookup env "idx" = some (.base ta))
    (hok : LocalEnv.lookup env "ok" = some (.base oa)) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ oa.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                   .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
          ∗ mba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩ : HeapCell)
          ∗ oa.id ↦ (⟨some .bool, .bool b⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.mapLookupStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hm, Hid, Hmb, Ht, Ho, Hcont⟩
  rw [QuorumPin.mapLookupStmt_eq]
  iapply (wp_stmt_op_first (op := .mapLookup (.int .uint64) (.defined ⟨"main.Index"⟩))
    (nt := 2) (e := .ref "idx") (rest := [.ref "ok", .var "m", .var "id"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm1
  iapply (wp_eval_ref hidx)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm2
  iapply (wp_stmt_op_shift_target (loc := .base ta) (by simp) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm3
  iapply (wp_eval_ref hok)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm4
  iapply (wp_stmt_op_shift_target (loc := .base oa) (by simp) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm5
  iapply (wp_eval_var (cell := ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
    .map ⟨some (.base mba)⟩⟩) hm)
  isplitl [Hm]
  · iexact Hm
  iintro Hm
  iapply (wp_stmt_op_shift_plain (by simp))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm6
  iapply (wp_eval_var (cell := ⟨some (.int .uint64), .int q .uint64⟩) hid)
  isplitl [Hid]
  · iexact Hid
  iintro Hid
  iapply (wp_map_lookup (mba := mba) (ta := ta) (oa := oa) (mty := mty)
    (entries := entries)
    (key := .int q .uint64) (val := .int v .uint64) (b := b)
    (tcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell' := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (ocell := ⟨some .bool, .bool false⟩)
    (ocell' := ⟨some .bool, .bool b⟩)
    (hkey := fun σ _ht => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, hq, typeResolutionFuel])
    (hpair := hpair)
    (hstoret := fun σ ht hl => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hl ⊢
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, hv, Bind.bind, Except.bind])
    (hstoreo := fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  isplitl [Hmb]
  · iexact Hmb
  isplitl [Ht]
  · iexact Ht
  isplitl [Ho]
  · iexact Ho
  iintro ⟨Hmb, Ht, Ho⟩
  iapply Hcont $$ [$Hm $Hid $Hmb $Ht $Ho]

/-- **The ONE-ENTRY specialization — the registered law.** Its `hpair` is
`mapLookupValue_singleton`, so every premise is a pin fact or a
normalization the walk can discharge mechanically; that is what makes it
safe to register. The n = 1 summit walk uses exactly this instance and its
statement is unchanged by the 2026-08-01 generalization above. -/
@[go_walk_law]
theorem wp_map_lookup_ackedIndex {ma ida mba ta oa : Addr} {mty : Option Ty}
    {q v : Int} {env k}
    (htypes : GoCoreGS.types GF = GoldenQuorum.quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v)
    (hm : LocalEnv.lookup env "m" = some (.base ma))
    (hid : LocalEnv.lookup env "id" = some (.base ida))
    (hidx : LocalEnv.lookup env "idx" = some (.base ta))
    (hok : LocalEnv.lookup env "ok" = some (.base oa)) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ oa.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                   .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
          ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩ : HeapCell)
          ∗ oa.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.mapLookupStmt env k) @ s ; E {{ Φ }} :=
  wp_map_lookup_ackedIndex_entries htypes hq hv
    (fun σ _ht hl => mapLookupValue_singleton σ hl) hm hid hidx hok

/-- **Witness for `wp_make_slice`** (and for the allocating apply core) on
the REAL `$c2 = make([]uint64, n)` of the pinned `CommittedIndex` — the
branch the on-stack scratch array normally avoids. At `n = 1`: the backing
array `[1]uint64` is allocated at a machine-chosen address and a slice
over it is stored in `$c2`. Every premise is discharged by computation. -/
theorem wp_make_slice_c2 {c2a na : Addr} {env k}
    (hres : LocalEnv.lookup env "$c2" = some (.base c2a))
    (hn : LocalEnv.lookup env "n" = some (.base na)) :
    c2a.id ↦ (⟨some (.slice (.int .uint64)),
               .slice ⟨none, 0, 0, 0⟩⟩ : HeapCell)
      ∗ na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ iprop(∀ fa : Addr,
          fa.id ↦ (⟨some (.array 1 (.int .uint64)),
                    .array #[.int 0 .uint64]⟩ : HeapCell)
            ∗ c2a.id ↦ (⟨some (.slice (.int .uint64)),
                         .slice ⟨some (.base fa), 0, 1, 1⟩⟩ : HeapCell)
            ∗ na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell) -∗
          WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.ciMakeSliceStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hc2, Hn, Hcont⟩
  rw [QuorumPin.ciMakeSliceStmt_eq]
  iapply (wp_stmt_op_first (op := .makeSlice (.int .uint64) false) (nt := 1)
    (e := .ref "$c2") (rest := [.var "n"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hm1
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hm2
  iapply (wp_stmt_op_shift_target (loc := .base c2a) (by simp) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hm3
  iapply (wp_eval_var (a := na) (cell := ⟨some (.int .int), .int 1 .int⟩) hn)
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply (wp_make_slice (elem := .int .uint64) (a := c2a) (n := 1)
    (backing := .array #[.int 0 .uint64])
    (newcell := fun fa => ⟨some (.slice (.int .uint64)),
                           .slice ⟨some (.base fa), 0, 1, 1⟩⟩)
    (hbacking := fun σ _ht => by
      simp [buildDefaultArrayValue, buildArrayValue, defaultValue,
        defaultValueFuel, typeResolutionFuel, Bind.bind, Except.bind])
    (oldcell := ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  isplitl [Hc2]
  · iexact Hc2
  iintro %fa ⟨Hfa, Hc2⟩
  iapply Hcont $$ %fa [$Hfa $Hc2 $Hn]

/-- **Witness for `wp_call_dynamic_enter₂`** on the REAL interface call
`l.AckedIndex(id)` of the pinned `CommittedIndex`: the callsite names the
ANCHOR `main.AckedIndexer.AckedIndex` (a bodiless `Func`), the receiver
arrives as an interface box with dynamic type
`.defined main.mapAckIndexer`, and ONE step redirects to
`main.mapAckIndexer.AckedIndex` with the receiver UNBOXED
(`needsDeref = false`), allocates the two parameter cells (normalized at
`.defined main.mapAckIndexer` and `uint64`) and the two result cells
(`$res0 : main.Index` defaulted to `0`, `$res1 : bool` to `false`), and
enters the implementation body.

EVERY premise is discharged by computation against `quorumLowered`; the
only external hypotheses are the three ghost-state pins. This is the law
the pre-`types`-pin ghost state made unstateable: `bindParams` normalizes
at `.defined main.mapAckIndexer` and `allocDecls` defaults at
`.defined main.Index`, both `TypeEnv.lookup σ.types` resolutions. -/
@[go_walk_law]
theorem wp_call_dynamic_enter_ackedIndex {mba : Addr} {n : Int}
    {locs : List Loc} {env k}
    (hprog : GoCoreGS.prog GF = GoldenQuorum.quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = GoldenQuorum.quorumLowered.methods)
    (htypes : GoCoreGS.types GF = GoldenQuorum.quorumLowered.typeDefs.toList) :
    iprop(∀ a₀ : Addr, ∀ a₁ : Addr, ∀ a₂ : Addr, ∀ a₃ : Addr,
        a₀.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ a₁.id ↦ (⟨some (.int .uint64),
                      .int (IntKind.uint64.normalize n) .uint64⟩ : HeapCell)
          ∗ a₂.id ↦ (⟨some (.defined ⟨"main.Index"⟩),
                      .int 0 .uint64⟩ : HeapCell)
          ∗ a₃.id ↦ (⟨some .bool, .bool false⟩ : HeapCell) -∗
        WP (Config.exec QuorumPin.ackedIndexImpl.body
              [[("$res1", Loc.base a₃), ("$res0", Loc.base a₂),
                ("id", Loc.base a₁), ("m", Loc.base a₀)]]
              (.frame locs [Loc.base a₂, Loc.base a₃] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.int n .uint64)
            (.callArgsK ⟨"main.AckedIndexer.AckedIndex"⟩ locs
              [.interface (.defined ⟨"main.mapAckIndexer"⟩)
                (.map ⟨some (.base mba)⟩)] [] env k)) @ s ; E {{ Φ }} :=
  wp_call_dynamic_enter₂
    (anchor := QuorumPin.ackedIndexAnchor) (concrete := QuorumPin.ackedIndexImpl)
    (recv := .map ⟨some (.base mba)⟩)
    (hfind := by rw [hprog]; exact QuorumPin.ackedIndexAnchor_find)
    (hanchor := QuorumPin.ackedIndexAnchor_args)
    (hargs := QuorumPin.ackedIndexImpl_args)
    (hres := QuorumPin.ackedIndexImpl_results)
    (hrid := by decide)
    (hdisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?, methodRecvInterfaceName?,
        resolveDefinedAliases, resolveDefinedAliasesFuel,
        concreteMethodForDynamic?, methodRecvDynamicTy?, canonicalTy,
        canonicalTyFuel, typeResolutionFuel, QuorumPin.quorumMethods_eq,
        QuorumPin.typeEnv_mapAckIndexer,
        QuorumPin.ackedIndexAnchor_id, QuorumPin.ackedIndexImpl_find,
        QuorumPin.beq_mapAckIndexer_self,
        Bind.bind, Except.bind])
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel])
    (hdef₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index])
    (hdef₁ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])

/-- **Witness for `wp_call_enter₂`** (the STATIC two-argument/two-result
frame entry) on the REAL `main.mapAckIndexer.AckedIndex` of the pinned
lowering, called on a CONCRETE receiver (no interface box, so
`dynamicDispatch?` must answer `none` — which it does because the
method's recorded receiver `.defined main.mapAckIndexer` resolves to a
map type, not an interface: the `methodRecvInterfaceName?` gate).

This is the entry the `GoFuncSpec2` discharge walks, and it is the exact
complement of `wp_call_dynamic_enter_ackedIndex`: same method, same
parameter/result cells, the other dispatch answer. Every premise is
discharged by computation against `quorumLowered`; the only external
hypotheses are the three ghost-state pins. -/
@[go_walk_law]
theorem wp_call_enter_ackedIndexImpl {mba : Addr} {n : Int}
    {locs : List Loc} {env k}
    (hprog : GoCoreGS.prog GF = GoldenQuorum.quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = GoldenQuorum.quorumLowered.methods)
    (htypes : GoCoreGS.types GF = GoldenQuorum.quorumLowered.typeDefs.toList) :
    iprop(∀ a₀ : Addr, ∀ a₁ : Addr, ∀ a₂ : Addr, ∀ a₃ : Addr,
        a₀.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ a₁.id ↦ (⟨some (.int .uint64),
                      .int (IntKind.uint64.normalize n) .uint64⟩ : HeapCell)
          ∗ a₂.id ↦ (⟨some (.defined ⟨"main.Index"⟩),
                      .int 0 .uint64⟩ : HeapCell)
          ∗ a₃.id ↦ (⟨some .bool, .bool false⟩ : HeapCell) -∗
        WP (Config.exec QuorumPin.ackedIndexImpl.body
              [[("$res1", Loc.base a₃), ("$res0", Loc.base a₂),
                ("id", Loc.base a₁), ("m", Loc.base a₀)]]
              (.frame locs [Loc.base a₂, Loc.base a₃] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.int n .uint64)
            (.callArgsK ⟨"main.mapAckIndexer.AckedIndex"⟩ locs
              [.map ⟨some (.base mba)⟩] [] env k)) @ s ; E {{ Φ }} :=
  wp_call_enter₂
    (func := QuorumPin.ackedIndexImpl)
    (hfind := by rw [hprog]; exact QuorumPin.ackedIndexImpl_find)
    (hargs := QuorumPin.ackedIndexImpl_args)
    (hres := QuorumPin.ackedIndexImpl_results)
    (hrid := by decide)
    (hnodisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?, methodRecvInterfaceName?,
        resolveDefinedAliases, resolveDefinedAliasesFuel,
        QuorumPin.quorumMethods_eq, QuorumPin.typeEnv_mapAckIndexer,
        Bind.bind, Except.bind]
      -- the receiver resolves to a MAP type, never `.interface`, so both
      -- arms of the remaining match answer "no dynamic dispatch".
      split <;> rfl)
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel])
    (hdef₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index])
    (hdef₁ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])

end

/-! ## The regression guard on the `σ.types` pin

Kernel-checked demonstration that frame entry into this program depends on
`σ.types`: the SAME value at the SAME declared type normalizes to `.ok`
under the program's type environment and to `unsupported` under an empty
one — two states that can agree on `functions` and `methods`.
`bindParams` (every quorum entry point has a `.defined`-typed parameter),
`allocDecls` (`$res0 : main.Index`), and `concreteMethodForDynamic?`
(receiver canonicalization) all route through it. This is why
`GoCoreGS.types` exists; delete the pin and the laws above become
vacuous, which is exactly what this theorem makes visible. -/
theorem typeEnv_pin_is_load_bearing :
    TypeEnv.lookup GoldenQuorum.quorumLowered.typeDefs.toList ⟨"main.Index"⟩
        = some (.defined (.int .uint64))
      ∧ (normalizeValueForTy ({ types := [] } : ExecState)
          (.defined ⟨"main.Index"⟩) (.int 5 .uint64)).toOption = none
      ∧ (normalizeValueForTy
          ({ types := [(⟨"main.Index"⟩, .defined (.int .uint64))] } : ExecState)
          (.defined ⟨"main.Index"⟩) (.int 5 .uint64)).toOption
        = some (.int 5 .uint64) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp +decide [normalizeValueForTy, normalizeValueForTyFuel, TypeEnv.lookup,
      typeResolutionFuel, Except.toOption]
  · have n5 : IntKind.uint64.normalize 5 = 5 := by rfl
    simp +decide [normalizeValueForTy, normalizeValueForTyFuel, TypeEnv.lookup,
      typeResolutionFuel, Except.toOption, n5]


end GoLean.Iris
