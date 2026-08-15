import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.Pure

/-!
# WordCount — Machine

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Machine-layer configurations

Transcribed from the machine (probe-verified against a concrete run;
every raw segment below re-checks the transcription by `rfl`). Address
layout at the canonical placement (`base = 1`, `na = 2`): 0 =
`$callres`, 1 = the words backing array, 2 = the parameter `words`
(the handle), 3 = `$res0`, 4 = `$c0`, 5 = the map DATA cell, 6 =
`counts`, 7 = `i`, 8 = `$forFirst` — then the SYMBOLIC region: two
fresh `$c1`/`$c2` cells per counting iteration (9 + 2k), `best` at
`9 + 2·len`, one fresh `c` value cell per range iteration. -/

abbrev tU64 : Ty := .int .uint64
abbrev tMap : Ty := .map tU64 tU64

abbrev wcCountBody : Stmt :=
  .block
    #[]
    #[.seqn
        #[.initialization { id := "$c1", typ := tMap },
          .assign (.var "$c1") (.var "counts")],
      .seqn
        #[.initialization { id := "$c2", typ := tU64 },
          .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))],
      .mapAssign (.var "$c1") (.var "$c2")
        (.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
          (.intLit 1 .uint64))
        tU64 tU64]

abbrev wcWhileBody : Stmt :=
  .block
    #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "i")
          (.length (.var "words") (some (.slice tU64))))
        (.seqn #[])
        .breakStmt,
      wcCountBody]

abbrev wcRangeBody : Stmt :=
  .block
    #[]
    #[.ifThenElse (.greaterCmp (.var "c") (.var "best"))
        (.block
          #[]
          #[.seqn #[.assign (.var "best") (.var "c")]])
        (.seqn #[])]

abbrev wcMapRangeStmt : Stmt :=
  .mapRange none (some "c") (.var "counts") tU64 tU64 wcRangeBody

abbrev bestSeqn : Stmt :=
  .seqn
    #[.initialization { id := "best", typ := tU64 },
      .assign (.var "best") (.intLit 0 .uint64)]

abbrev retSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "best"), .returnStmt]

abbrev asgnC1 : Stmt := .assign (.var "$c1") (.var "counts")
abbrev seqnC2 : Stmt :=
  .seqn
    #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))]
abbrev mapAsgnStmt : Stmt :=
  .mapAssign (.var "$c1") (.var "$c2")
    (.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64))
    tU64 tU64

/-! ### Environments and continuations -/

def sc0 : Scope := [("$res0", .base ⟨3⟩), ("words", .base ⟨2⟩)]
def sc1 : Scope := [("counts", .base ⟨6⟩), ("$c0", .base ⟨4⟩)]
def envR0 : LocalEnv := [sc1, sc0]
def envB : LocalEnv :=
  [[("$forFirst", .base ⟨8⟩)], [("i", .base ⟨7⟩)], sc1, sc0]
def envB1 : LocalEnv := [[("i", .base ⟨7⟩)], sc1, sc0]
def env2 : LocalEnv := [] :: envB
def env3 : LocalEnv := [] :: env2
def u1Env (na : Nat) : LocalEnv := [("$c1", .base ⟨na⟩)] :: env2
def uEnv (na : Nat) : LocalEnv :=
  [("$c2", .base ⟨na + 1⟩), ("$c1", .base ⟨na⟩)] :: env2

def frameK : Cont :=
  .frame [(.chain [], [.ref "$callres"])] [[("$callres", .base ⟨0⟩)]]
    [.base ⟨3⟩] [] .stop false
def tailB : Cont :=
  .seq [] envB (.seq [] envB1
    (.seq [bestSeqn, wcMapRangeStmt, retSeqn] envR0 frameK))
/-- The counting-loop head configuration. -/
def headC : Config :=
  .exec (.while (.boolLit true) wcWhileBody) envB tailB
def loopKC : Cont := .loop (.boolLit true) wcWhileBody envB tailB
def bodyTail : Cont := .seq [wcCountBody] env2 loopKC
/-- The exit test's delivery continuation (segment split point). -/
def cmpContC : Cont := .ifK (.seqn #[]) .breakStmt env2 bodyTail
/-- The `len(words)` apply point inside the exit test. -/
def lenK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] env2
    (.strictK .lessCmp [.int iv .int] [] env2 cmpContC)
def postBodyK : Cont := .seq [] env2 loopKC

/-! ### Heap cells and the phase-C state family -/

abbrev u64cell (v : Int) : HeapCell :=
  ⟨some tU64, .int v .uint64⟩
abbrev intcell (v : Int) : HeapCell :=
  ⟨some (.int .int), .int v .int⟩
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev handleCell (n : Nat) : HeapCell :=
  ⟨some (.slice tU64), .slice ⟨some (.base ⟨1⟩), 0, n, n⟩⟩
abbrev sliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨1⟩), 0, n, n⟩
abbrev mhCell : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨5⟩)⟩⟩
abbrev mdCell (kvs : List (Int × Nat)) : HeapCell :=
  ⟨none, .mapData (toEntries kvs)⟩

/-- The nine concrete front cells during the counting loop. -/
def frontC (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell 0), (.base ⟨1⟩, arrCell L ws),
   (.base ⟨2⟩, handleCell L), (.base ⟨3⟩, u64cell 0),
   (.base ⟨4⟩, mhCell), (.base ⟨5⟩, mdCell kvs),
   (.base ⟨6⟩, mhCell), (.base ⟨7⟩, intcell iv), (.base ⟨8⟩, bcell ff)]

/-- The phase-C state: concrete front + the symbolic dead-cell tail. -/
def σC (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (iv : Int) (ff : Bool) (dead : Heap) (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontC L ws kvs iv ff ++ dead, nextAddr := na }

/-- **The choice-pick step** (§10b): at a nonempty snapshot, ONE choice
is consumed (`idx < size` from `Choices.consume`'s `% bound` contract),
the picked entry's VALUE cell is freshly allocated at the current
`nextAddr`, and the entry is erased. -/
theorem stepFn_pick {σ : ExecState} {rem : List (Int × Nat)}
    {idx : Nat} {ch ch' : Choices} {body : Stmt} {env : LocalEnv} {k : Cont}
    (hconsume : Choices.consume ch rem.length = (idx, ch'))
    (hidx : idx < rem.length)
    {p : Int × Nat} (hp : rem[idx]? = some p)
    (hv : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    stepFn σ
      (.next (.mapIterK none (some "c") tU64 tU64 body (toEntries rem) env k))
      ch
      = .ok (.exec body (env.pushScope.declare "c" (.base ⟨σ.nextAddr⟩))
          (.mapIterK none (some "c") tU64 tU64 body
            (toEntries (rem.eraseIdx idx)) env k),
        { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some tU64, .int (p.2 : Int) .uint64⟩,
            nextAddr := σ.nextAddr + 1 },
        ch') := by
  have hne : (toEntries rem).isEmpty = false := by
    cases rem with
    | nil => cases hidx
    | cons q rest => rfl
  have hsz : (toEntries rem).size = rem.length := toEntries_size rem
  have hget : (toEntries rem)[idx]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) :=
    toEntries_getElem? rem idx hp
  have hidx' : idx < (toEntries rem).size := by rw [hsz]; exact hidx
  simp only [stepFn, hne, Bool.false_eq_true, if_false]
  split
  · rename_i hnone
    rw [hsz, hconsume] at hnone
    simp only at hnone
    rw [hget] at hnone
    cases hnone
  · rename_i key value hsome
    rw [hsz, hconsume] at hsome
    simp only at hsome
    rw [hget] at hsome
    injection hsome with h1
    injection h1 with hk hv2
    subst hk
    subst hv2
    simp only [bindIterVars, Bind.bind, Except.bind, pure, Except.pure]
    rw [show normalizeValueForTy σ tU64 (.int (p.2 : Int) .uint64)
        = .ok (.int (p.2 : Int) .uint64) from by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        hv]]
    simp only [Bind.bind, Except.bind, pure, Except.pure, ExecState.alloc,
      ExecState.freshLoc, hsz, hconsume, toEntries_eraseIdx rem idx hidx']

/-! ## The placement-generic counting-loop composition (consolidation
slice 2026-08-13, worklist item 1)

The counting loop's COMPOSITION layer, stated ONCE over an abstract
state family `S`, abstract placement environments/continuations, and
the per-segment transition facts as hypotheses. Design informed by the
storm diagnosis (`docs/2026-08-13_consolidation-slice.md` §1): in this
layer the unifier only ever matches the VARIABLE `S`, and every
instantiation site discharges a hypothesis whose type pins all
intermediate states/configurations (variant E's fix made structural) —
the storm class cannot ignite here. The two consumers are the
canonical placement (`wc_count_iter`/`wc_count_loop` below, retrofitted
to instantiations) and the harness placement (`wcH_count_iter`/
`wcH_count_loop`, the former gap-G1 blocker). Full segment
α-abstraction was considered and REJECTED (recorded): per-placement
`rfl` segments are cheap and were never the storm's site; the
composition + the conditioned state-massage discharges were. -/

-- PROMOTED to `GoLeanProofs/StepKit.lean` (Gallery Campaign kit-gap
-- closure GAP-M2, 2026-08-15): `DeadFrom` and its two `push` lemmas
-- are pure heap algebra and now live beside the P11 append/set kit;
-- visible here via `open GoLean.Surface`.


end GoLean.Examples.WordCount
