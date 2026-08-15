import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.MapMem

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

open GoLean GoLean.GoCore GoLean.GoCore.Machine
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

-- GAP-M1 CLOSED (kit-gap closure, 2026-08-15): the binder-specialized
-- `stepFn_pick` this module carried is DELETED — the kit forms are
-- `MapMem.stepFn_pick_bind` (parameterized over both binder options,
-- allocation via `bindIterVars`) and its two corollaries
-- `stepFn_pick_value` / `stepFn_pick_novars`.

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
