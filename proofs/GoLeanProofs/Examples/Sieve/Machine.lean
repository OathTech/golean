import GoLeanProofs.Examples.SieveProgram
import GoLeanProofs.Examples.Sieve.Pure
import GoLeanProofs.SliceMem
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.Values

/-!
# Sieve — Machine: segments, loop inductions, run assembly

The machine half of the `sieve` gallery example (Gallery Campaign G1,
hard lane). Three nested loop phases over ONE growing heap:

* the ENTRY (concrete addresses 0–9: harness `n`/`$res0`/`$c2`,
  callee `n`/`$res0`, `$c0`, the `make([]bool, n+1)` BACKING cell at
  6, the `composite` handle at 7, outer `i` at 8, outer `$forFirst`
  at 9) — closed by `with_unfolding_all rfl` slabs plus one
  conditioned `makeSlice` apply at the SYMBOLIC length `n+1`;
* the OUTER marking loop — per pass that enters the `!composite[i]`
  branch the machine allocates `j` and an inner `$forFirst` at the
  CURRENT `nextAddr` (symbolic), runs the inner marking loop there,
  and retires both cells into the dead region; segments at symbolic
  addresses are conditioned kit chains (`stepFn_var`,
  `storeTarget_addr` + `stepFn_store_step`, `stepFn_init_seq` +
  `set_fresh`, `stepFn_seqn_splice`), the FibMemo footprint style;
* the COUNT loop — three more symbolic cells (`count`/`i`/
  `$forFirst`), allocation-free iterations, an accumulator invariant
  `count-cell = c + countFrom bs n i`.

Each machine loop induction lands exactly on the pure mirror's
equation lemmas (`markFrom_step/stop`, `sieveOuter_step/stop`,
`countFrom_step/stop` — NEVER unfolded, per the recorded WF pitfall),
so `sv_runs` delivers `sieveAnswer n` and the root's headline rewrites
it to `primeCount n` with `sieveAnswer_eq`.

Heap-algebra helpers (`FreshFrom`-style dead-region facts,
`lookup_set_other`/`lookup_set_self`/`set_cons_ne`/`set_cons_self`/
`set_set`) mirror the FibMemo unit's (`Examples/FibMemo/Rec.lean`) —
kit candidates; the lane owner consolidates.
-/

namespace GoLean.Examples.Sieve

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Vocabulary -/

abbrev tU : Ty := .int .uint64
abbrev tSB : Ty := .slice .bool

/-- uint64 cell -/
abbrev u64cell (v : Int) : HeapCell := ⟨some tU, .int v .uint64⟩
/-- bool cell -/
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
/-- the slice HANDLE over the backing cell at address 6, length `m` -/
def svHandle (m : Nat) : GoValue := .slice ⟨some (.base ⟨6⟩), 0, m, m⟩
/-- slice-handle cell -/
abbrev hcell (m : Nat) : HeapCell := ⟨some tSB, svHandle m⟩
/-- the BACKING cell: one `[m]bool` array holding table `bs` -/
abbrev bkcell (m : Nat) (bs : List Bool) : HeapCell :=
  ⟨some (.array m .bool), .array ⟨bs.map GoValue.bool⟩⟩

/-! ## The subject `Func`, verbatim, pinned (powmod-style abbrevs) -/

abbrev svZeroBlock : Stmt :=
  .block #[] #[.seqn #[.assign (.var "$res0") (.intLit 0 .uint64), .returnStmt]]
abbrev svGuard : Stmt :=
  .ifThenElse (.lessCmp (.var "n") (.intLit 2 .uint64)) svZeroBlock (.seqn #[])
abbrev svC0Seqn : Stmt :=
  .seqn #[.initialization { id := "$c0", typ := tSB },
          .makeSlice (.var "$c0") .bool (.add (.var "n") (.intLit 1 .uint64)) none]
abbrev svCompSeqn : Stmt :=
  .seqn #[.initialization { id := "composite", typ := tSB },
          .assign (.var "composite") (.var "$c0")]
abbrev svISeqn : Stmt :=
  .seqn #[.initialization { id := "i", typ := tU },
          .assign (.var "i") (.intLit 2 .uint64)]
abbrev svIncIf : Stmt :=
  .ifThenElse (.var "$forFirst")
    (.assign (.var "$forFirst") (.boolLit false))
    (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64)))
abbrev svInnerFlagIf : Stmt :=
  .ifThenElse (.var "$forFirst")
    (.assign (.var "$forFirst") (.boolLit false))
    (.assign (.var "j") (.add (.var "j") (.var "i")))
abbrev svOuterGuardIf : Stmt :=
  .ifThenElse (.atMostCmp (.mul (.var "i") (.var "i")) (.var "n"))
    (.seqn #[]) .breakStmt
abbrev svInnerGuardIf : Stmt :=
  .ifThenElse (.atMostCmp (.var "j") (.var "n")) (.seqn #[]) .breakStmt
abbrev svCntGuardIf : Stmt :=
  .ifThenElse (.atMostCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt
abbrev svMarkStore : Stmt :=
  .block #[]
    #[.seqn #[.assign
        (.addr (.indexAddr (.var "composite") (.var "j"))) (.boolLit true)]]
abbrev svInnerBody : Stmt :=
  .block #[] #[svInnerFlagIf, .seqn #[], svInnerGuardIf, svMarkStore]
abbrev svFF2Block : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) svInnerBody]
abbrev svJSeqn : Stmt :=
  .seqn #[.initialization { id := "j", typ := tU },
          .assign (.var "j") (.mul (.var "i") (.var "i"))]
abbrev svMarkB2 : Stmt := .block #[] #[svJSeqn, svFF2Block]
abbrev svMarkB1 : Stmt := .block #[] #[svMarkB2]
abbrev svNotIf : Stmt :=
  .ifThenElse (.not (.indexGet (.var "composite") (.var "i")))
    svMarkB1 (.seqn #[])
abbrev svOuterUser : Stmt := .block #[] #[svNotIf]
abbrev svOuterBody : Stmt :=
  .block #[] #[svIncIf, .seqn #[], svOuterGuardIf, svOuterUser]
abbrev svOuterFFBlock : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) svOuterBody]
abbrev svOuterBlock : Stmt := .block #[] #[svISeqn, svOuterFFBlock]
abbrev svCountSeqn : Stmt :=
  .seqn #[.initialization { id := "count", typ := tU },
          .assign (.var "count") (.intLit 0 .uint64)]
abbrev svCntInc : Stmt :=
  .block #[]
    #[.assign (.var "count") (.add (.var "count") (.intLit 1 .uint64))]
abbrev svCntIf : Stmt :=
  .ifThenElse (.not (.indexGet (.var "composite") (.var "i")))
    svCntInc (.seqn #[])
abbrev svCntUser : Stmt := .block #[] #[svCntIf]
abbrev svCntBody : Stmt :=
  .block #[] #[svIncIf, .seqn #[], svCntGuardIf, svCntUser]
abbrev svCntFFBlock : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) svCntBody]
abbrev svCntBlock : Stmt := .block #[] #[svISeqn, svCntFFBlock]
abbrev svEpi : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "count"), .returnStmt]

/-- The subject `Func`, transcribed in readable form (the pin below
ties it to the frontend's lowering by `rfl`). -/
def countPrimesFunc : Func :=
  { id := { key := "countPrimes" },
    args := #[{ id := "n", typ := tU }],
    results := #[{ id := "$res0", typ := tU }],
    body := .block #[]
      #[svGuard, svC0Seqn, svCompSeqn, svOuterBlock, svCountSeqn,
        svCntBlock, svEpi],
    variadic := false, wrapper := false }

/-- The lowering pin: the transcription IS the frontend's `countPrimes`. -/
theorem countPrimes_pin :
    findFunctionIn? sieveLowered.funcs ⟨"countPrimes"⟩ = some countPrimesFunc := rfl

/-! ## The post-prelude seed (hand-written here because the pinned
harness `Func` lives in the ROOT, which imports this module; the root
derives the entry equation with `derive_entry_eq` and bridges to these
by `rfl` — the two spellings are definitionally the same records) -/

/-- The harness BODY, transcribed (the root's pinned
`sieveHarnessFunc.body` reduces to exactly this). -/
def svHarnessBody : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "$c2", typ := tU },
              .call #[.var "$c2"] { key := "countPrimes" } #[.var "n"]],
      .seqn #[.assign (.var "$res0") (.var "$c2"), .returnStmt]]

/-- The machine entry's post-prelude state (argument cell 0 receives
the ALREADY-normalized `n`, result cell 1 its default). -/
def svSeed0 (n : Int) : ExecState :=
  { types := sieveLowered.typeDefs.toList,
    functions := sieveLowered.funcs,
    methods := sieveLowered.methods,
    heap := [(.base ⟨0⟩, u64cell n), (.base ⟨1⟩, u64cell 0)],
    nextAddr := 2 }

/-- The post-prelude start configuration. -/
def svC00 : Config :=
  .exec svHarnessBody [[("$res0", .base ⟨1⟩), ("n", .base ⟨0⟩)]]
    (.frame [] [] [] [] .stop false)

/-! ## Environments (transcribed from the machine's own scoping,
probe-verified against full-`repr` dumps at n = 10) -/

def hEnvH : LocalEnv :=
  [[("$c2", .base ⟨2⟩)], [("$res0", .base ⟨1⟩), ("n", .base ⟨0⟩)]]
def fEnv : LocalEnv :=
  [[("$res0", .base ⟨4⟩), ("n", .base ⟨3⟩)]]
def bEnv : LocalEnv := [] :: fEnv
def c0Env : LocalEnv := [("$c0", .base ⟨5⟩)] :: fEnv
def cEnv : LocalEnv :=
  [("composite", .base ⟨7⟩), ("$c0", .base ⟨5⟩)] :: fEnv
def iEnv : LocalEnv := [("i", .base ⟨8⟩)] :: cEnv
def oEnvIn : LocalEnv := [("$forFirst", .base ⟨9⟩)] :: iEnv
def oEnvB1 : LocalEnv := [] :: oEnvIn
def oEnvB2 : LocalEnv := [] :: oEnvB1
def mEnvB1 : LocalEnv := [] :: oEnvB2
def jEnv (a : Nat) : LocalEnv := [("j", .base ⟨a⟩)] :: mEnvB1
def inEnv (a : Nat) : LocalEnv :=
  [("$forFirst", .base ⟨a + 1⟩)] :: jEnv a
def inEnvB1 (a : Nat) : LocalEnv := [] :: inEnv a
def kEnv (b : Nat) : LocalEnv :=
  [("count", .base ⟨b⟩), ("composite", .base ⟨7⟩), ("$c0", .base ⟨5⟩)] :: fEnv
def kiEnv (b : Nat) : LocalEnv := [("i", .base ⟨b + 1⟩)] :: kEnv b
def kEnvIn (b : Nat) : LocalEnv :=
  [("$forFirst", .base ⟨b + 2⟩)] :: kiEnv b
def kEnvB1 (b : Nat) : LocalEnv := [] :: kEnvIn b
def kEnvB2 (b : Nat) : LocalEnv := [] :: kEnvB1 b

/-! ## Continuations -/

def svHEpi : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c2"), .returnStmt]
def hFrame0 : Cont := .frame [] [] [] [] .stop false
def hTailK : Cont := .seq [svHEpi] hEnvH hFrame0
/-- The `countPrimes` call frame the harness builds. -/
def svCallK : Cont :=
  .frame [(.chain [], [.ref "$c2"])] hEnvH [.base ⟨4⟩] [] hTailK false
def guardK : Cont :=
  .ifK svZeroBlock (.seqn #[]) bEnv
    (.seq [svC0Seqn, svCompSeqn, svOuterBlock, svCountSeqn, svCntBlock, svEpi]
      bEnv svCallK)
def msTailK : Cont :=
  .seq [svCompSeqn, svOuterBlock, svCountSeqn, svCntBlock, svEpi] c0Env svCallK
/-- The `makeSlice` wide-op continuation at its apply point. -/
def msK : Cont :=
  .stmtOpK (.makeSlice .bool false) 1 [.addr (.base ⟨5⟩)] [] c0Env msTailK
def postOuterK : Cont :=
  .seq [svCountSeqn, svCntBlock, svEpi] cEnv svCallK
def outerHeadTail : Cont := .seq [] oEnvIn (.seq [] iEnv postOuterK)
/-- The recurring OUTER loop-head configuration. -/
def svHeadCfg : Config :=
  .exec (.while (.boolLit true) svOuterBody) oEnvIn outerHeadTail
def outerLoopK : Cont :=
  .loop (.boolLit true) svOuterBody oEnvIn outerHeadTail
/-- The outer `i*i <= n` test's delivery continuation. -/
def outerCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt oEnvB1 (.seq [svOuterUser] oEnvB1 outerLoopK)
def notTail : Cont := .seq [] oEnvB2 (.seq [] oEnvB1 outerLoopK)
/-- The `!composite[i]` delivery continuation (outer loop). -/
def notIfK : Cont := .ifK svMarkB1 (.seqn #[]) oEnvB2 notTail
def mTail : Cont := .seq [] mEnvB1 notTail
def innerHeadTail (a : Nat) : Cont :=
  .seq [] (inEnv a) (.seq [] (jEnv a) mTail)
/-- The recurring INNER (marking) loop-head configuration; `a` is the
pass's `j`-cell address. -/
def innerHeadCfg (a : Nat) : Config :=
  .exec (.while (.boolLit true) svInnerBody) (inEnv a) (innerHeadTail a)
def innerLoopK (a : Nat) : Cont :=
  .loop (.boolLit true) svInnerBody (inEnv a) (innerHeadTail a)
/-- The inner `j <= n` test's delivery continuation. -/
def innerCmpK (a : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt (inEnvB1 a)
    (.seq [svMarkStore] (inEnvB1 a) (innerLoopK a))
def postCntK (b : Nat) : Cont := .seq [svEpi] (kEnv b) svCallK
def cntHeadTail (b : Nat) : Cont :=
  .seq [] (kEnvIn b) (.seq [] (kiEnv b) (postCntK b))
/-- The recurring COUNT loop-head configuration; `b` is the
`count`-cell address. -/
def cntHeadCfg (b : Nat) : Config :=
  .exec (.while (.boolLit true) svCntBody) (kEnvIn b) (cntHeadTail b)
def cntLoopK (b : Nat) : Cont :=
  .loop (.boolLit true) svCntBody (kEnvIn b) (cntHeadTail b)
/-- The count `i <= n` test's delivery continuation. -/
def cntCmpK (b : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt (kEnvB1 b)
    (.seq [svCntUser] (kEnvB1 b) (cntLoopK b))
def cntNotTail (b : Nat) : Cont :=
  .seq [] (kEnvB2 b) (.seq [] (kEnvB1 b) (cntLoopK b))
/-- The count `!composite[i]` delivery continuation. -/
def cntNotIfK (b : Nat) : Cont :=
  .ifK svCntInc (.seqn #[]) (kEnvB2 b) (cntNotTail b)

/-! ## State families -/

/-- The single state former (footprint style): the sieve program at
heap `h`, next address `na`. -/
def svSt (h : Heap) (na : Nat) : ExecState :=
  { types := sieveLowered.typeDefs.toList,
    functions := sieveLowered.funcs,
    methods := sieveLowered.methods,
    heap := h, nextAddr := na }

/-- Guard-phase state: harness cells + callee `n`/`$res0`. -/
def svStG (n₀ nv : Int) : ExecState :=
  svSt [(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell 0),
        (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
        (.base ⟨4⟩, u64cell 0)] 5
/-- Pre-`makeSlice` state: `$c0` declared, still the nil slice. -/
def svStE1 (n₀ nv : Int) : ExecState :=
  svSt [(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell 0),
        (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
        (.base ⟨4⟩, u64cell 0),
        (.base ⟨5⟩, ⟨some tSB, .slice ⟨none, 0, 0, 0⟩⟩)] 6
/-- Post-`makeSlice` state: backing at 6, handle in `$c0`. -/
def svStE2 (n₀ nv : Int) (m : Nat) (bs : List Bool) : ExecState :=
  svSt [(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell 0),
        (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
        (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, hcell m),
        (.base ⟨6⟩, bkcell m bs)] 7

/-- The concrete 10-cell heap FRONT of the loop phases. -/
def svFront (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell 0),
   (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
   (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, hcell m),
   (.base ⟨6⟩, bkcell m bs), (.base ⟨7⟩, hcell m),
   (.base ⟨8⟩, u64cell iv), (.base ⟨9⟩, bcell ff)]

/-- Outer-loop state: concrete front, abstract dead tail. -/
def svStO (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (ff : Bool) (dead : Heap) (na : Nat) : ExecState :=
  svSt (svFront n₀ nv m bs iv ff ++ dead) na

/-- The two live cells of a marking pass at base `a`. -/
def mLive (a : Nat) (jv : Int) (f2 : Bool) : Heap :=
  [(.base ⟨a⟩, u64cell jv), (.base ⟨a + 1⟩, bcell f2)]

/-- Marking-pass state: outer front (flag already false), dead tail,
then the pass's `j`/`$forFirst` cells at `a`/`a+1`. -/
def svStM (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (a : Nat) (jv : Int) (f2 : Bool) : ExecState :=
  svSt (svFront n₀ nv m bs iv false ++ (dead ++ mLive a jv f2)) (a + 2)

/-- The three live cells of the count phase at base `b`. -/
def kLive (b : Nat) (cv iv2 : Int) (f3 : Bool) : Heap :=
  [(.base ⟨b⟩, u64cell cv), (.base ⟨b + 1⟩, u64cell iv2),
   (.base ⟨b + 2⟩, bcell f3)]

/-- Count-loop state: front (outer `i` parked at `ivo`, flag false),
dead tail, then `count`/`i`/`$forFirst` at `b`/`b+1`/`b+2`. -/
def svStK (n₀ nv : Int) (m : Nat) (bs : List Bool) (ivo : Int)
    (dead : Heap) (b : Nat) (cv iv2 : Int) (f3 : Bool) : ExecState :=
  svSt (svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3)) (b + 3)

/-- The terminal front: result cells 1/2/4 hold the answer. -/
def svFrontFin (n₀ nv ans : Int) (m : Nat) (bs : List Bool)
    (ivo : Int) : Heap :=
  [(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell ans),
   (.base ⟨2⟩, u64cell ans), (.base ⟨3⟩, u64cell nv),
   (.base ⟨4⟩, u64cell ans), (.base ⟨5⟩, hcell m),
   (.base ⟨6⟩, bkcell m bs), (.base ⟨7⟩, hcell m),
   (.base ⟨8⟩, u64cell ivo), (.base ⟨9⟩, bcell false)]

/-- The terminal state of the `n ≥ 2` pipeline. -/
def svStFin (n₀ nv ans : Int) (m : Nat) (bs : List Bool)
    (ivo : Int) (dead : Heap) (b : Nat) (cv iv2 : Int) : ExecState :=
  svSt (svFrontFin n₀ nv ans m bs ivo ++ (dead ++ kLive b cv iv2 false))
    (b + 3)

/-! ## Heap-algebra helpers — PROMOTED (WP arc s2 item 1): the five
private mirrors that sat here (`lookup_set_other`, `lookup_set_self`,
`set_cons_ne`, `set_cons_self`, `lookup_cons_self`) are StepKit's
footprint battery now; call sites resolve through
`open GoLean.Surface`. -/

/-- The 10-cell front is fresh at and above address 10. -/
private theorem front_lookup_none {n₀ nv : Int} {m : Nat} {bs : List Bool}
    {iv : Int} {ff : Bool} {x : Nat} (hx : 10 ≤ x) :
    Heap.lookup (svFront n₀ nv m bs iv ff) (.base ⟨x⟩) = none :=
  -- WP arc s2 item 5: the 10-link chain replaced by the kit's
  -- executable front bound.
  lookup_of_keysBelow (k := 10) (by rfl) hx

/-- Reading the mapped-to-`GoValue` BOOL backing at an in-range index
(GAP-WITNESS: mirrors `SliceMem.getElem?_mapU` at `Bool`). -/
theorem getElem?_mapB (l : List Bool) (k : Nat) (hk : k < l.length) :
    (⟨l.map GoValue.bool⟩ : Array GoValue)[k]?
      = some (.bool (l.getD k false)) := by
  simp [List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]

/-- Normalizing at `.bool` is the identity catch-all, so the list
normalizer is the identity — the `[]bool` mirror of `SliceMem`'s
private `normalizeListWith_u64`, with NO range hypotheses.
GAP-WITNESS (kit gap). -/
private theorem normalizeListWith_id (l : List GoValue) :
    normalizeListWith (fun x => Except.ok x) l = .ok ⟨l⟩ := by
  induction l with
  | nil => rfl
  | cons v rest ih => simp [normalizeListWith, ih, Bind.bind, Except.bind]

/-- GAP-WITNESS (kit gap): **the `[]bool` element store through an
index-chain target** (`composite[j] = true`) — mirrors
`SliceMem.storeTarget_slice_u64`; EASIER, since bool values have no
range side-conditions. -/
theorem storeTarget_slice_bool {σ : ExecState} {a : Addr}
    {off len cap i n : Nat} {ik : IntKind} {l : List Bool} {w : Bool}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨some (.array n .bool), .array ⟨l.map GoValue.bool⟩⟩)
    (hcap : len ≤ cap) (hi : i < len)
    (hsz : off + i < l.length) (hn : l.length = n) :
    storeTarget σ
      (.chain (.slice ⟨some (.base a), off, len, cap⟩) [.int (i : Nat) ik]
        [.index])
      (.bool w)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨some (.array n .bool),
           .array ⟨(l.set (off + i) w).map GoValue.bool⟩⟩) } := by
  have hvs : validateSlice (⟨some (.base a), off, len, cap⟩ : SliceValue)
      = .ok () := by
    simp [validateSlice, Nat.not_lt.mpr hcap, Bind.bind, Except.bind]
  have hloc : sliceIndexLoc ⟨some (.base a), off, len, cap⟩ ((i : Nat) : Int)
      = .ok (.index (.base a) (Int.ofNat (off + i))) := by
    simp only [sliceIndexLoc, hvs, Bind.bind, Except.bind,
      pure, Except.pure, Int.toNat_natCast, Int.ofNat_eq_natCast]
    rw [if_neg (by omega)]
    simp [hi]
  have hglist : l[off + i]? = some (l[off + i]'hsz) :=
    List.getElem?_eq_getElem hsz
  have harrset : arraySet (⟨l.map GoValue.bool⟩ : Array GoValue)
      (Int.ofNat (off + i)) (.bool w)
      = .ok ⟨(l.set (off + i) w).map GoValue.bool⟩ := by
    have hidx : ((off + i : Nat) : Int).toNat = off + i := by omega
    simp only [arraySet, arrayIndexNat, Bind.bind, Except.bind,
      Int.ofNat_eq_natCast, hidx]
    rw [if_neg (by omega), if_pos (by simpa using hsz)]
    simp [hglist, coerceStoredValue, Array.set!, pure, Except.pure]
  have hnorm : normalizeValueForTy σ (.array n .bool)
      (.array ⟨(l.set (off + i) w).map GoValue.bool⟩)
      = .ok (.array ⟨(l.set (off + i) w).map GoValue.bool⟩) := by
    rw [normalizeValueForTy, typeResolutionFuel]
    simp only [normalizeValueForTyFuel]
    rw [if_neg (by simp [hn])]
    simp [normalizeListWith_id, List.map_set, Bind.bind, Except.bind,
      Functor.map, Except.map]
  simp only [storeTarget, resolveChain, indexTargetLoc, valueAsInt,
    valueAsLoc, hloc, Bind.bind, Except.bind, storeLoc,
    loadLoc, hlook, harrset, hnorm, pure, Except.pure]

/-- GAP-WITNESS (kit gap; mirrors `GoLean.Iris.buildDefaultArrayValue_int`
in `Laws/StmtOps.lean`, restated Iris-free over `Laws/Values`'
`forIn_range'_inv`): the default `[m]bool` at a SYMBOLIC length is `m`
`false`s. -/
theorem buildDefaultArrayValue_bool (σ : ExecState) (m : Nat) :
    buildDefaultArrayValue σ m .bool
      = .ok (.array ⟨List.replicate m (GoValue.bool false)⟩) := by
  simp only [buildDefaultArrayValue, buildArrayValue,
    Std.Legacy.Range.forIn_eq_forIn_range', Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show ([:m] : Std.Legacy.Range).size = m from by
    simp [Std.Legacy.Range.size]]
  rw [GoLean.Iris.forIn_range'_inv (N := m) (n := m) (j := 0)
    (b := (#[] : Array GoValue))
    (Q := fun i acc => acc = ⟨List.replicate i (GoValue.bool false)⟩)
    (out := fun _ acc => acc.push (.bool false))
    (res := ⟨List.replicate m (GoValue.bool false)⟩)
    ?hfill (by omega) (by simp) (by intro b' h; rw [h, Nat.zero_add])]
  · rfl
  · case hfill =>
      intro i acc hi hacc
      refine ⟨by simp [defaultValue, defaultValueFuel, typeResolutionFuel], ?_⟩
      rw [hacc, List.replicate_succ']
      simp [Array.push]

/-! ## Normal-form side conditions for stores -/

private theorem norm_u64_cell {σ : ExecState} {v : Int}
    (hv : IntKind.normalize .uint64 v = v) :
    normalizeValueForTy σ tU (.int v .uint64) = .ok (.int v .uint64) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel, hv]

private theorem norm_bool_cell {σ : ExecState} {b : Bool} :
    normalizeValueForTy σ .bool (.bool b) = .ok (.bool b) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]

/-! ## Mark-phase heap facts (live cells at `a`/`a+1` behind the
concrete front and the abstract dead tail) -/

private theorem mheap_lookup_j {n₀ nv iv jv : Int} {m : Nat} {bs : List Bool}
    {dead : Heap} {a : Nat} {f2 : Bool}
    (hd : DeadFrom dead a) (h10 : 10 ≤ a) :
    Heap.lookup (svFront n₀ nv m bs iv false ++ (dead ++ mLive a jv f2))
      (.base ⟨a⟩) = some (u64cell jv) := by
  rw [lookup_append_right (front_lookup_none h10),
    lookup_append_right (hd a (Nat.le_refl a))]
  exact lookup_cons_self

private theorem mheap_lookup_ff {n₀ nv iv jv : Int} {m : Nat} {bs : List Bool}
    {dead : Heap} {a : Nat} {f2 : Bool}
    (hd : DeadFrom dead a) (h10 : 10 ≤ a) :
    Heap.lookup (svFront n₀ nv m bs iv false ++ (dead ++ mLive a jv f2))
      (.base ⟨a + 1⟩) = some (bcell f2) := by
  rw [lookup_append_right (front_lookup_none (by omega)),
    lookup_append_right (hd (a + 1) (by omega)), mLive,
    lookup_cons_ne (base_beq_false (by omega : a ≠ a + 1))]
  exact lookup_cons_self

private theorem mheap_set_j {n₀ nv iv jv jv' : Int} {m : Nat} {bs : List Bool}
    {dead : Heap} {a : Nat} {f2 : Bool}
    (hd : DeadFrom dead a) (h10 : 10 ≤ a) :
    Heap.set (svFront n₀ nv m bs iv false ++ (dead ++ mLive a jv f2))
      (.base ⟨a⟩) (u64cell jv')
      = svFront n₀ nv m bs iv false ++ (dead ++ mLive a jv' f2) := by
  rw [set_append_right (front_lookup_none h10),
    set_append_right (hd a (Nat.le_refl a))]
  show _ ++ (_ ++ Heap.set (mLive a jv f2) _ _) = _
  rw [mLive, set_cons_self]
  rfl

private theorem mheap_set_ff {n₀ nv iv jv : Int} {m : Nat} {bs : List Bool}
    {dead : Heap} {a : Nat} {f2 f2' : Bool}
    (hd : DeadFrom dead a) (h10 : 10 ≤ a) :
    Heap.set (svFront n₀ nv m bs iv false ++ (dead ++ mLive a jv f2))
      (.base ⟨a + 1⟩) (bcell f2')
      = svFront n₀ nv m bs iv false ++ (dead ++ mLive a jv f2') := by
  rw [set_append_right (front_lookup_none (by omega)),
    set_append_right (hd (a + 1) (by omega))]
  show _ ++ (_ ++ Heap.set (mLive a jv f2) _ _) = _
  rw [mLive, set_cons_ne (base_beq_false (by omega : a ≠ a + 1)),
    set_cons_self]
  rfl

/-- The backing-cell store keeps the live tail intact (concrete cell 6
sits in the front; pure structural reduction). -/
private theorem set_front6 {n₀ nv iv : Int} {m : Nat} {bs bs' : List Bool}
    {ff : Bool} {X : Heap} :
    Heap.set (svFront n₀ nv m bs iv ff ++ X) (.base ⟨6⟩) (bkcell m bs')
      = svFront n₀ nv m bs' iv ff ++ X := by
  with_unfolding_all rfl

/-! ## Mark-phase intermediate continuations -/

def mEnvB2 : LocalEnv := [] :: mEnvB1
def stEnv (a : Nat) : LocalEnv := [] :: inEnvB1 a
abbrev jAsg : Stmt := .assign (.var "j") (.mul (.var "i") (.var "i"))
abbrev ffAsgT : Stmt := .assign (.var "$forFirst") (.boolLit true)
abbrev whileIn : Stmt := .while (.boolLit true) svInnerBody
def jRhsK (a : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨a⟩)) [] []] [] [] (.seqn #[]) (jEnv a)
    (.seq [svFF2Block] (jEnv a) mTail)
def inFlagTail (a : Nat) : Cont :=
  .seq [.seqn #[], svInnerGuardIf, svMarkStore] (inEnvB1 a) (innerLoopK a)
def inFlagIfK (a : Nat) : Cont :=
  .ifK (.assign (.var "$forFirst") (.boolLit false))
    (.assign (.var "j") (.add (.var "j") (.var "i"))) (inEnvB1 a)
    (inFlagTail a)
def jGuardK (a : Nat) : Cont :=
  .strictK .atMostCmp [] [.var "n"] (inEnvB1 a) (innerCmpK a)
def stTail (a : Nat) : Cont :=
  .seq [] (stEnv a) (.seq [] (inEnvB1 a) (innerLoopK a))
def mstTgtK (a : Nat) (m : Nat) : Cont :=
  .tgtOpK (.chain [.index]) [svHandle m] [] [] [] .vals [.boolLit true] []
    (.seqn #[]) (stEnv a) (stTail a)
def jIncRhsK (a : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨a⟩)) [] []] [] [] (.seqn #[])
    (inEnvB1 a) (inFlagTail a)

/-! ## Mark-phase rfl slabs -/

private theorem sv_me1 (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 7 (svStO n₀ nv m bs iv false dead na)
        (.retV (.bool true) notIfK) ch
      = .ok (.exec (.initialization { id := "j", typ := tU }) mEnvB2
            (.seq [jAsg, svFF2Block] mEnvB2 mTail),
          svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

private theorem sv_me3 (iv : Int)
    (H : Heap) (na' : Nat) (a : Nat) (ch : Choices)
    (h8 : Heap.lookup H (.base ⟨8⟩) = some (u64cell iv)) :
    stepFnIter 8 (svSt H na')
        (.next (.seq [jAsg, svFF2Block] (jEnv a) mTail)) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .mul [.int iv .uint64] [] (jEnv a) (jRhsK a)),
          svSt H na', ch) := by
  show stepFnIter (5 + 1 + 1 + 1) _ _ _ = _
  have hA : stepFnIter 5 (svSt H na')
      (.next (.seq [jAsg, svFF2Block] (jEnv a) mTail)) ch
      = .ok (.evalE (.var "i") (jEnv a)
          (.strictK .mul [] [.var "i"] (jEnv a) (jRhsK a)), svSt H na', ch) := by
    with_unfolding_all rfl
  have hv := stepFnIter_one (stepFn_var (σ := svSt H na') (x := "i")
    (env := jEnv a) (a := ⟨8⟩)
    (k := .strictK .mul [] [.var "i"] (jEnv a) (jRhsK a)) (ch := ch)
    (c := u64cell iv) rfl h8)
  have hB : stepFnIter 1 (svSt H na')
      (.retV (.int iv .uint64) (.strictK .mul [] [.var "i"] (jEnv a) (jRhsK a)))
      ch
      = .ok (.evalE (.var "i") (jEnv a)
          (.strictK .mul [.int iv .uint64] [] (jEnv a) (jRhsK a)),
        svSt H na', ch) := by
    with_unfolding_all rfl
  have hv2 := stepFnIter_one (stepFn_var (σ := svSt H na') (x := "i")
    (env := jEnv a) (a := ⟨8⟩)
    (k := .strictK .mul [.int iv .uint64] [] (jEnv a) (jRhsK a)) (ch := ch)
    (c := u64cell iv) rfl h8)
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA hv) hB) hv2

private theorem sv_me5 (H : Heap) (na' : Nat) (a : Nat) (v : Int)
    (ch : Choices) :
    stepFnIter 1 (svSt H na') (.retV (.int v .uint64) (jRhsK a)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (jEnv a)
            (.seq [svFF2Block] (jEnv a) mTail)),
          svSt H na', ch) := by
  with_unfolding_all rfl

private theorem sv_me8 (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 3 (svSt H na')
        (.next (.seq ((#[] : Array Stmt).toList ++ [svFF2Block]) (jEnv a) mTail))
        ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
            ([] :: jEnv a)
            (.seq [ffAsgT, whileIn] ([] :: jEnv a) (.seq [] (jEnv a) mTail)),
          svSt H na', ch) := by
  with_unfolding_all rfl

private theorem sv_me10 (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 6 (svSt H na')
        (.next (.seq [ffAsgT, whileIn] (inEnv a) (.seq [] (jEnv a) mTail))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 1⟩)) [] []]
            [.bool true] (.seqn #[]) (inEnv a)
            (.seq [whileIn] (inEnv a) (.seq [] (jEnv a) mTail))),
          svSt H na', ch) := by
  with_unfolding_all rfl

private theorem sv_me14 (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 1 (svSt H na')
        (.next (.seq ((#[] : Array Stmt).toList ++ [whileIn]) (inEnv a)
          (.seq [] (jEnv a) mTail))) ch
      = .ok (innerHeadCfg a, svSt H na', ch) := by
  with_unfolding_all rfl

/-- Inner head → the `$forFirst` read point. 6 steps. -/
private theorem sv_mh (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 6 (svSt H na') (innerHeadCfg a) ch
      = .ok (.evalE (.var "$forFirst") (inEnvB1 a) (inFlagIfK a),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Flag TRUE → the `$forFirst := false` store point. 6 steps. -/
private theorem sv_mft (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 6 (svSt H na') (.retV (.bool true) (inFlagIfK a)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 1⟩)) [] []]
            [.bool false] (.seqn #[]) (inEnvB1 a) (inFlagTail a)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Flag FALSE → the `j` read of `j := j + i`. 5 steps. -/
private theorem sv_mff (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 5 (svSt H na') (.retV (.bool false) (inFlagIfK a)) ch
      = .ok (.evalE (.var "j") (inEnvB1 a)
            (.strictK .add [] [.var "i"] (inEnvB1 a) (jIncRhsK a)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Post-flag-store drain → the `j <= n` read point. From the drained
`storeK` through the two splices to the `j` read. 7 steps. -/
private theorem sv_mg (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 7 (svSt H na')
        (.next (.storeK [] [] (.seqn #[]) (inEnvB1 a) (inFlagTail a))) ch
      = .ok (.evalE (.var "j") (inEnvB1 a) (jGuardK a), svSt H na', ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 2) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_storeK_nil (σ := svSt H na')
    (body := .seqn #[]) (env := inEnvB1 a) (k := inFlagTail a) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na') (ss := #[])
    (env := inEnvB1 a) (rest := [.seqn #[], svInnerGuardIf, svMarkStore])
    (k := innerLoopK a) (ch := ch))
  have h3 : stepFnIter 1 (svSt H na')
      (.next (.seq ((#[] : Array Stmt).toList
          ++ [.seqn #[], svInnerGuardIf, svMarkStore])
        (inEnvB1 a) (innerLoopK a))) ch
      = .ok (.exec (.seqn #[]) (inEnvB1 a)
          (.seq [svInnerGuardIf, svMarkStore] (inEnvB1 a) (innerLoopK a)),
        svSt H na', ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na') (ss := #[])
    (env := inEnvB1 a) (rest := [svInnerGuardIf, svMarkStore])
    (k := innerLoopK a) (ch := ch))
  have h5 : stepFnIter 1 (svSt H na')
      (.next (.seq ((#[] : Array Stmt).toList ++ [svInnerGuardIf, svMarkStore])
        (inEnvB1 a) (innerLoopK a))) ch
      = .ok (.exec svInnerGuardIf (inEnvB1 a)
          (.seq [svMarkStore] (inEnvB1 a) (innerLoopK a)), svSt H na', ch) := by
    with_unfolding_all rfl
  have h6 : stepFnIter 2 (svSt H na')
      (.exec svInnerGuardIf (inEnvB1 a)
        (.seq [svMarkStore] (inEnvB1 a) (innerLoopK a))) ch
      = .ok (.evalE (.var "j") (inEnvB1 a) (jGuardK a), svSt H na', ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6

/-- `j` delivered to the guard → the test's delivery (reads `n` at
cell 3; the `atMostCmp` apply reduces definitionally). 3 steps. -/
private theorem sv_mgd (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (X : Heap) (na' : Nat) (a : Nat) (jv : Int) (ch : Choices) :
    stepFnIter 3 (svSt (svFront n₀ nv m bs iv false ++ X) na')
        (.retV (.int jv .uint64) (jGuardK a)) ch
      = .ok (.retV (.bool (decide (jv ≤ nv))) (innerCmpK a),
          svSt (svFront n₀ nv m bs iv false ++ X) na', ch) := by
  with_unfolding_all rfl

/-- Test TRUE → the mark store's `j` (index) read. 10 steps. -/
private theorem sv_ms1 (H : Heap) (na' : Nat) (a : Nat) (m : Nat)
    (ch : Choices)
    (h7 : Heap.lookup H (.base ⟨7⟩) = some (hcell m)) :
    stepFnIter 10 (svSt H na') (.retV (.bool true) (innerCmpK a)) ch
      = .ok (.evalE (.var "j") (stEnv a) (mstTgtK a m), svSt H na', ch) := by
  show stepFnIter (1 + 1 + 3 + 1 + 2 + 1 + 1) _ _ _ = _
  have h1 : stepFnIter 1 (svSt H na') (.retV (.bool true) (innerCmpK a)) ch
      = .ok (.exec (.seqn #[]) (inEnvB1 a)
          (.seq [svMarkStore] (inEnvB1 a) (innerLoopK a)), svSt H na', ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na') (ss := #[])
    (env := inEnvB1 a) (rest := [svMarkStore]) (k := innerLoopK a) (ch := ch))
  have h3 : stepFnIter 3 (svSt H na')
      (.next (.seq ((#[] : Array Stmt).toList ++ [svMarkStore])
        (inEnvB1 a) (innerLoopK a))) ch
      = .ok (.exec (.seqn #[.assign
            (.addr (.indexAddr (.var "composite") (.var "j"))) (.boolLit true)])
          (stEnv a) (stTail a), svSt H na', ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na')
    (ss := #[.assign (.addr (.indexAddr (.var "composite") (.var "j")))
      (.boolLit true)])
    (env := stEnv a) (rest := []) (k := .seq [] (inEnvB1 a) (innerLoopK a))
    (ch := ch))
  have h5 : stepFnIter 2 (svSt H na')
      (.next (.seq ((#[.assign (.addr (.indexAddr (.var "composite") (.var "j")))
            (.boolLit true)] : Array Stmt).toList ++ [])
        (stEnv a) (.seq [] (inEnvB1 a) (innerLoopK a)))) ch
      = .ok (.evalE (.var "composite") (stEnv a)
          (.tgtOpK (.chain [.index]) [] [.var "j"] [] [] .vals [.boolLit true]
            [] (.seqn #[]) (stEnv a) (stTail a)), svSt H na', ch) := by
    with_unfolding_all rfl
  have h6 := stepFnIter_one (stepFn_var (σ := svSt H na') (x := "composite")
    (env := stEnv a) (a := ⟨7⟩)
    (k := .tgtOpK (.chain [.index]) [] [.var "j"] [] [] .vals [.boolLit true]
      [] (.seqn #[]) (stEnv a) (stTail a)) (ch := ch)
    (c := hcell m) rfl h7)
  have h7' : stepFnIter 1 (svSt H na')
      (.retV (svHandle m)
        (.tgtOpK (.chain [.index]) [] [.var "j"] [] [] .vals [.boolLit true]
          [] (.seqn #[]) (stEnv a) (stTail a))) ch
      = .ok (.evalE (.var "j") (stEnv a) (mstTgtK a m), svSt H na', ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5)
    h6) h7'

/-! ## Entry-phase and outer-dispatch segments (`with_unfolding_all rfl`
slabs over the concrete front; probe-verified boundaries) -/

/-- Entry → the `n < 2` guard's delivery (through the `countPrimes`
frame entry at concrete addresses). 17 steps. -/
private theorem sv_segE0 (n₀ : Int) (ch : Choices) :
    stepFnIter 17 (svSeed0 n₀) svC00 ch
      = .ok (.retV (.bool (decide (IntKind.normalize .uint64 n₀ < 2))) guardK,
          svStG n₀ (IntKind.normalize .uint64 n₀), ch) := by
  with_unfolding_all rfl

/-- Guard TRUE → `$res0 := 0`, return, frame exit, harness epilogue,
terminal. 38 steps; every written cell already holds `0`. -/
private theorem sv_segGT (n₀ nv : Int) (ch : Choices) :
    stepFnIter 38 (svStG n₀ nv) (.retV (.bool true) guardK) ch
      = .ok (.next .stop, svStG n₀ nv, ch) := by
  with_unfolding_all rfl

/-- Guard FALSE → `$c0` declared, `n + 1` computed, the `makeSlice`
apply point. 15 steps. -/
private theorem sv_segE1 (n₀ nv : Int) (ch : Choices) :
    stepFnIter 15 (svStG n₀ nv) (.retV (.bool false) guardK) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (nv + 1)) .uint64) msK,
          svStE1 n₀ nv, ch) := by
  with_unfolding_all rfl

/-- GAP-WITNESS (kit gap; the `[]bool` sibling of
`StepKit.stepFn_makeSlice_u64_step`'s apply fact): `make([]bool, m)` at
the SYMBOLIC length `m` from the concrete pre-state — backing array of
`m` `false`s allocated at address 6, the handle stored into `$c0`. -/
theorem sv_makeSlice (n₀ nv : Int) (m : Nat) (ch : Choices) :
    applyStmtOp (svStE1 n₀ nv) ch (.makeSlice .bool false) 1
      [.addr (.base ⟨5⟩), .int ((m : Nat) : Int) .uint64]
      = .ok (svStE2 n₀ nv m (List.replicate m false), ch) := by
  have hbs : svStE2 n₀ nv m (List.replicate m false)
      = svSt [(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell 0),
              (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
              (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, hcell m),
              (.base ⟨6⟩, ⟨some (.array m .bool),
                .array ⟨List.replicate m (GoValue.bool false)⟩⟩)] 7 := by
    simp only [svStE2, bkcell, List.map_replicate]
  rw [hbs]
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, Bind.bind, Except.bind,
    pure, Except.pure, natFromNonneg_cast, buildDefaultArrayValue_bool,
    if_neg (show ¬ (m < m) by omega)]
  with_unfolding_all rfl

/-- Post-`makeSlice` → the outer loop head (declares `composite`, `i`,
`$forFirst` at concrete 7/8/9). 42 steps. -/
private theorem sv_segE2 (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (ch : Choices) :
    stepFnIter 42 (svStE2 n₀ nv m bs) (.next msTailK) ch
      = .ok (svHeadCfg, svStO n₀ nv m bs 2 true [] 10, ch) := by
  with_unfolding_all rfl

def oCmp2K : Cont :=
  .strictK .atMostCmp [] [.var "n"] oEnvB1 outerCmpK

/-- FIRST outer dispatch (flag up): head → the `i*i` apply point. 25
steps; the flag drops. -/
private theorem sv_segA0 (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (svStO n₀ nv m bs iv true dead na) svHeadCfg ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .mul [.int iv .uint64] [] oEnvB1 oCmp2K),
          svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

def incRhsK : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨8⟩)) [] []] [] [] (.seqn #[]) oEnvB1
    (.seq [.seqn #[], svOuterGuardIf, svOuterUser] oEnvB1 outerLoopK)

/-- LATER outer dispatch, phase a (flag down): head → the `i + 1` apply
point. 15 steps. -/
private theorem sv_segA1a (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 15 (svStO n₀ nv m bs iv false dead na) svHeadCfg ch
      = .ok (.retV (.int 1 .uint64)
            (.strictK .add [.int iv .uint64] [] oEnvB1 incRhsK),
          svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- LATER outer dispatch, phase b: the incremented `i` stored and
re-read → the `i*i` apply point. 13 steps. -/
private theorem sv_segA1b (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (iv w : Int) (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 13 (svStO n₀ nv m bs iv false dead na)
        (.retV (.int w .uint64) incRhsK) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 w) .uint64)
            (.strictK .mul [.int (IntKind.normalize .uint64 w) .uint64] []
              oEnvB1 oCmp2K),
          svStO n₀ nv m bs (IntKind.normalize .uint64 w) false dead na, ch) := by
  with_unfolding_all rfl

/-- The `i*i` product delivered → the test's delivery (reads `n`). 3
steps. -/
private theorem sv_segCmpN (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (iv p : Int) (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 3 (svStO n₀ nv m bs iv false dead na)
        (.retV (.int p .uint64) oCmp2K) ch
      = .ok (.retV (.bool (decide (p ≤ nv))) outerCmpK,
          svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

def notK : Cont := .strictK .not [] [] oEnvB2 notIfK

/-- Outer test TRUE → the `composite[i]` apply point. 11 steps. -/
private theorem sv_segB (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 11 (svStO n₀ nv m bs iv false dead na)
        (.retV (.bool true) outerCmpK) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .indexGet [svHandle m] [] oEnvB2 notK),
          svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- The `!` step on the delivered element. 1 step. -/
private theorem sv_segNot (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (na : Nat) (b : Bool) (ch : Choices) :
    stepFnIter 1 (svStO n₀ nv m bs iv false dead na)
        (.retV (.bool b) notK) ch
      = .ok (.retV (.bool (!b)) notIfK,
          svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- `!composite[i]` FALSE (already marked): skip back to the head. 5
steps. -/
private theorem sv_segSkip (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 5 (svStO n₀ nv m bs iv false dead na)
        (.retV (.bool false) notIfK) ch
      = .ok (svHeadCfg, svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Outer test FALSE: break, unwind to the count phase's sequence. 6
steps. -/
private theorem sv_segOExit (n₀ nv : Int) (m : Nat) (bs : List Bool) (iv : Int)
    (dead : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 6 (svStO n₀ nv m bs iv false dead na)
        (.retV (.bool false) outerCmpK) ch
      = .ok (.next postOuterK, svStO n₀ nv m bs iv false dead na, ch) := by
  with_unfolding_all rfl

/-! ## Mark-phase small slabs (store spine + head) -/

/-- Index value delivered to the store target → the drained `storeK`.
3 steps. -/
private theorem sv_ms3 (H : Heap) (na' : Nat) (a m : Nat) (jv : Int)
    (ch : Choices) :
    stepFnIter 3 (svSt H na') (.retV (.int jv .uint64) (mstTgtK a m)) ch
      = .ok (.next (.storeK [.chain (svHandle m) [.int jv .uint64] [.index]]
            [.bool true] (.seqn #[]) (stEnv a) (stTail a)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Post-store unwind → the inner head. 3 steps. -/
private theorem sv_ms8 (H : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 3 (svSt H na')
        (.next (.seq ((#[] : Array Stmt).toList ++ []) (stEnv a)
          (.seq [] (inEnvB1 a) (innerLoopK a)))) ch
      = .ok (innerHeadCfg a, svSt H na', ch) := by
  with_unfolding_all rfl

/-- The `+`'s second operand (`i`, concrete cell 8). 2 steps. -/
private theorem sv_mw13 (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (iv jv : Int) (X : Heap) (na' : Nat) (a : Nat) (ch : Choices) :
    stepFnIter 2 (svSt (svFront n₀ nv m bs iv false ++ X) na')
        (.retV (.int jv .uint64)
          (.strictK .add [] [.var "i"] (inEnvB1 a) (jIncRhsK a))) ch
      = .ok (.retV (.int iv .uint64)
            (.strictK .add [.int jv .uint64] [] (inEnvB1 a) (jIncRhsK a)),
          svSt (svFront n₀ nv m bs iv false ++ X) na', ch) := by
  with_unfolding_all rfl

/-! ## The marking pass: entry segment, iteration, exit -/

/-- **Mark-pass ENTRY** (`!composite[i]` TRUE): allocate `j := i*i` and
the inner `$forFirst` at `na`/`na+1`, run the inner first dispatch, and
deliver the first `j <= n` test. 60 steps. -/
theorem sv_markEntry (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (i : Nat) (dead : Heap) (na : Nat) (ch : Choices)
    (hd : DeadFrom dead na) (h10 : 10 ≤ na) (hii : i * i < 2 ^ 64) :
    stepFnIter 60 (svStO n₀ nv m bs (i : Int) false dead na)
        (.retV (.bool true) notIfK) ch
      = .ok (.retV (.bool (decide (((i * i : Nat) : Int) ≤ nv))) (innerCmpK na),
          svStM n₀ nv m bs (i : Int) dead na ((i * i : Nat) : Int) false, ch) := by
  show stepFnIter (7 + 1 + 8 + 1 + 1 + 1 + 1 + 1 + 3 + 1 + 6 + 1 + 1 + 1 + 1
    + 6 + 1 + 6 + 1 + 7 + 1 + 3) _ _ _ = _
  have e0 : Heap.lookup (svFront n₀ nv m bs (i : Int) false ++ dead)
      (.base ⟨na⟩) = none := by
    rw [lookup_append_right (front_lookup_none h10)]
    exact hd na (Nat.le_refl na)
  have hA := sv_me1 n₀ nv m bs (i : Int) dead na ch
  -- init j at na
  have hInitRaw : stepFn (svStO n₀ nv m bs (i : Int) false dead na)
      (.exec (.initialization { id := "j", typ := tU }) mEnvB2
        (.seq [jAsg, svFF2Block] mEnvB2 mTail)) ch
      = .ok (.next (.seq [jAsg, svFF2Block] (jEnv na) mTail),
          svSt (Heap.set (svFront n₀ nv m bs (i : Int) false ++ dead)
            (.base ⟨na⟩) (u64cell 0)) (na + 1), ch) :=
    stepFn_init_seq (by with_unfolding_all rfl)
  rw [set_fresh e0] at hInitRaw
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hInitRaw
  have hInit := stepFnIter_one hInitRaw
  have hB := sv_me3 (i : Int)
    (svFront n₀ nv m bs (i : Int) false ++ (dead ++ [(.base ⟨na⟩, u64cell 0)]))
    (na + 1) na ch (by with_unfolding_all rfl)
  have hMul : stepFn (svSt (svFront n₀ nv m bs (i : Int) false
        ++ (dead ++ [(.base ⟨na⟩, u64cell 0)])) (na + 1))
      (.retV (.int (i : Int) .uint64)
        (.strictK .mul [.int (i : Int) .uint64] [] (jEnv na) (jRhsK na))) ch
      = .ok (.retV (.int ((i * i : Nat) : Int) .uint64) (jRhsK na),
          svSt (svFront n₀ nv m bs (i : Int) false
            ++ (dead ++ [(.base ⟨na⟩, u64cell 0)])) (na + 1), ch) :=
    stepFn_strict_apply (done := [.int (i : Int) .uint64])
      (applyStrictOp_mul_u64 hii)
  have hC := sv_me5 (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ [(.base ⟨na⟩, u64cell 0)])) (na + 1) na ((i * i : Nat) : Int) ch
  have l1 : Heap.lookup (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ [(.base ⟨na⟩, u64cell 0)])) (.base ⟨na⟩)
      = some (u64cell 0) := by
    rw [lookup_append_right (front_lookup_none h10),
      lookup_append_right (hd na (Nat.le_refl na))]
    exact lookup_cons_self
  have hstRaw : storeTarget (svSt (svFront n₀ nv m bs (i : Int) false
        ++ (dead ++ [(.base ⟨na⟩, u64cell 0)])) (na + 1))
      (.chain (.addr (.base ⟨na⟩)) [] []) (.int ((i * i : Nat) : Int) .uint64)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs (i : Int) false
          ++ (dead ++ [(.base ⟨na⟩, u64cell 0)])) (.base ⟨na⟩)
            (u64cell ((i * i : Nat) : Int))) (na + 1)) :=
    storeTarget_addr l1 (norm_u64_cell (unorm_nat_of_lt hii))
  rw [set_append_right (front_lookup_none h10),
    set_append_right (hd na (Nat.le_refl na)), set_cons_self] at hstRaw
  have hStore1 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := jEnv na)
    (k := .seq [svFF2Block] (jEnv na) mTail) (ch := ch) hstRaw)
  have hD := stepFnIter_one (stepFn_storeK_nil
    (σ := svSt (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ [(.base ⟨na⟩, u64cell ((i * i : Nat) : Int))])) (na + 1))
    (body := .seqn #[]) (env := jEnv na)
    (k := .seq [svFF2Block] (jEnv na) mTail) (ch := ch))
  have hE := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ [(.base ⟨na⟩, u64cell ((i * i : Nat) : Int))])) (na + 1))
    (ss := #[]) (env := jEnv na) (rest := [svFF2Block]) (k := mTail) (ch := ch))
  have hF := sv_me8 (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ [(.base ⟨na⟩, u64cell ((i * i : Nat) : Int))])) (na + 1) na ch
  have e2 : Heap.lookup (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ [(.base ⟨na⟩, u64cell ((i * i : Nat) : Int))]))
      (.base ⟨na + 1⟩) = none := by
    rw [lookup_append_right (front_lookup_none (by omega)),
      lookup_append_right (hd (na + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    rfl
  have hInit2Raw : stepFn (svSt (svFront n₀ nv m bs (i : Int) false
        ++ (dead ++ [(.base ⟨na⟩, u64cell ((i * i : Nat) : Int))])) (na + 1))
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: jEnv na)
        (.seq [ffAsgT, whileIn] ([] :: jEnv na) (.seq [] (jEnv na) mTail))) ch
      = .ok (.next (.seq [ffAsgT, whileIn] (inEnv na)
            (.seq [] (jEnv na) mTail)),
          svSt (Heap.set (svFront n₀ nv m bs (i : Int) false
            ++ (dead ++ [(.base ⟨na⟩, u64cell ((i * i : Nat) : Int))]))
            (.base ⟨na + 1⟩) (bcell false)) (na + 2), ch) :=
    stepFn_init_seq (by with_unfolding_all rfl)
  rw [set_fresh e2] at hInit2Raw
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hInit2Raw
  have hInit2 := stepFnIter_one hInit2Raw
  have hG := sv_me10 (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ mLive na ((i * i : Nat) : Int) false)) (na + 2) na ch
  have l3 : Heap.lookup (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na ((i * i : Nat) : Int) false)) (.base ⟨na + 1⟩)
      = some (bcell false) := mheap_lookup_ff hd h10
  have hst2Raw : storeTarget (svSt (svFront n₀ nv m bs (i : Int) false
        ++ (dead ++ mLive na ((i * i : Nat) : Int) false)) (na + 2))
      (.chain (.addr (.base ⟨na + 1⟩)) [] []) (.bool true)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs (i : Int) false
          ++ (dead ++ mLive na ((i * i : Nat) : Int) false)) (.base ⟨na + 1⟩)
          (bcell true)) (na + 2)) :=
    storeTarget_addr l3 norm_bool_cell
  rw [mheap_set_ff hd h10] at hst2Raw
  have hStore2 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := inEnv na)
    (k := .seq [whileIn] (inEnv na) (.seq [] (jEnv na) mTail)) (ch := ch)
    hst2Raw)
  have hH := stepFnIter_one (stepFn_storeK_nil
    (σ := svSt (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (na + 2))
    (body := .seqn #[]) (env := inEnv na)
    (k := .seq [whileIn] (inEnv na) (.seq [] (jEnv na) mTail)) (ch := ch))
  have hI := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (na + 2))
    (ss := #[]) (env := inEnv na) (rest := [whileIn])
    (k := .seq [] (jEnv na) mTail) (ch := ch))
  have hJ := sv_me14 (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (na + 2) na ch
  have hK := sv_mh (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (na + 2) na ch
  have l4 : Heap.lookup (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (.base ⟨na + 1⟩)
      = some (bcell true) := mheap_lookup_ff hd h10
  have hL := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (na + 2))
    (x := "$forFirst") (env := inEnvB1 na) (a := ⟨na + 1⟩)
    (k := inFlagIfK na) (ch := ch) (c := bcell true) rfl l4)
  have hM := sv_mft (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (na + 2) na ch
  have hst3Raw : storeTarget (svSt (svFront n₀ nv m bs (i : Int) false
        ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (na + 2))
      (.chain (.addr (.base ⟨na + 1⟩)) [] []) (.bool false)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs (i : Int) false
          ++ (dead ++ mLive na ((i * i : Nat) : Int) true)) (.base ⟨na + 1⟩)
          (bcell false)) (na + 2)) :=
    storeTarget_addr l4 norm_bool_cell
  rw [mheap_set_ff hd h10] at hst3Raw
  have hStore3 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := inEnvB1 na)
    (k := inFlagTail na) (ch := ch) hst3Raw)
  have hN := sv_mg (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ mLive na ((i * i : Nat) : Int) false)) (na + 2) na ch
  have l5 : Heap.lookup (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na ((i * i : Nat) : Int) false)) (.base ⟨na⟩)
      = some (u64cell ((i * i : Nat) : Int)) := mheap_lookup_j hd h10
  have hO := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na ((i * i : Nat) : Int) false)) (na + 2))
    (x := "j") (env := inEnvB1 na) (a := ⟨na⟩)
    (k := jGuardK na) (ch := ch) (c := u64cell ((i * i : Nat) : Int)) rfl l5)
  have hP := sv_mgd n₀ nv m bs (i : Int)
    (dead ++ mLive na ((i * i : Nat) : Int) false) (na + 2) na
    ((i * i : Nat) : Int) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hA hInit) hB) hMul) hC) hStore1) hD) hE) hF) hInit2)
    hG) hStore2) hH) hI) hJ) hK) hL) hM) hStore3) hN) hO) hP

/-- **Mark-pass ITERATION** (test TRUE at `j`): store
`composite[j] = true`, advance `j := j + i`, deliver the next test.
49 steps. -/
theorem sv_markIter (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (i j : Nat) (dead : Heap) (na : Nat) (ch : Choices)
    (hd : DeadFrom dead na) (h10 : 10 ≤ na)
    (hjm : j < m) (hjlen : j < bs.length) (hlen : bs.length = m)
    (hji : j + i < 2 ^ 64) :
    stepFnIter 49 (svStM n₀ nv m bs (i : Int) dead na (j : Int) false)
        (.retV (.bool true) (innerCmpK na)) ch
      = .ok (.retV (.bool (decide (((j + i : Nat) : Int) ≤ nv))) (innerCmpK na),
          svStM n₀ nv m (bs.set j true) (i : Int) dead na
            ((j + i : Nat) : Int) false, ch) := by
  show stepFnIter (10 + 1 + 3 + 1 + 1 + 1 + 3 + 6 + 1 + 5 + 1 + 2 + 1 + 1 + 1
    + 7 + 1 + 3) _ _ _ = _
  have w1 := sv_ms1 (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ mLive na (j : Int) false)) (na + 2) na m ch
    (by with_unfolding_all rfl)
  have l1 : Heap.lookup (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (.base ⟨na⟩)
      = some (u64cell (j : Int)) := mheap_lookup_j hd h10
  have w2 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (na + 2))
    (x := "j") (env := stEnv na) (a := ⟨na⟩)
    (k := mstTgtK na m) (ch := ch) (c := u64cell (j : Int)) rfl l1)
  have w3 := sv_ms3 (svFront n₀ nv m bs (i : Int) false
    ++ (dead ++ mLive na (j : Int) false)) (na + 2) na m (j : Int) ch
  -- the element store into the backing cell
  have hstRaw : storeTarget (svSt (svFront n₀ nv m bs (i : Int) false
        ++ (dead ++ mLive na (j : Int) false)) (na + 2))
      (.chain (svHandle m) [.int (j : Nat) .uint64] [.index]) (.bool true)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs (i : Int) false
          ++ (dead ++ mLive na (j : Int) false)) (.base ⟨6⟩)
          ⟨some (.array m .bool),
           .array ⟨(bs.set (0 + j) true).map GoValue.bool⟩⟩) (na + 2)) :=
    storeTarget_slice_bool (by with_unfolding_all rfl) (Nat.le_refl m) hjm
      (by omega) hlen
  rw [Nat.zero_add, set_front6] at hstRaw
  have w5 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := stEnv na)
    (k := stTail na) (ch := ch) hstRaw)
  have w6 := stepFnIter_one (stepFn_storeK_nil
    (σ := svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (na + 2))
    (body := .seqn #[]) (env := stEnv na) (k := stTail na) (ch := ch))
  have w7 := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (na + 2))
    (ss := #[]) (env := stEnv na) (rest := [])
    (k := .seq [] (inEnvB1 na) (innerLoopK na)) (ch := ch))
  have w8 := sv_ms8 (svFront n₀ nv m (bs.set j true) (i : Int) false
    ++ (dead ++ mLive na (j : Int) false)) (na + 2) na ch
  have w9 := sv_mh (svFront n₀ nv m (bs.set j true) (i : Int) false
    ++ (dead ++ mLive na (j : Int) false)) (na + 2) na ch
  have l2 : Heap.lookup (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (.base ⟨na + 1⟩)
      = some (bcell false) := mheap_lookup_ff hd h10
  have w10 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (na + 2))
    (x := "$forFirst") (env := inEnvB1 na) (a := ⟨na + 1⟩)
    (k := inFlagIfK na) (ch := ch) (c := bcell false) rfl l2)
  have w11 := sv_mff (svFront n₀ nv m (bs.set j true) (i : Int) false
    ++ (dead ++ mLive na (j : Int) false)) (na + 2) na ch
  have l3 : Heap.lookup (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (.base ⟨na⟩)
      = some (u64cell (j : Int)) := mheap_lookup_j hd h10
  have w12 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na (j : Int) false)) (na + 2))
    (x := "j") (env := inEnvB1 na) (a := ⟨na⟩)
    (k := .strictK .add [] [.var "i"] (inEnvB1 na) (jIncRhsK na)) (ch := ch)
    (c := u64cell (j : Int)) rfl l3)
  have w13 := sv_mw13 n₀ nv m (bs.set j true) (i : Int) (j : Int)
    (dead ++ mLive na (j : Int) false) (na + 2) na ch
  have w14 : stepFn (svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
        ++ (dead ++ mLive na (j : Int) false)) (na + 2))
      (.retV (.int (i : Int) .uint64)
        (.strictK .add [.int (j : Int) .uint64] [] (inEnvB1 na)
          (jIncRhsK na))) ch
      = .ok (.retV (.int ((j + i : Nat) : Int) .uint64) (jIncRhsK na),
          svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
            ++ (dead ++ mLive na (j : Int) false)) (na + 2), ch) :=
    stepFn_strict_apply (done := [.int (j : Int) .uint64])
      (applyStrictOp_add_u64 hji)
  have w15 : stepFnIter 1 (svSt (svFront n₀ nv m (bs.set j true) (i : Int)
        false ++ (dead ++ mLive na (j : Int) false)) (na + 2))
      (.retV (.int ((j + i : Nat) : Int) .uint64) (jIncRhsK na)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.int ((j + i : Nat) : Int) .uint64] (.seqn #[]) (inEnvB1 na)
            (inFlagTail na)),
          svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
            ++ (dead ++ mLive na (j : Int) false)) (na + 2), ch) := by
    with_unfolding_all rfl
  have hst2Raw : storeTarget (svSt (svFront n₀ nv m (bs.set j true) (i : Int)
        false ++ (dead ++ mLive na (j : Int) false)) (na + 2))
      (.chain (.addr (.base ⟨na⟩)) [] []) (.int ((j + i : Nat) : Int) .uint64)
      = .ok (svSt (Heap.set (svFront n₀ nv m (bs.set j true) (i : Int) false
          ++ (dead ++ mLive na (j : Int) false)) (.base ⟨na⟩)
          (u64cell ((j + i : Nat) : Int))) (na + 2)) :=
    storeTarget_addr l3 (norm_u64_cell (unorm_nat_of_lt hji))
  rw [mheap_set_j hd h10] at hst2Raw
  have w16 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := inEnvB1 na)
    (k := inFlagTail na) (ch := ch) hst2Raw)
  have w17 := sv_mg (svFront n₀ nv m (bs.set j true) (i : Int) false
    ++ (dead ++ mLive na ((j + i : Nat) : Int) false)) (na + 2) na ch
  have l4 : Heap.lookup (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na ((j + i : Nat) : Int) false)) (.base ⟨na⟩)
      = some (u64cell ((j + i : Nat) : Int)) := mheap_lookup_j hd h10
  have w18 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m (bs.set j true) (i : Int) false
      ++ (dead ++ mLive na ((j + i : Nat) : Int) false)) (na + 2))
    (x := "j") (env := inEnvB1 na) (a := ⟨na⟩)
    (k := jGuardK na) (ch := ch) (c := u64cell ((j + i : Nat) : Int)) rfl l4)
  have w19 := sv_mgd n₀ nv m (bs.set j true) (i : Int)
    (dead ++ mLive na ((j + i : Nat) : Int) false) (na + 2) na
    ((j + i : Nat) : Int) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain w1 w2) w3) w5) w6) w7) w8) w9) w10) w11) w12) w13)
    (stepFnIter_one w14)) w15) w16) w17) w18) w19

/-- **Mark-pass EXIT** (test FALSE): break, unwind, back at the OUTER
head; the pass's two cells go dead. 10 steps. -/
private theorem sv_markExit (n₀ nv : Int) (m : Nat) (bs : List Bool)
    (iv jv : Int) (dead : Heap) (a : Nat) (ch : Choices) :
    stepFnIter 10 (svStM n₀ nv m bs iv dead a jv false)
        (.retV (.bool false) (innerCmpK a)) ch
      = .ok (svHeadCfg,
          svStO n₀ nv m bs iv false (dead ++ mLive a jv false) (a + 2), ch) := by
  with_unfolding_all rfl

/-- **The inner marking loop**, by induction on the remaining window
`n + 1 - j`: from the `j <= n` test's delivery the run reaches the
outer head with the table `markFrom n i bs j` and the two pass cells
dead, within `49·d + 10` steps. -/
theorem sv_mark_loop (n₀ : Int) (n m i : Nat) (hm : m = n + 1)
    (hi1 : 1 ≤ i) (hilt : i < 2 ^ 32) (hn : n < 2 ^ 62) :
    ∀ d : Nat, ∀ j : Nat, ∀ bs : List Bool, ∀ dead : Heap, ∀ na : Nat,
      ∀ ch : Choices, n + 1 - j ≤ d → bs.length = m →
      DeadFrom dead na → 10 ≤ na →
      ∃ (k : Nat) (jv' : Int), k ≤ 49 * d + 10 ∧
        stepFnIter k (svStM n₀ (n : Int) m bs (i : Int) dead na (j : Int) false)
            (.retV (.bool (decide ((j : Int) ≤ (n : Int)))) (innerCmpK na)) ch
          = .ok (svHeadCfg,
              svStO n₀ (n : Int) m (markFrom n i bs j) (i : Int) false
                (dead ++ mLive na jv' false) (na + 2), ch) := by
  intro d
  induction d with
  | zero =>
    intro j bs dead na ch hjd hbs hdd h10
    have hgt : n < j := by omega
    rw [markFrom_stop n i bs j hgt,
      show decide ((j : Int) ≤ (n : Int)) = false from
        decide_eq_false (by exact_mod_cast (by omega : ¬ (j ≤ n)))]
    exact ⟨10, (j : Int), by omega,
      sv_markExit n₀ (n : Int) m bs (i : Int) (j : Int) dead na ch⟩
  | succ d ih =>
    intro j bs dead na ch hjd hbs hdd h10
    by_cases hle : j ≤ n
    · have hji : j + i < 2 ^ 64 := by omega
      have hIter := sv_markIter n₀ (n : Int) m bs i j dead na ch hdd h10
        (by omega) (by omega) hbs hji
      obtain ⟨k, jv', hk, hrun⟩ := ih (j + i) (bs.set j true) dead na ch
        (by omega) (by simp [hbs]) hdd h10
      rw [markFrom_step n i bs j hle (by omega)]
      rw [show decide ((j : Int) ≤ (n : Int)) = true from
        decide_eq_true (by exact_mod_cast hle)]
      exact ⟨49 + k, jv', by omega, stepFnIter_chain hIter hrun⟩
    · have hgt : n < j := by omega
      rw [markFrom_stop n i bs j hgt,
        show decide ((j : Int) ≤ (n : Int)) = false from
          decide_eq_false (by exact_mod_cast hle)]
      exact ⟨10, (j : Int), by omega,
        sv_markExit n₀ (n : Int) m bs (i : Int) (j : Int) dead na ch⟩

/-! ## Count-phase heap facts (live cells at `b`/`b+1`/`b+2`) -/

private theorem kheap_lookup_c {n₀ nv ivo cv iv2 : Int} {m : Nat}
    {bs : List Bool} {dead : Heap} {b : Nat} {f3 : Bool}
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    Heap.lookup (svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3))
      (.base ⟨b⟩) = some (u64cell cv) := by
  rw [lookup_append_right (front_lookup_none h10),
    lookup_append_right (hd b (Nat.le_refl b))]
  exact lookup_cons_self

private theorem kheap_lookup_i {n₀ nv ivo cv iv2 : Int} {m : Nat}
    {bs : List Bool} {dead : Heap} {b : Nat} {f3 : Bool}
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    Heap.lookup (svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3))
      (.base ⟨b + 1⟩) = some (u64cell iv2) := by
  rw [lookup_append_right (front_lookup_none (by omega)),
    lookup_append_right (hd (b + 1) (by omega)), kLive,
    lookup_cons_ne (base_beq_false (by omega : b ≠ b + 1))]
  exact lookup_cons_self

private theorem kheap_lookup_ff {n₀ nv ivo cv iv2 : Int} {m : Nat}
    {bs : List Bool} {dead : Heap} {b : Nat} {f3 : Bool}
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    Heap.lookup (svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3))
      (.base ⟨b + 2⟩) = some (bcell f3) := by
  rw [lookup_append_right (front_lookup_none (by omega)),
    lookup_append_right (hd (b + 2) (by omega)), kLive,
    lookup_cons_ne (base_beq_false (by omega : b ≠ b + 2)),
    lookup_cons_ne (base_beq_false (by omega : b + 1 ≠ b + 2))]
  exact lookup_cons_self

private theorem kheap_set_c {n₀ nv ivo cv cv' iv2 : Int} {m : Nat}
    {bs : List Bool} {dead : Heap} {b : Nat} {f3 : Bool}
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    Heap.set (svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3))
      (.base ⟨b⟩) (u64cell cv')
      = svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv' iv2 f3) := by
  rw [set_append_right (front_lookup_none h10),
    set_append_right (hd b (Nat.le_refl b))]
  show _ ++ (_ ++ Heap.set (kLive b cv iv2 f3) _ _) = _
  rw [kLive, set_cons_self]
  rfl

private theorem kheap_set_i {n₀ nv ivo cv iv2 iv2' : Int} {m : Nat}
    {bs : List Bool} {dead : Heap} {b : Nat} {f3 : Bool}
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    Heap.set (svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3))
      (.base ⟨b + 1⟩) (u64cell iv2')
      = svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2' f3) := by
  rw [set_append_right (front_lookup_none (by omega)),
    set_append_right (hd (b + 1) (by omega))]
  show _ ++ (_ ++ Heap.set (kLive b cv iv2 f3) _ _) = _
  rw [kLive, set_cons_ne (base_beq_false (by omega : b ≠ b + 1)),
    set_cons_self]
  rfl

private theorem kheap_set_ff {n₀ nv ivo cv iv2 : Int} {m : Nat}
    {bs : List Bool} {dead : Heap} {b : Nat} {f3 f3' : Bool}
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    Heap.set (svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3))
      (.base ⟨b + 2⟩) (bcell f3')
      = svFront n₀ nv m bs ivo false ++ (dead ++ kLive b cv iv2 f3') := by
  rw [set_append_right (front_lookup_none (by omega)),
    set_append_right (hd (b + 2) (by omega))]
  show _ ++ (_ ++ Heap.set (kLive b cv iv2 f3) _ _) = _
  rw [kLive, set_cons_ne (base_beq_false (by omega : b ≠ b + 2)),
    set_cons_ne (base_beq_false (by omega : b + 1 ≠ b + 2)),
    set_cons_self]
  rfl

/-! ## Count-phase intermediate continuations -/

abbrev kAsg0 : Stmt := .assign (.var "count") (.intLit 0 .uint64)
abbrev kiAsg : Stmt := .assign (.var "i") (.intLit 2 .uint64)
abbrev whileCnt : Stmt := .while (.boolLit true) svCntBody
def kFlagTail (b : Nat) : Cont :=
  .seq [.seqn #[], svCntGuardIf, svCntUser] (kEnvB1 b) (cntLoopK b)
def kFlagIfK (b : Nat) : Cont :=
  .ifK (.assign (.var "$forFirst") (.boolLit false))
    (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))) (kEnvB1 b)
    (kFlagTail b)
def kGuardK (b : Nat) : Cont :=
  .strictK .atMostCmp [] [.var "n"] (kEnvB1 b) (cntCmpK b)
def kIncRhsK (b : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨b + 1⟩)) [] []] [] [] (.seqn #[])
    (kEnvB1 b) (kFlagTail b)
def kIncEnv (b : Nat) : LocalEnv := [] :: kEnvB2 b
def kCntRhsK (b : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨b⟩)) [] []] [] [] (.seqn #[])
    (kIncEnv b) (.seq [] (kIncEnv b) (cntNotTail b))
def kEpiRhsK (b : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] [] (.seqn #[]) (kEnv b)
    (.seq [.returnStmt] (kEnv b) svCallK)

/-! ## Count-phase slabs -/

/-- Count head → the `$forFirst` read. 6 steps. -/
private theorem sv_kh (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 6 (svSt H na') (cntHeadCfg b) ch
      = .ok (.evalE (.var "$forFirst") (kEnvB1 b) (kFlagIfK b),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Count flag TRUE → the flag-clear store point. 6 steps. -/
private theorem sv_kft (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 6 (svSt H na') (.retV (.bool true) (kFlagIfK b)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨b + 2⟩)) [] []]
            [.bool false] (.seqn #[]) (kEnvB1 b) (kFlagTail b)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Count flag FALSE → the `i` read of `i := i + 1`. 5 steps. -/
private theorem sv_kff (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 5 (svSt H na') (.retV (.bool false) (kFlagIfK b)) ch
      = .ok (.evalE (.var "i") (kEnvB1 b)
            (.strictK .add [] [.intLit 1 .uint64] (kEnvB1 b) (kIncRhsK b)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- The literal `1` operand. 2 steps. -/
private theorem sv_kw (H : Heap) (na' : Nat) (b : Nat) (iv2 : Int)
    (ch : Choices) :
    stepFnIter 2 (svSt H na')
        (.retV (.int iv2 .uint64)
          (.strictK .add [] [.intLit 1 .uint64] (kEnvB1 b) (kIncRhsK b))) ch
      = .ok (.retV (.int 1 .uint64)
            (.strictK .add [.int iv2 .uint64] [] (kEnvB1 b) (kIncRhsK b)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- The incremented `i` delivered → its `storeK`. 1 step. -/
private theorem sv_kis (H : Heap) (na' : Nat) (b : Nat) (w : Int)
    (ch : Choices) :
    stepFnIter 1 (svSt H na') (.retV (.int w .uint64) (kIncRhsK b)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨b + 1⟩)) [] []]
            [.int w .uint64] (.seqn #[]) (kEnvB1 b) (kFlagTail b)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Post-flag/increment drain → the `i <= n` read. 7 steps. -/
private theorem sv_kg (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 7 (svSt H na')
        (.next (.storeK [] [] (.seqn #[]) (kEnvB1 b) (kFlagTail b))) ch
      = .ok (.evalE (.var "i") (kEnvB1 b) (kGuardK b), svSt H na', ch) := by
  show stepFnIter (1 + 1 + 1 + 1 + 1 + 2) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_storeK_nil (σ := svSt H na')
    (body := .seqn #[]) (env := kEnvB1 b) (k := kFlagTail b) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na') (ss := #[])
    (env := kEnvB1 b) (rest := [.seqn #[], svCntGuardIf, svCntUser])
    (k := cntLoopK b) (ch := ch))
  have h3 : stepFnIter 1 (svSt H na')
      (.next (.seq ((#[] : Array Stmt).toList
          ++ [.seqn #[], svCntGuardIf, svCntUser]) (kEnvB1 b) (cntLoopK b))) ch
      = .ok (.exec (.seqn #[]) (kEnvB1 b)
          (.seq [svCntGuardIf, svCntUser] (kEnvB1 b) (cntLoopK b)),
        svSt H na', ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na') (ss := #[])
    (env := kEnvB1 b) (rest := [svCntGuardIf, svCntUser]) (k := cntLoopK b)
    (ch := ch))
  have h5 : stepFnIter 1 (svSt H na')
      (.next (.seq ((#[] : Array Stmt).toList ++ [svCntGuardIf, svCntUser])
        (kEnvB1 b) (cntLoopK b))) ch
      = .ok (.exec svCntGuardIf (kEnvB1 b)
          (.seq [svCntUser] (kEnvB1 b) (cntLoopK b)), svSt H na', ch) := by
    with_unfolding_all rfl
  have h6 : stepFnIter 2 (svSt H na')
      (.exec svCntGuardIf (kEnvB1 b)
        (.seq [svCntUser] (kEnvB1 b) (cntLoopK b))) ch
      = .ok (.evalE (.var "i") (kEnvB1 b) (kGuardK b), svSt H na', ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6

/-- `i` delivered to the count guard → the test's delivery. 3 steps. -/
private theorem sv_kgd (n₀ nv : Int) (m : Nat) (bs : List Bool) (ivo : Int)
    (X : Heap) (na' : Nat) (b : Nat) (iv2 : Int) (ch : Choices) :
    stepFnIter 3 (svSt (svFront n₀ nv m bs ivo false ++ X) na')
        (.retV (.int iv2 .uint64) (kGuardK b)) ch
      = .ok (.retV (.bool (decide (iv2 ≤ nv))) (cntCmpK b),
          svSt (svFront n₀ nv m bs ivo false ++ X) na', ch) := by
  with_unfolding_all rfl

/-- Count test TRUE → the `composite[i]` index read. 10 steps (one
splice at the symbolic env). -/
private theorem sv_kr1 (n₀ nv : Int) (m : Nat) (bs : List Bool) (ivo : Int)
    (X : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 10 (svSt (svFront n₀ nv m bs ivo false ++ X) na')
        (.retV (.bool true) (cntCmpK b)) ch
      = .ok (.evalE (.var "i") (kEnvB2 b)
            (.strictK .indexGet [svHandle m] [] (kEnvB2 b)
              (.strictK .not [] [] (kEnvB2 b) (cntNotIfK b))),
          svSt (svFront n₀ nv m bs ivo false ++ X) na', ch) := by
  show stepFnIter (1 + 1 + 8) _ _ _ = _
  have h1 : stepFnIter 1 (svSt (svFront n₀ nv m bs ivo false ++ X) na')
      (.retV (.bool true) (cntCmpK b)) ch
      = .ok (.exec (.seqn #[]) (kEnvB1 b)
          (.seq [svCntUser] (kEnvB1 b) (cntLoopK b)),
        svSt (svFront n₀ nv m bs ivo false ++ X) na', ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m bs ivo false ++ X) na') (ss := #[])
    (env := kEnvB1 b) (rest := [svCntUser]) (k := cntLoopK b) (ch := ch))
  have h3 : stepFnIter 8 (svSt (svFront n₀ nv m bs ivo false ++ X) na')
      (.next (.seq ((#[] : Array Stmt).toList ++ [svCntUser])
        (kEnvB1 b) (cntLoopK b))) ch
      = .ok (.evalE (.var "i") (kEnvB2 b)
          (.strictK .indexGet [svHandle m] [] (kEnvB2 b)
            (.strictK .not [] [] (kEnvB2 b) (cntNotIfK b))),
        svSt (svFront n₀ nv m bs ivo false ++ X) na', ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The count `!` step. 1 step. -/
private theorem sv_knot (H : Heap) (na' : Nat) (b : Nat) (w : Bool)
    (ch : Choices) :
    stepFnIter 1 (svSt H na')
        (.retV (.bool w) (.strictK .not [] [] (kEnvB2 b) (cntNotIfK b))) ch
      = .ok (.retV (.bool (!w)) (cntNotIfK b), svSt H na', ch) := by
  with_unfolding_all rfl

/-- Count `!composite[i]` TRUE → the `count` read of `count + 1`. 7
steps. -/
private theorem sv_kincA (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 7 (svSt H na') (.retV (.bool true) (cntNotIfK b)) ch
      = .ok (.evalE (.var "count") (kIncEnv b)
            (.strictK .add [] [.intLit 1 .uint64] (kIncEnv b) (kCntRhsK b)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- The literal `1` operand of `count + 1`. 2 steps. -/
private theorem sv_kincB (H : Heap) (na' : Nat) (b : Nat) (cv : Int)
    (ch : Choices) :
    stepFnIter 2 (svSt H na')
        (.retV (.int cv .uint64)
          (.strictK .add [] [.intLit 1 .uint64] (kIncEnv b) (kCntRhsK b))) ch
      = .ok (.retV (.int 1 .uint64)
            (.strictK .add [.int cv .uint64] [] (kIncEnv b) (kCntRhsK b)),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- The incremented `count` delivered → its `storeK`. 1 step. -/
private theorem sv_kincC (H : Heap) (na' : Nat) (b : Nat) (w : Int)
    (ch : Choices) :
    stepFnIter 1 (svSt H na') (.retV (.int w .uint64) (kCntRhsK b)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨b⟩)) [] []]
            [.int w .uint64] (.seqn #[]) (kIncEnv b)
            (.seq [] (kIncEnv b) (cntNotTail b))),
          svSt H na', ch) := by
  with_unfolding_all rfl

/-- Post-`count`-store drain → the count head. 6 steps. -/
private theorem sv_kincD (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 6 (svSt H na')
        (.next (.storeK [] [] (.seqn #[]) (kIncEnv b)
          (.seq [] (kIncEnv b) (cntNotTail b)))) ch
      = .ok (cntHeadCfg b, svSt H na', ch) := by
  show stepFnIter (1 + 1 + 4) _ _ _ = _
  have h1 := stepFnIter_one (stepFn_storeK_nil (σ := svSt H na')
    (body := .seqn #[]) (env := kIncEnv b)
    (k := .seq [] (kIncEnv b) (cntNotTail b)) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na') (ss := #[])
    (env := kIncEnv b) (rest := []) (k := cntNotTail b) (ch := ch))
  have h3 : stepFnIter 4 (svSt H na')
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (kIncEnv b)
        (cntNotTail b))) ch
      = .ok (cntHeadCfg b, svSt H na', ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- Count `!composite[i]` FALSE → back at the head. 5 steps. -/
private theorem sv_kskip (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 5 (svSt H na') (.retV (.bool false) (cntNotIfK b)) ch
      = .ok (cntHeadCfg b, svSt H na', ch) := by
  show stepFnIter (1 + 1 + 3) _ _ _ = _
  have h1 : stepFnIter 1 (svSt H na') (.retV (.bool false) (cntNotIfK b)) ch
      = .ok (.exec (.seqn #[]) (kEnvB2 b) (cntNotTail b), svSt H na', ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na') (ss := #[])
    (env := kEnvB2 b) (rest := [])
    (k := .seq [] (kEnvB1 b) (cntLoopK b)) (ch := ch))
  have h3 : stepFnIter 3 (svSt H na')
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (kEnvB2 b)
        (.seq [] (kEnvB1 b) (cntLoopK b)))) ch
      = .ok (cntHeadCfg b, svSt H na', ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- Count test FALSE → break, unwind, `$res0 := count`'s `count` read
point. 12 steps (one splice at the symbolic env). -/
private theorem sv_kx1 (H : Heap) (na' : Nat) (b : Nat) (ch : Choices) :
    stepFnIter 12 (svSt H na') (.retV (.bool false) (cntCmpK b)) ch
      = .ok (.evalE (.var "count") (kEnv b) (kEpiRhsK b), svSt H na', ch) := by
  show stepFnIter (7 + 1 + 4) _ _ _ = _
  have h1 : stepFnIter 7 (svSt H na') (.retV (.bool false) (cntCmpK b)) ch
      = .ok (.exec svEpi (kEnv b) (.seq [] (kEnv b) svCallK),
          svSt H na', ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := svSt H na')
    (ss := #[.assign (.var "$res0") (.var "count"), .returnStmt])
    (env := kEnv b) (rest := []) (k := svCallK) (ch := ch))
  have h3 : stepFnIter 4 (svSt H na')
      (.next (.seq ((#[.assign (.var "$res0") (.var "count"),
            .returnStmt] : Array Stmt).toList ++ [])
        (kEnv b) svCallK)) ch
      = .ok (.evalE (.var "count") (kEnv b) (kEpiRhsK b), svSt H na', ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The `count` value delivered → store into `$res0` (cell 4), return,
frame exit into `$c2` (cell 2), harness epilogue (cell 1), terminal.
28 steps; the one symbolic-env splice (the store's empty body under
`kEnv b`) is conditioned, everything else is concrete. -/
private theorem sv_kx6 (n₀ nv ivo cv iv2 : Int) (m : Nat) (bs : List Bool)
    (dead : Heap) (b : Nat) (ch : Choices) :
    stepFnIter 28 (svStK n₀ nv m bs ivo dead b cv iv2 false)
        (.retV (.int cv .uint64) (kEpiRhsK b)) ch
      = .ok (.next .stop,
          svSt ([(.base ⟨0⟩, u64cell n₀),
            (.base ⟨1⟩, u64cell (IntKind.normalize .uint64
              (IntKind.normalize .uint64 (IntKind.normalize .uint64 cv)))),
            (.base ⟨2⟩, u64cell (IntKind.normalize .uint64
              (IntKind.normalize .uint64 cv))),
            (.base ⟨3⟩, u64cell nv), (.base ⟨4⟩,
              u64cell (IntKind.normalize .uint64 cv)),
            (.base ⟨5⟩, hcell m), (.base ⟨6⟩, bkcell m bs),
            (.base ⟨7⟩, hcell m), (.base ⟨8⟩, u64cell ivo),
            (.base ⟨9⟩, bcell false)]
            ++ (dead ++ kLive b cv iv2 false)) (b + 3), ch) := by
  show stepFnIter (3 + 1 + 24) _ _ _ = _
  have h1 : stepFnIter 3 (svStK n₀ nv m bs ivo dead b cv iv2 false)
      (.retV (.int cv .uint64) (kEpiRhsK b)) ch
      = .ok (.exec (.seqn #[]) (kEnv b) (.seq [.returnStmt] (kEnv b) svCallK),
          svSt ([(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell 0),
            (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
            (.base ⟨4⟩, u64cell (IntKind.normalize .uint64 cv)),
            (.base ⟨5⟩, hcell m), (.base ⟨6⟩, bkcell m bs),
            (.base ⟨7⟩, hcell m), (.base ⟨8⟩, u64cell ivo),
            (.base ⟨9⟩, bcell false)]
            ++ (dead ++ kLive b cv iv2 false)) (b + 3), ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt ([(.base ⟨0⟩, u64cell n₀), (.base ⟨1⟩, u64cell 0),
      (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
      (.base ⟨4⟩, u64cell (IntKind.normalize .uint64 cv)),
      (.base ⟨5⟩, hcell m), (.base ⟨6⟩, bkcell m bs),
      (.base ⟨7⟩, hcell m), (.base ⟨8⟩, u64cell ivo),
      (.base ⟨9⟩, bcell false)]
      ++ (dead ++ kLive b cv iv2 false)) (b + 3))
    (ss := #[]) (env := kEnv b) (rest := [.returnStmt]) (k := svCallK)
    (ch := ch))
  have h3 : stepFnIter 24 (svSt ([(.base ⟨0⟩, u64cell n₀),
        (.base ⟨1⟩, u64cell 0), (.base ⟨2⟩, u64cell 0),
        (.base ⟨3⟩, u64cell nv),
        (.base ⟨4⟩, u64cell (IntKind.normalize .uint64 cv)),
        (.base ⟨5⟩, hcell m), (.base ⟨6⟩, bkcell m bs),
        (.base ⟨7⟩, hcell m), (.base ⟨8⟩, u64cell ivo),
        (.base ⟨9⟩, bcell false)]
        ++ (dead ++ kLive b cv iv2 false)) (b + 3))
      (.next (.seq ((#[] : Array Stmt).toList ++ [.returnStmt]) (kEnv b)
        svCallK)) ch
      = .ok (.next .stop,
          svSt ([(.base ⟨0⟩, u64cell n₀),
            (.base ⟨1⟩, u64cell (IntKind.normalize .uint64
              (IntKind.normalize .uint64 (IntKind.normalize .uint64 cv)))),
            (.base ⟨2⟩, u64cell (IntKind.normalize .uint64
              (IntKind.normalize .uint64 cv))),
            (.base ⟨3⟩, u64cell nv), (.base ⟨4⟩,
              u64cell (IntKind.normalize .uint64 cv)),
            (.base ⟨5⟩, hcell m), (.base ⟨6⟩, bkcell m bs),
            (.base ⟨7⟩, hcell m), (.base ⟨8⟩, u64cell ivo),
            (.base ⟨9⟩, bcell false)]
            ++ (dead ++ kLive b cv iv2 false)) (b + 3), ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-! ## Count-phase composite segments -/

/-- **Count INIT**: from the post-outer-exit sequence, allocate
`count`/`i`/`$forFirst` at `b`/`b+1`/`b+2` and reach the count head.
42 steps. -/
theorem sv_kInit (n₀ nv ivo : Int) (m : Nat) (bs : List Bool)
    (dead : Heap) (b : Nat) (ch : Choices)
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    stepFnIter 42 (svStO n₀ nv m bs ivo false dead b) (.next postOuterK) ch
      = .ok (cntHeadCfg b, svStK n₀ nv m bs ivo dead b 0 2 true, ch) := by
  show stepFnIter (3 + 1 + 6 + 1 + 1 + 1 + 3 + 1 + 1 + 1 + 6 + 1 + 1 + 1 + 3
    + 1 + 6 + 1 + 1 + 1 + 1) _ _ _ = _
  have e0 : Heap.lookup (svFront n₀ nv m bs ivo false ++ dead)
      (.base ⟨b⟩) = none := by
    rw [lookup_append_right (front_lookup_none h10)]
    exact hd b (Nat.le_refl b)
  have h1 : stepFnIter 3 (svStO n₀ nv m bs ivo false dead b)
      (.next postOuterK) ch
      = .ok (.exec (.initialization { id := "count", typ := tU }) cEnv
          (.seq [kAsg0, svCntBlock, svEpi] cEnv svCallK),
        svStO n₀ nv m bs ivo false dead b, ch) := by
    with_unfolding_all rfl
  have h2Raw : stepFn (svStO n₀ nv m bs ivo false dead b)
      (.exec (.initialization { id := "count", typ := tU }) cEnv
        (.seq [kAsg0, svCntBlock, svEpi] cEnv svCallK)) ch
      = .ok (.next (.seq [kAsg0, svCntBlock, svEpi] (kEnv b) svCallK),
          svSt (Heap.set (svFront n₀ nv m bs ivo false ++ dead)
            (.base ⟨b⟩) (u64cell 0)) (b + 1), ch) :=
    stepFn_init_seq (by with_unfolding_all rfl)
  rw [set_fresh e0] at h2Raw
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h2Raw
  have h2 := stepFnIter_one h2Raw
  have h3 : stepFnIter 6 (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
      (.next (.seq [kAsg0, svCntBlock, svEpi] (kEnv b) svCallK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨b⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (kEnv b)
            (.seq [svCntBlock, svEpi] (kEnv b) svCallK)),
          svSt (svFront n₀ nv m bs ivo false
            ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1), ch) := by
    with_unfolding_all rfl
  have l1 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (.base ⟨b⟩)
      = some (u64cell 0) := by
    rw [lookup_append_right (front_lookup_none h10),
      lookup_append_right (hd b (Nat.le_refl b))]
    exact lookup_cons_self
  have hstRaw : storeTarget (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
      (.chain (.addr (.base ⟨b⟩)) [] []) (.int 0 .uint64)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs ivo false
          ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (.base ⟨b⟩)
          (u64cell 0)) (b + 1)) :=
    storeTarget_addr l1 (norm_u64_cell (by decide))
  rw [set_append_right (front_lookup_none h10),
    set_append_right (hd b (Nat.le_refl b)), set_cons_self] at hstRaw
  have h4 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := kEnv b)
    (k := .seq [svCntBlock, svEpi] (kEnv b) svCallK) (ch := ch) hstRaw)
  have h5 := stepFnIter_one (stepFn_storeK_nil
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
    (body := .seqn #[]) (env := kEnv b)
    (k := .seq [svCntBlock, svEpi] (kEnv b) svCallK) (ch := ch))
  have h6 := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
    (ss := #[]) (env := kEnv b) (rest := [svCntBlock, svEpi])
    (k := svCallK) (ch := ch))
  have h7 : stepFnIter 3 (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
      (.next (.seq ((#[] : Array Stmt).toList ++ [svCntBlock, svEpi])
        (kEnv b) svCallK)) ch
      = .ok (.exec svISeqn ([] :: kEnv b)
          (.seq [svCntFFBlock] ([] :: kEnv b) (postCntK b)),
        svSt (svFront n₀ nv m bs ivo false
          ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1), ch) := by
    with_unfolding_all rfl
  have h8 := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
    (ss := #[.initialization { id := "i", typ := tU }, kiAsg])
    (env := [] :: kEnv b) (rest := [svCntFFBlock]) (k := postCntK b)
    (ch := ch))
  have h9 : stepFnIter 1 (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
      (.next (.seq ((#[.initialization { id := "i", typ := tU },
            kiAsg] : Array Stmt).toList ++ [svCntFFBlock])
        ([] :: kEnv b) (postCntK b))) ch
      = .ok (.exec (.initialization { id := "i", typ := tU }) ([] :: kEnv b)
          (.seq [kiAsg, svCntFFBlock] ([] :: kEnv b) (postCntK b)),
        svSt (svFront n₀ nv m bs ivo false
          ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1), ch) := by
    with_unfolding_all rfl
  have e1 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (.base ⟨b + 1⟩) = none := by
    rw [lookup_append_right (front_lookup_none (by omega)),
      lookup_append_right (hd (b + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : b ≠ b + 1))]
    rfl
  have h10Raw : stepFn (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (b + 1))
      (.exec (.initialization { id := "i", typ := tU }) ([] :: kEnv b)
        (.seq [kiAsg, svCntFFBlock] ([] :: kEnv b) (postCntK b))) ch
      = .ok (.next (.seq [kiAsg, svCntFFBlock] (kiEnv b) (postCntK b)),
          svSt (Heap.set (svFront n₀ nv m bs ivo false
            ++ (dead ++ [(.base ⟨b⟩, u64cell 0)])) (.base ⟨b + 1⟩)
            (u64cell 0)) (b + 2), ch) :=
    stepFn_init_seq (by with_unfolding_all rfl)
  rw [set_fresh e1] at h10Raw
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h10Raw
  have h10' := stepFnIter_one h10Raw
  have h11 : stepFnIter 6 (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 0)]))
        (b + 2))
      (.next (.seq [kiAsg, svCntFFBlock] (kiEnv b) (postCntK b))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨b + 1⟩)) [] []]
            [.int 2 .uint64] (.seqn #[]) (kiEnv b)
            (.seq [svCntFFBlock] (kiEnv b) (postCntK b))),
          svSt (svFront n₀ nv m bs ivo false
            ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 0)]))
            (b + 2), ch) := by
    with_unfolding_all rfl
  have l2 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 0)]))
      (.base ⟨b + 1⟩) = some (u64cell 0) := by
    rw [lookup_append_right (front_lookup_none (by omega)),
      lookup_append_right (hd (b + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : b ≠ b + 1))]
    exact lookup_cons_self
  have hst2Raw : storeTarget (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 0)]))
        (b + 2))
      (.chain (.addr (.base ⟨b + 1⟩)) [] []) (.int 2 .uint64)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs ivo false
          ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 0)]))
          (.base ⟨b + 1⟩) (u64cell 2)) (b + 2)) :=
    storeTarget_addr l2 (norm_u64_cell (by decide))
  rw [set_append_right (front_lookup_none (by omega)),
    set_append_right (hd (b + 1) (by omega)),
    set_cons_ne (base_beq_false (by omega : b ≠ b + 1)),
    set_cons_self] at hst2Raw
  have h12 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := kiEnv b)
    (k := .seq [svCntFFBlock] (kiEnv b) (postCntK b)) (ch := ch) hst2Raw)
  have h13 := stepFnIter_one (stepFn_storeK_nil
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 2)]))
      (b + 2))
    (body := .seqn #[]) (env := kiEnv b)
    (k := .seq [svCntFFBlock] (kiEnv b) (postCntK b)) (ch := ch))
  have h14 := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 2)]))
      (b + 2))
    (ss := #[]) (env := kiEnv b) (rest := [svCntFFBlock])
    (k := postCntK b) (ch := ch))
  have h15 : stepFnIter 3 (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 2)]))
        (b + 2))
      (.next (.seq ((#[] : Array Stmt).toList ++ [svCntFFBlock]) (kiEnv b)
        (postCntK b))) ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
          ([] :: kiEnv b)
          (.seq [ffAsgT, whileCnt] ([] :: kiEnv b)
            (.seq [] (kiEnv b) (postCntK b))),
        svSt (svFront n₀ nv m bs ivo false
          ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 2)]))
          (b + 2), ch) := by
    with_unfolding_all rfl
  have e2 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 2)]))
      (.base ⟨b + 2⟩) = none := by
    rw [lookup_append_right (front_lookup_none (by omega)),
      lookup_append_right (hd (b + 2) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : b ≠ b + 2)),
      lookup_cons_ne (base_beq_false (by omega : b + 1 ≠ b + 2))]
    rfl
  have h16Raw : stepFn (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 2)]))
        (b + 2))
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: kiEnv b)
        (.seq [ffAsgT, whileCnt] ([] :: kiEnv b)
          (.seq [] (kiEnv b) (postCntK b)))) ch
      = .ok (.next (.seq [ffAsgT, whileCnt] (kEnvIn b)
            (.seq [] (kiEnv b) (postCntK b))),
          svSt (Heap.set (svFront n₀ nv m bs ivo false
            ++ (dead ++ [(.base ⟨b⟩, u64cell 0), (.base ⟨b + 1⟩, u64cell 2)]))
            (.base ⟨b + 2⟩) (bcell false)) (b + 3), ch) :=
    stepFn_init_seq (by with_unfolding_all rfl)
  rw [set_fresh e2] at h16Raw
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h16Raw
  have h16 := stepFnIter_one h16Raw
  have h17 : stepFnIter 6 (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b 0 2 false)) (b + 3))
      (.next (.seq [ffAsgT, whileCnt] (kEnvIn b)
        (.seq [] (kiEnv b) (postCntK b)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨b + 2⟩)) [] []]
            [.bool true] (.seqn #[]) (kEnvIn b)
            (.seq [whileCnt] (kEnvIn b) (.seq [] (kiEnv b) (postCntK b)))),
          svSt (svFront n₀ nv m bs ivo false
            ++ (dead ++ kLive b 0 2 false)) (b + 3), ch) := by
    with_unfolding_all rfl
  have l3 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b 0 2 false)) (.base ⟨b + 2⟩)
      = some (bcell false) := kheap_lookup_ff hd h10
  have hst3Raw : storeTarget (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b 0 2 false)) (b + 3))
      (.chain (.addr (.base ⟨b + 2⟩)) [] []) (.bool true)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs ivo false
          ++ (dead ++ kLive b 0 2 false)) (.base ⟨b + 2⟩)
          (bcell true)) (b + 3)) :=
    storeTarget_addr l3 norm_bool_cell
  rw [kheap_set_ff hd h10] at hst3Raw
  have h18 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := kEnvIn b)
    (k := .seq [whileCnt] (kEnvIn b) (.seq [] (kiEnv b) (postCntK b)))
    (ch := ch) hst3Raw)
  have h19 := stepFnIter_one (stepFn_storeK_nil
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b 0 2 true)) (b + 3))
    (body := .seqn #[]) (env := kEnvIn b)
    (k := .seq [whileCnt] (kEnvIn b) (.seq [] (kiEnv b) (postCntK b)))
    (ch := ch))
  have h20 := stepFnIter_one (stepFn_seqn_splice
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b 0 2 true)) (b + 3))
    (ss := #[]) (env := kEnvIn b) (rest := [whileCnt])
    (k := .seq [] (kiEnv b) (postCntK b)) (ch := ch))
  have h21 : stepFnIter 1 (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b 0 2 true)) (b + 3))
      (.next (.seq ((#[] : Array Stmt).toList ++ [whileCnt]) (kEnvIn b)
        (.seq [] (kiEnv b) (postCntK b)))) ch
      = .ok (cntHeadCfg b,
          svSt (svFront n₀ nv m bs ivo false
            ++ (dead ++ kLive b 0 2 true)) (b + 3), ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    h1 h2) h3) h4) h5) h6) h7) h8) h9) h10') h11) h12) h13) h14) h15) h16)
    h17) h18) h19) h20) h21

/-- **Count FIRST dispatch** (flag up): head → the `i <= n` test's
delivery; the flag drops, `i` unchanged. 25 steps. -/
private theorem sv_kDisp1 (n₀ nv ivo cv iv2 : Int) (m : Nat) (bs : List Bool)
    (dead : Heap) (b : Nat) (ch : Choices)
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) :
    stepFnIter 25 (svStK n₀ nv m bs ivo dead b cv iv2 true) (cntHeadCfg b) ch
      = .ok (.retV (.bool (decide (iv2 ≤ nv))) (cntCmpK b),
          svStK n₀ nv m bs ivo dead b cv iv2 false, ch) := by
  show stepFnIter (6 + 1 + 6 + 1 + 7 + 1 + 3) _ _ _ = _
  have h1 := sv_kh (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv iv2 true)) (b + 3) b ch
  have l1 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv iv2 true)) (.base ⟨b + 2⟩)
      = some (bcell true) := kheap_lookup_ff hd h10
  have h2 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv iv2 true)) (b + 3))
    (x := "$forFirst") (env := kEnvB1 b) (a := ⟨b + 2⟩)
    (k := kFlagIfK b) (ch := ch) (c := bcell true) rfl l1)
  have h3 := sv_kft (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv iv2 true)) (b + 3) b ch
  have hstRaw : storeTarget (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b cv iv2 true)) (b + 3))
      (.chain (.addr (.base ⟨b + 2⟩)) [] []) (.bool false)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs ivo false
          ++ (dead ++ kLive b cv iv2 true)) (.base ⟨b + 2⟩)
          (bcell false)) (b + 3)) :=
    storeTarget_addr l1 norm_bool_cell
  rw [kheap_set_ff hd h10] at hstRaw
  have h4 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := kEnvB1 b)
    (k := kFlagTail b) (ch := ch) hstRaw)
  have h5 := sv_kg (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv iv2 false)) (b + 3) b ch
  have l2 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv iv2 false)) (.base ⟨b + 1⟩)
      = some (u64cell iv2) := kheap_lookup_i hd h10
  have h6 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv iv2 false)) (b + 3))
    (x := "i") (env := kEnvB1 b) (a := ⟨b + 1⟩)
    (k := kGuardK b) (ch := ch) (c := u64cell iv2) rfl l2)
  have h7 := sv_kgd n₀ nv m bs ivo (dead ++ kLive b cv iv2 false) (b + 3) b
    iv2 ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7

/-- **Count LATER dispatch** (flag down): head → `i := i + 1` → the
test's delivery. 29 steps. -/
private theorem sv_kDisp (n₀ nv ivo cv : Int) (m : Nat) (bs : List Bool)
    (i : Nat) (dead : Heap) (b : Nat) (ch : Choices)
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) (hi1 : i + 1 < 2 ^ 64) :
    stepFnIter 29 (svStK n₀ nv m bs ivo dead b cv (i : Int) false)
        (cntHeadCfg b) ch
      = .ok (.retV (.bool (decide (((i + 1 : Nat) : Int) ≤ nv))) (cntCmpK b),
          svStK n₀ nv m bs ivo dead b cv ((i + 1 : Nat) : Int) false, ch) := by
  show stepFnIter (6 + 1 + 5 + 1 + 2 + 1 + 1 + 1 + 7 + 1 + 3) _ _ _ = _
  have h1 := sv_kh (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv (i : Int) false)) (b + 3) b ch
  have l1 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv (i : Int) false)) (.base ⟨b + 2⟩)
      = some (bcell false) := kheap_lookup_ff hd h10
  have h2 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv (i : Int) false)) (b + 3))
    (x := "$forFirst") (env := kEnvB1 b) (a := ⟨b + 2⟩)
    (k := kFlagIfK b) (ch := ch) (c := bcell false) rfl l1)
  have h3 := sv_kff (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv (i : Int) false)) (b + 3) b ch
  have l2 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv (i : Int) false)) (.base ⟨b + 1⟩)
      = some (u64cell (i : Int)) := kheap_lookup_i hd h10
  have h4 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv (i : Int) false)) (b + 3))
    (x := "i") (env := kEnvB1 b) (a := ⟨b + 1⟩)
    (k := .strictK .add [] [.intLit 1 .uint64] (kEnvB1 b) (kIncRhsK b))
    (ch := ch) (c := u64cell (i : Int)) rfl l2)
  have h5 := sv_kw (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv (i : Int) false)) (b + 3) b (i : Int) ch
  have h6 : stepFn (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b cv (i : Int) false)) (b + 3))
      (.retV (.int 1 .uint64)
        (.strictK .add [.int (i : Int) .uint64] [] (kEnvB1 b)
          (kIncRhsK b))) ch
      = .ok (.retV (.int ((i + 1 : Nat) : Int) .uint64) (kIncRhsK b),
          svSt (svFront n₀ nv m bs ivo false
            ++ (dead ++ kLive b cv (i : Int) false)) (b + 3), ch) :=
    stepFn_strict_apply (done := [.int (i : Int) .uint64])
      (applyStrictOp_add_u64 (b := 1) hi1)
  have h7 := sv_kis (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv (i : Int) false)) (b + 3) b
    ((i + 1 : Nat) : Int) ch
  have hstRaw : storeTarget (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b cv (i : Int) false)) (b + 3))
      (.chain (.addr (.base ⟨b + 1⟩)) [] []) (.int ((i + 1 : Nat) : Int)
        .uint64)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs ivo false
          ++ (dead ++ kLive b cv (i : Int) false)) (.base ⟨b + 1⟩)
          (u64cell ((i + 1 : Nat) : Int))) (b + 3)) :=
    storeTarget_addr l2 (norm_u64_cell (unorm_nat_of_lt hi1))
  rw [kheap_set_i hd h10] at hstRaw
  have h8 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := kEnvB1 b)
    (k := kFlagTail b) (ch := ch) hstRaw)
  have h9 := sv_kg (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv ((i + 1 : Nat) : Int) false)) (b + 3) b ch
  have l3 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv ((i + 1 : Nat) : Int) false)) (.base ⟨b + 1⟩)
      = some (u64cell ((i + 1 : Nat) : Int)) := kheap_lookup_i hd h10
  have h10' := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv ((i + 1 : Nat) : Int) false)) (b + 3))
    (x := "i") (env := kEnvB1 b) (a := ⟨b + 1⟩)
    (k := kGuardK b) (ch := ch) (c := u64cell ((i + 1 : Nat) : Int)) rfl l3)
  have h11 := sv_kgd n₀ nv m bs ivo
    (dead ++ kLive b cv ((i + 1 : Nat) : Int) false) (b + 3) b
    ((i + 1 : Nat) : Int) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5)
    (stepFnIter_one h6)) h7) h8) h9) h10') h11

/-- **Count READ**: test TRUE → `composite[i]` read and negated. 13
steps. -/
private theorem sv_kRead (n₀ nv ivo cv : Int) (m : Nat) (bs : List Bool)
    (i : Nat) (dead : Heap) (b : Nat) (ch : Choices)
    (hd : DeadFrom dead b) (h10 : 10 ≤ b)
    (him : i < m) (hilen : i < bs.length) :
    stepFnIter 13 (svStK n₀ nv m bs ivo dead b cv (i : Int) false)
        (.retV (.bool true) (cntCmpK b)) ch
      = .ok (.retV (.bool (!(bs.getD i false))) (cntNotIfK b),
          svStK n₀ nv m bs ivo dead b cv (i : Int) false, ch) := by
  show stepFnIter (10 + 1 + 1 + 1) _ _ _ = _
  have h1 := sv_kr1 n₀ nv m bs ivo (dead ++ kLive b cv (i : Int) false)
    (b + 3) b ch
  have l1 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv (i : Int) false)) (.base ⟨b + 1⟩)
      = some (u64cell (i : Int)) := kheap_lookup_i hd h10
  have h2 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b cv (i : Int) false)) (b + 3))
    (x := "i") (env := kEnvB2 b) (a := ⟨b + 1⟩)
    (k := .strictK .indexGet [svHandle m] [] (kEnvB2 b)
      (.strictK .not [] [] (kEnvB2 b) (cntNotIfK b)))
    (ch := ch) (c := u64cell (i : Int)) rfl l1)
  have h3 : stepFn (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b cv (i : Int) false)) (b + 3))
      (.retV (.int (i : Int) .uint64)
        (.strictK .indexGet [svHandle m] [] (kEnvB2 b)
          (.strictK .not [] [] (kEnvB2 b) (cntNotIfK b)))) ch
      = .ok (.retV (.bool (bs.getD i false))
          (.strictK .not [] [] (kEnvB2 b) (cntNotIfK b)),
        svSt (svFront n₀ nv m bs ivo false
          ++ (dead ++ kLive b cv (i : Int) false)) (b + 3), ch) :=
    stepFn_strict_apply (done := [svHandle m])
      (applyStrictOp_indexGet_slice (by with_unfolding_all rfl)
        (Nat.le_refl m) him (by rw [Nat.zero_add]; exact getElem?_mapB bs i hilen))
  have h4 := sv_knot (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b cv (i : Int) false)) (b + 3) b (bs.getD i false) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2)
    (stepFnIter_one h3)) h4

/-- **Count INCREMENT**: unmarked slot → `count := count + 1`, back at
the head. 19 steps. -/
private theorem sv_kInc (n₀ nv ivo : Int) (m : Nat) (bs : List Bool)
    (c : Nat) (iv2 : Int) (dead : Heap) (b : Nat) (ch : Choices)
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) (hc1 : c + 1 < 2 ^ 64) :
    stepFnIter 19 (svStK n₀ nv m bs ivo dead b (c : Int) iv2 false)
        (.retV (.bool true) (cntNotIfK b)) ch
      = .ok (cntHeadCfg b,
          svStK n₀ nv m bs ivo dead b ((c + 1 : Nat) : Int) iv2 false, ch) := by
  show stepFnIter (7 + 1 + 2 + 1 + 1 + 1 + 6) _ _ _ = _
  have h1 := sv_kincA (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3) b ch
  have l1 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b (c : Int) iv2 false)) (.base ⟨b⟩)
      = some (u64cell (c : Int)) := kheap_lookup_c hd h10
  have h2 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3))
    (x := "count") (env := kIncEnv b) (a := ⟨b⟩)
    (k := .strictK .add [] [.intLit 1 .uint64] (kIncEnv b) (kCntRhsK b))
    (ch := ch) (c := u64cell (c : Int)) rfl l1)
  have h3 := sv_kincB (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3) b (c : Int) ch
  have h4 : stepFn (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3))
      (.retV (.int 1 .uint64)
        (.strictK .add [.int (c : Int) .uint64] [] (kIncEnv b)
          (kCntRhsK b))) ch
      = .ok (.retV (.int ((c + 1 : Nat) : Int) .uint64) (kCntRhsK b),
          svSt (svFront n₀ nv m bs ivo false
            ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3), ch) :=
    stepFn_strict_apply (done := [.int (c : Int) .uint64])
      (applyStrictOp_add_u64 (b := 1) hc1)
  have h5 := sv_kincC (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3) b
    ((c + 1 : Nat) : Int) ch
  have hstRaw : storeTarget (svSt (svFront n₀ nv m bs ivo false
        ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3))
      (.chain (.addr (.base ⟨b⟩)) [] []) (.int ((c + 1 : Nat) : Int) .uint64)
      = .ok (svSt (Heap.set (svFront n₀ nv m bs ivo false
          ++ (dead ++ kLive b (c : Int) iv2 false)) (.base ⟨b⟩)
          (u64cell ((c + 1 : Nat) : Int))) (b + 3)) :=
    storeTarget_addr l1 (norm_u64_cell (unorm_nat_of_lt hc1))
  rw [kheap_set_c hd h10] at hstRaw
  have h6 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[]) (env := kIncEnv b)
    (k := .seq [] (kIncEnv b) (cntNotTail b)) (ch := ch) hstRaw)
  have h7 := sv_kincD (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b ((c + 1 : Nat) : Int) iv2 false)) (b + 3) b ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) (stepFnIter_one h4)) h5)
    h6) h7

/-- **Count EXIT**: test FALSE → the returned answer lands in the
harness result cell; terminal. 41 steps. -/
private theorem sv_kExit (n₀ nv ivo : Int) (m : Nat) (bs : List Bool)
    (c : Nat) (iv2 : Int) (dead : Heap) (b : Nat) (ch : Choices)
    (hd : DeadFrom dead b) (h10 : 10 ≤ b) (hc : c < 2 ^ 64) :
    stepFnIter 41 (svStK n₀ nv m bs ivo dead b (c : Int) iv2 false)
        (.retV (.bool false) (cntCmpK b)) ch
      = .ok (.next .stop,
          svStFin n₀ nv ((c : Nat) : Int) m bs ivo dead b (c : Int) iv2, ch) := by
  show stepFnIter (12 + 1 + 28) _ _ _ = _
  have h1 := sv_kx1 (svFront n₀ nv m bs ivo false
    ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3) b ch
  have l1 : Heap.lookup (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b (c : Int) iv2 false)) (.base ⟨b⟩)
      = some (u64cell (c : Int)) := kheap_lookup_c hd h10
  have h2 := stepFnIter_one (stepFn_var
    (σ := svSt (svFront n₀ nv m bs ivo false
      ++ (dead ++ kLive b (c : Int) iv2 false)) (b + 3))
    (x := "count") (env := kEnv b) (a := ⟨b⟩)
    (k := kEpiRhsK b) (ch := ch) (c := u64cell (c : Int)) rfl l1)
  have h3 := sv_kx6 n₀ nv ivo (c : Int) iv2 m bs dead b ch
  simp only [unorm_nat_of_lt hc] at h3
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- **The count loop**, by induction on the remaining window
`n + 1 - i`: from the `i <= n` test's delivery with the accumulator at
`c`, the run reaches the entry terminal with `c + countFrom bs n i` in
the harness result cell, within `61·d + 50` steps. -/
theorem sv_count_loop (n₀ ivo : Int) (n m : Nat) (hm : m = n + 1)
    (hn : n < 2 ^ 62) :
    ∀ d : Nat, ∀ i c : Nat, ∀ bs : List Bool, ∀ dead : Heap, ∀ b : Nat,
      ∀ ch : Choices, n + 1 - i ≤ d → c + (n + 2 - i) < 2 ^ 62 →
      i ≤ n + 1 → bs.length = m → DeadFrom dead b → 10 ≤ b →
      ∃ (k : Nat) (iv2' : Int), k ≤ 61 * d + 50 ∧
        stepFnIter k (svStK n₀ (n : Int) m bs ivo dead b (c : Int) (i : Int)
            false)
            (.retV (.bool (decide ((i : Int) ≤ (n : Int)))) (cntCmpK b)) ch
          = .ok (.next .stop,
              svStFin n₀ (n : Int) ((c + countFrom bs n i : Nat) : Int) m bs
                ivo dead b ((c + countFrom bs n i : Nat) : Int) iv2', ch) := by
  intro d
  induction d with
  | zero =>
    intro i c bs dead b ch hid hc hi1 hbs hdd h10
    have hgt : n < i := by omega
    rw [countFrom_stop bs n i hgt,
      show decide ((i : Int) ≤ (n : Int)) = false from
        decide_eq_false (by exact_mod_cast (by omega : ¬ (i ≤ n)))]
    refine ⟨41, (i : Int), by omega, ?_⟩
    have h := sv_kExit n₀ (n : Int) ivo m bs c (i : Int) dead b ch hdd h10
      (by omega)
    rw [show c + 0 = c from by omega]
    exact h
  | succ d ih =>
    intro i c bs dead b ch hid hc hi1 hbs hdd h10
    by_cases hle : i ≤ n
    · rw [show decide ((i : Int) ≤ (n : Int)) = true from
        decide_eq_true (by exact_mod_cast hle)]
      have hread := sv_kRead n₀ (n : Int) ivo (c : Int) m bs i dead b ch
        hdd h10 (by omega) (by omega)
      rw [countFrom_step bs n i hle]
      by_cases hmk : bs.getD i false = true
      · -- already marked: no increment
        rw [hmk] at hread
        have hskip := sv_kskip (svFront n₀ (n : Int) m bs ivo false
          ++ (dead ++ kLive b (c : Int) (i : Int) false)) (b + 3) b ch
        have hdisp := sv_kDisp n₀ (n : Int) ivo (c : Int) m bs i dead b ch
          hdd h10 (by omega)
        obtain ⟨k, iv2', hk, hrun⟩ := ih (i + 1) c bs dead b ch (by omega)
          (by omega) (by omega) hbs hdd h10
        rw [hmk, if_pos rfl]
        refine ⟨13 + 5 + 29 + k, iv2', by omega, ?_⟩
        rw [show c + (0 + countFrom bs n (i + 1)) = c + countFrom bs n (i + 1)
          from by omega]
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hread
          hskip) hdisp) hrun
      · -- unmarked: count += 1
        have hmk' : bs.getD i false = false := by
          cases h : bs.getD i false
          · rfl
          · exact absurd h hmk
        rw [hmk'] at hread
        have hinc := sv_kInc n₀ (n : Int) ivo m bs c (i : Int) dead b ch
          hdd h10 (by omega)
        have hdisp := sv_kDisp n₀ (n : Int) ivo ((c + 1 : Nat) : Int) m bs i
          dead b ch hdd h10 (by omega)
        obtain ⟨k, iv2', hk, hrun⟩ := ih (i + 1) (c + 1) bs dead b ch
          (by omega) (by omega) (by omega) hbs hdd h10
        rw [hmk', if_neg (by simp)]
        refine ⟨13 + 19 + 29 + k, iv2', by omega, ?_⟩
        rw [show c + (1 + countFrom bs n (i + 1))
          = (c + 1) + countFrom bs n (i + 1) from by omega]
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hread
          hinc) hdisp) hrun
    · have hgt : n < i := by omega
      rw [countFrom_stop bs n i hgt,
        show decide ((i : Int) ≤ (n : Int)) = false from
          decide_eq_false (by exact_mod_cast hle)]
      refine ⟨41, (i : Int), by omega, ?_⟩
      have h := sv_kExit n₀ (n : Int) ivo m bs c (i : Int) dead b ch hdd h10
        (by omega)
      rw [show c + 0 = c from by omega]
      exact h

/-! ## The outer loop -/

/-- A LATER outer dispatch, assembled: head (flag down) → `i := i + 1` →
the `i*i <= n` test's delivery. 33 steps. -/
private theorem sv_dispA1 (n₀ nv : Int) (m : Nat) (bs : List Bool) (i : Nat)
    (dead : Heap) (na : Nat) (ch : Choices)
    (hi64 : i + 1 < 2 ^ 64) (hsq : (i + 1) * (i + 1) < 2 ^ 64) :
    stepFnIter 33 (svStO n₀ nv m bs (i : Int) false dead na) svHeadCfg ch
      = .ok (.retV (.bool (decide ((((i + 1) * (i + 1) : Nat) : Int) ≤ nv)))
            outerCmpK,
          svStO n₀ nv m bs ((i + 1 : Nat) : Int) false dead na, ch) := by
  show stepFnIter (15 + 1 + 13 + 1 + 3) _ _ _ = _
  have h1 := sv_segA1a n₀ nv m bs (i : Int) dead na ch
  have h2 : stepFn (svStO n₀ nv m bs (i : Int) false dead na)
      (.retV (.int 1 .uint64)
        (.strictK .add [.int (i : Int) .uint64] [] oEnvB1 incRhsK)) ch
      = .ok (.retV (.int ((i + 1 : Nat) : Int) .uint64) incRhsK,
          svStO n₀ nv m bs (i : Int) false dead na, ch) :=
    stepFn_strict_apply (done := [.int (i : Int) .uint64])
      (applyStrictOp_add_u64 (b := 1) hi64)
  have h3 := sv_segA1b n₀ nv m bs (i : Int) ((i + 1 : Nat) : Int) dead na ch
  simp only [unorm_nat_of_lt hi64] at h3
  have h4 : stepFn (svStO n₀ nv m bs ((i + 1 : Nat) : Int) false dead na)
      (.retV (.int ((i + 1 : Nat) : Int) .uint64)
        (.strictK .mul [.int ((i + 1 : Nat) : Int) .uint64] [] oEnvB1
          oCmp2K)) ch
      = .ok (.retV (.int (((i + 1) * (i + 1) : Nat) : Int) .uint64) oCmp2K,
          svStO n₀ nv m bs ((i + 1 : Nat) : Int) false dead na, ch) :=
    stepFn_strict_apply (done := [.int ((i + 1 : Nat) : Int) .uint64])
      (applyStrictOp_mul_u64 hsq)
  have h5 := sv_segCmpN n₀ nv m bs ((i + 1 : Nat) : Int)
    (((i + 1) * (i + 1) : Nat) : Int) dead na ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 (stepFnIter_one h2)) h3) (stepFnIter_one h4)) h5

/-- **The outer loop**, by induction on `n + 1 - i`: from the
`i*i <= n` test's delivery the run reaches the count phase's sequence
with the table `sieveOuter n bs i`, within `(49·(n+1) + 200)·d + 6`
steps. The invariant `(i−1)² ≤ n+1` bounds every `i*i` the machine
computes below the uint64 wrap threshold (`i ≤ 2³¹ + 1`, so
`i² < 2⁶³`). -/
theorem sv_outer_loop (n₀ : Int) (n m : Nat) (hm : m = n + 1)
    (hn : n < 2 ^ 62) :
    ∀ d : Nat, ∀ i : Nat, ∀ bs : List Bool, ∀ dead : Heap, ∀ na : Nat,
      ∀ ch : Choices, n + 1 - i ≤ d → 2 ≤ i → (i - 1) * (i - 1) ≤ n + 1 →
      bs.length = m → DeadFrom dead na → 10 ≤ na →
      ∃ (k : Nat) (iv' : Int) (dead' : Heap) (na' : Nat),
        k ≤ (49 * (n + 1) + 200) * d + 6 ∧ DeadFrom dead' na' ∧ 10 ≤ na' ∧
        stepFnIter k (svStO n₀ (n : Int) m bs (i : Int) false dead na)
            (.retV (.bool (decide (((i * i : Nat) : Int) ≤ (n : Int))))
              outerCmpK) ch
          = .ok (.next postOuterK,
              svStO n₀ (n : Int) m (sieveOuter n bs i) iv' false dead' na',
              ch) := by
  intro d
  induction d with
  | zero =>
    intro i bs dead na ch hid hi2 hprev hbs hdd h10
    have hii : i * 1 ≤ i * i := Nat.mul_le_mul (Nat.le_refl i) (by omega)
    simp only [Nat.mul_one] at hii
    have hgt : n < i * i := by omega
    rw [sieveOuter_stop n bs i hgt,
      show decide (((i * i : Nat) : Int) ≤ (n : Int)) = false from
        decide_eq_false (by exact_mod_cast (by omega : ¬ (i * i ≤ n)))]
    exact ⟨6, (i : Int), dead, na, by omega, hdd, h10,
      sv_segOExit n₀ (n : Int) m bs (i : Int) dead na ch⟩
  | succ d ih =>
    intro i bs dead na ch hid hi2 hprev hbs hdd h10
    have hii1 : i * 1 ≤ i * i := Nat.mul_le_mul (Nat.le_refl i) (by omega)
    simp only [Nat.mul_one] at hii1
    have hile : i ≤ 2 ^ 31 + 1 := by
      rcases Nat.lt_or_ge (2 ^ 31 + 1) i with h | h
      · exfalso
        have h1 : 2 ^ 31 + 1 ≤ i - 1 := by omega
        have h2 : (2 ^ 31 + 1) * (2 ^ 31 + 1) ≤ (i - 1) * (i - 1) :=
          Nat.mul_le_mul h1 h1
        omega
      · exact h
    have hii64 : i * i < 2 ^ 64 := by
      have h2 : i * i ≤ (2 ^ 31 + 1) * (2 ^ 31 + 1) :=
        Nat.mul_le_mul hile hile
      omega
    have hsq1 : (i + 1) * (i + 1) < 2 ^ 64 := by
      have h2 : (i + 1) * (i + 1) ≤ (2 ^ 31 + 2) * (2 ^ 31 + 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have hmulsucc : (49 * (n + 1) + 200) * (d + 1)
        = (49 * (n + 1) + 200) * d + (49 * (n + 1) + 200) :=
      Nat.mul_succ _ _
    by_cases houter : i * i ≤ n
    · rw [show decide (((i * i : Nat) : Int) ≤ (n : Int)) = true from
        decide_eq_true (by exact_mod_cast houter)]
      have him : i < m := by omega
      have hB := sv_segB n₀ (n : Int) m bs (i : Int) dead na ch
      have hIdx : stepFn (svStO n₀ (n : Int) m bs (i : Int) false dead na)
          (.retV (.int (i : Int) .uint64)
            (.strictK .indexGet [svHandle m] [] oEnvB2 notK)) ch
          = .ok (.retV (.bool (bs.getD i false)) notK,
              svStO n₀ (n : Int) m bs (i : Int) false dead na, ch) :=
        stepFn_strict_apply (done := [svHandle m])
          (applyStrictOp_indexGet_slice (by with_unfolding_all rfl)
            (Nat.le_refl m) him
            (by rw [Nat.zero_add]; exact getElem?_mapB bs i (by omega)))
      have hNot := sv_segNot n₀ (n : Int) m bs (i : Int) dead na
        (bs.getD i false) ch
      rw [sieveOuter_step n bs i houter hi2]
      have hprev' : (i + 1 - 1) * (i + 1 - 1) ≤ n + 1 := by
        have h' : i + 1 - 1 = i := by omega
        rw [h']
        omega
      by_cases hmk : bs.getD i false = true
      · -- already marked: skip
        rw [hmk] at hIdx hNot
        have hSkip := sv_segSkip n₀ (n : Int) m bs (i : Int) dead na ch
        have hDisp := sv_dispA1 n₀ (n : Int) m bs i dead na ch (by omega) hsq1
        obtain ⟨k, iv', dead', na', hk, hdd', h10', hrun⟩ :=
          ih (i + 1) bs dead na ch (by omega) (by omega) hprev' hbs hdd h10
        rw [if_pos hmk]
        refine ⟨11 + 1 + 1 + 5 + 33 + k, iv', dead', na', by omega,
          hdd', h10', ?_⟩
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain hB (stepFnIter_one hIdx)) hNot)
          hSkip) hDisp) hrun
      · -- unmarked: the marking pass
        have hmk' : bs.getD i false = false := by
          cases h : bs.getD i false
          · rfl
          · exact absurd h hmk
        rw [hmk'] at hIdx hNot
        have hME := sv_markEntry n₀ (n : Int) m bs i dead na ch hdd h10 hii64
        obtain ⟨k₁, jv', hk₁, hrun₁⟩ := sv_mark_loop n₀ n m i hm (by omega)
          (by omega) hn (n + 1) (i * i) bs dead na ch (by omega) hbs hdd h10
        have hdd2 : DeadFrom (dead ++ mLive na jv' false) (na + 2) :=
          DeadFrom.push2 hdd
        have hDisp := sv_dispA1 n₀ (n : Int) m (markFrom n i bs (i * i)) i
          (dead ++ mLive na jv' false) (na + 2) ch (by omega) hsq1
        obtain ⟨k, iv', dead', na', hk, hdd', h10', hrun⟩ :=
          ih (i + 1) (markFrom n i bs (i * i)) (dead ++ mLive na jv' false)
            (na + 2) ch (by omega) (by omega) hprev'
            (by rw [markFrom_length]; exact hbs) hdd2 (by omega)
        rw [if_neg hmk]
        refine ⟨11 + 1 + 1 + 60 + k₁ + (33 + k), iv', dead', na', by omega,
          hdd', h10', ?_⟩
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain hB (stepFnIter_one hIdx)) hNot)
          hME) hrun₁) (stepFnIter_chain hDisp hrun)
    · rw [sieveOuter_stop n bs i (by omega),
        show decide (((i * i : Nat) : Int) ≤ (n : Int)) = false from
          decide_eq_false (by exact_mod_cast houter)]
      exact ⟨6, (i : Int), dead, na, by omega, hdd, h10,
        sv_segOExit n₀ (n : Int) m bs (i : Int) dead na ch⟩

/-! ## The end-to-end run -/

/-- **The run, end to end**: from the machine entry's post-prelude seed
the harness reaches the entry terminal within
`(n+1)·(49·(n+1) + 261) + 300` steps, with `primeCount n` in the
harness result cell. -/
theorem sv_runs (n : Nat) (hn : n < 2 ^ 62) (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ (n + 1) * (49 * (n + 1) + 261) + 300 ∧
      stepFnIter k (svSeed0 (n : Int)) svC00 ch = .ok (.next .stop, σf, ch) ∧
      loadMany σf [.base ⟨1⟩]
        = .ok [.int ((primeCount n : Nat) : Int) .uint64] := by
  have hE0 := sv_segE0 (n : Int) ch
  rw [unorm_nat_of_lt (by omega : n < 2 ^ 64)] at hE0
  by_cases hn2 : n < 2
  · -- the n < 2 guard: return 0
    rw [show decide ((n : Int) < 2) = true from
      decide_eq_true (by exact_mod_cast hn2)] at hE0
    have hGT := sv_segGT (n : Int) (n : Int) ch
    have h0 : primeCount n = 0 := by
      rw [← sieveAnswer_eq]
      simp only [sieveAnswer, if_pos hn2]
    refine ⟨17 + 38, svStG (n : Int) (n : Int), by omega,
      stepFnIter_chain hE0 hGT, ?_⟩
    rw [h0]
    with_unfolding_all rfl
  · -- the full pipeline
    have hnge : 2 ≤ n := by omega
    rw [show decide ((n : Int) < 2) = false from
      decide_eq_false (by exact_mod_cast (by omega : ¬ (n < 2)))] at hE0
    have hE1 := sv_segE1 (n : Int) (n : Int) ch
    rw [show ((n : Int) + 1) = ((n + 1 : Nat) : Int) from by omega,
      unorm_nat_of_lt (by omega : n + 1 < 2 ^ 64)] at hE1
    have hMS := stepFnIter_one (stepFn_stmtOp_apply (nt := 1)
      (done := [.addr (.base ⟨5⟩)]) (env := c0Env) (k := msTailK)
      (sv_makeSlice (n : Int) (n : Int) (n + 1) ch))
    have hE2 := sv_segE2 (n : Int) (n : Int) (n + 1)
      (List.replicate (n + 1) false) ch
    have hA0 := sv_segA0 (n : Int) (n : Int) (n + 1)
      (List.replicate (n + 1) false) 2 [] 10 ch
    have hMul2 : stepFn (svStO (n : Int) (n : Int) (n + 1)
          (List.replicate (n + 1) false) 2 false [] 10)
        (.retV (.int ((2 : Nat) : Int) .uint64)
          (.strictK .mul [.int ((2 : Nat) : Int) .uint64] [] oEnvB1 oCmp2K))
        ch
        = .ok (.retV (.int ((2 * 2 : Nat) : Int) .uint64) oCmp2K,
            svStO (n : Int) (n : Int) (n + 1)
              (List.replicate (n + 1) false) 2 false [] 10, ch) :=
      stepFn_strict_apply (done := [.int ((2 : Nat) : Int) .uint64])
        (applyStrictOp_mul_u64 (by omega))
    have hCmp := sv_segCmpN (n : Int) (n : Int) (n + 1)
      (List.replicate (n + 1) false) 2 ((2 * 2 : Nat) : Int) [] 10 ch
    obtain ⟨k₁, iv', dead', na', hk₁, hdd', h10', hrun₁⟩ :=
      sv_outer_loop (n : Int) n (n + 1) rfl hn (n + 1) 2
        (List.replicate (n + 1) false) [] 10 ch (by omega) (by omega)
        (by omega) (by simp) (fun x _ => rfl) (by omega)
    have hKI := sv_kInit (n : Int) (n : Int) iv' (n + 1)
      (sieveOuter n (List.replicate (n + 1) false) 2) dead' na' ch hdd' h10'
    have hKD1 := sv_kDisp1 (n : Int) (n : Int) iv' 0 2 (n + 1)
      (sieveOuter n (List.replicate (n + 1) false) 2) dead' na' ch hdd' h10'
    obtain ⟨k₂, iv2', hk₂, hrun₂⟩ :=
      sv_count_loop (n : Int) iv' n (n + 1) rfl hn (n + 1) 2 0
        (sieveOuter n (List.replicate (n + 1) false) 2) dead' na' ch
        (by omega) (by omega) (by omega)
        (by rw [sieveOuter_length]; simp) hdd' h10'
    rw [Nat.zero_add] at hrun₂
    have hansEq : countFrom (sieveOuter n (List.replicate (n + 1) false) 2)
        n 2 = primeCount n := by
      rw [← sieveAnswer_eq]
      simp only [sieveAnswer, if_neg (by omega : ¬ (n < 2))]
      rfl
    rw [hansEq] at hrun₂
    have halg : (n + 1) * (49 * (n + 1) + 261)
        = (49 * (n + 1) + 200) * (n + 1) + 61 * (n + 1) := by
      rw [show 49 * (n + 1) + 261 = (49 * (n + 1) + 200) + 61 from by omega,
        Nat.mul_add, Nat.mul_comm (n + 1) (49 * (n + 1) + 200),
        Nat.mul_comm (n + 1) 61]
    refine ⟨17 + 15 + 1 + 42 + 25 + 1 + 3 + (k₁ + 42 + 25) + k₂,
      svStFin (n : Int) (n : Int) ((primeCount n : Nat) : Int) (n + 1)
        (sieveOuter n (List.replicate (n + 1) false) 2) iv' dead' na'
        ((primeCount n : Nat) : Int) iv2', by omega, ?_, ?_⟩
    · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain hE0 hE1) hMS) hE2) hA0)
        (stepFnIter_one hMul2)) hCmp)
        (stepFnIter_chain (stepFnIter_chain hrun₁ hKI) hKD1)) hrun₂
    · with_unfolding_all rfl
