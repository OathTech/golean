import GoLeanProofs.Examples.SliceQueueProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq
import GoLeanProofs.Frame.Sim
import GoLeanProofs.Laws.StmtOps

/-!
# SliceQueue — the `queue` example (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/queue/main.go` (13 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/queue-lowered.repr`
and carried in `GoLeanProofs.Examples.SliceQueueProgram`.

The subject is a queue over `[]uint64`: `enqueue` is Go's `append`
(at the back), `dequeue` reads `q[0]` and re-slices `q[1:]` (the
front). FIFO order is the property of interest — the deliberate mirror
of the `stack` example's LIFO. The harness `queue_harness_r(n, seed, k)`
is the S3 RELATIONAL shape: enqueue the family `seed + i` (wrapping)
for `i < n`, recording each value into `enqueued`; dequeue
`d := min(k, n)` values (the min written explicitly), recording them in
dequeue order into `dequeued`; return `(enqueued, dequeued, qsize(q))`.
FIFO is `enqueued.take k` in the postcondition — where the stack's
mirror entry says `pushed.reverse.take k`.

**STATUS (G1.8, 2026-08-15): COMPLETE.** `queue_ok` and its
run-conditioned twin `queue_readout` are stated in this root (the
C-H4/C-H5 shape) and proved with zero `sorry`, the standard axiom trio,
no `native_decide` and no per-theorem heartbeat overrides. The
per-example axiom shard is `proofs/Audit/SliceQueue.lean`; the gallery
entry is in `docs/verified-examples.md`.

The layers below the headline, in the order they compose:

* the guardrails-wave stub content (the byte-derived harness
  transcription `queueHarnessRFunc` and its `rfl` pin), kept verbatim,
  plus the subject pins `enqueue_pin` / `dequeue_pin` / `qsize_pin`;
* the pure layer (`qFam`, `qPre`, `qBack`, the FIFO take-bridge
  `qFam_take`);
* the ENQUEUE PHASE, capacity- and address-GENERIC at every choice
  stream: `qe_E0_raw`/`qe_A0_raw` (entry), the per-iteration segment
  layer, `qe_pre`/`qe_post`/`qe_iter` (exactly 130 steps per enqueue on
  BOTH the in-place and the spill path) and `qe_loop` (`130·(n−j)`
  steps, existential over backing address/capacity/tail/stream —
  `qEnqInv`);
* the executable `append` facts this required — the gallery's first
  proofs THROUGH a growing slice: `qappend_inplace`, `qappend_spill`
  (ONE choice consumed, capacity `qSpillCap C extra` ranging over the
  machine's envelope), `buildAppendBacking_u64`,
  `sliceVisibleValues_u64`;
* the min-branch `qx_toHead` (61 steps, or 73 when `n < k`, both
  branches landing `d = min k n` and the four dequeue-loop cells);
* the DEQUEUE PHASE, entirely CHOICE-FREE: `qd_head` (25 steps), the
  `dequeue` callee `qd_callee` (49 steps — the `q[0]` read at the
  moving offset off the untouched backing, the `q[1:len(q)]` re-slice
  via `applyStrictOp_sliceExpr_slice`, both result stores), `qd_iter`
  (117 steps for one iteration) and `qd_loop` (`117·(m−j)`);
* the 72-step exit epilogue `q_exit`, the readback `q_readback`, the
  entry equation `qH_entry_eq` (from `derive_entry_eq` over `qProg`),
  and `q_run` — the whole harness in exactly
  `242 + 130·n + 117·min(k,n) + 12·[n < k]` steps at EVERY choice
  stream, existentially packaging the choice-dependent backing address,
  capacity, final tail, allocation front and leftover stream.

The shipped fuel bound in `queue_ok` is `247·n + 254`, which is a BOUND
— exactly attained when `k > n` and loose by `117·(n − k) + 12`
otherwise. It is not the measured count; `q_run` carries that.

**`∀ ch` does REAL WORK in this example** (unlike every earlier
non-map entry): the machine models `append`'s spill capacity as a
NONDETERMINISM ENVELOPE — a spilling append consumes one choice from
the stream and the realized capacity ranges over
`[newLen, appendSpillUpper]`. The enqueue-phase proofs are
capacity-generic, so they survive a re-envelope of `append`. The
DEQUEUE half consumes nothing: `q[1:]` only advances a header offset,
which is also why an enqueue costs 130 steps and a dequeue 117.

HOUSE RULE from this unit (the elaboration-storm class): state every
custom conditioned lemma over `(qSt σ H na)` with hypotheses on the
PLAIN `H`/`na` — never over `σ.heap`/`σ.nextAddr` projections. A
`DeadFrom`-typed argument spelled over state projections drops the
unifier into unbounded `Heap.lookup` δ-unfolding (measured: ~68k
unfoldings, 2M heartbeats); lookup-`Eq` atoms are safe either way.
The finishing session widened the same class twice more, both measured:
a lemma whose hypotheses are stated over `σ.heap` PROJECTIONS costs
>3M heartbeats at a literal-tail state (fix: a wrapper quantified over
the explicit `H`), and inline `by`-tactic arguments inside applications
at huge states compound identically (fix: pre-state every argument as a
named `have`). Together those took `qd_iter` from uncompilable at
40 min to 63 s.
-/

namespace GoLean.Examples.SliceQueue

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def queueHarnessRFunc : Func :=
{ id := { key := "queue_harness_r" },
  args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "k", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0",
                 typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
               { id := "$res1",
                 typ := GoLean.GoCore.Ty.array 8 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
               { id := "$res2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c7",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                  GoLean.GoCore.Stmt.makeSlice
                    (GoLean.GoCore.Assignee.var "$c7")
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                    (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                    (some (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "q",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "q")
                    (GoLean.GoCore.Expr.var "$c7")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "enqueued",
                      typ := GoLean.GoCore.Ty.array
                               8
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
              GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.seqn
                    #[GoLean.GoCore.Stmt.initialization
                        { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                      GoLean.GoCore.Stmt.assign
                        (GoLean.GoCore.Assignee.var "i")
                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.initialization
                        { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                      GoLean.GoCore.Stmt.assign
                        (GoLean.GoCore.Assignee.var "$forFirst")
                        (GoLean.GoCore.Expr.boolLit true),
                      GoLean.GoCore.Stmt.while
                        (GoLean.GoCore.Expr.boolLit true)
                        (GoLean.GoCore.Stmt.block
                          #[]
                          #[GoLean.GoCore.Stmt.ifThenElse
                              (GoLean.GoCore.Expr.var "$forFirst")
                              (GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "$forFirst")
                                (GoLean.GoCore.Expr.boolLit false))
                              (GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "i")
                                (GoLean.GoCore.Expr.add
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                            GoLean.GoCore.Stmt.seqn #[],
                            GoLean.GoCore.Stmt.ifThenElse
                              (GoLean.GoCore.Expr.lessCmp
                                (GoLean.GoCore.Expr.var "i")
                                (GoLean.GoCore.Expr.var "n"))
                              (GoLean.GoCore.Stmt.seqn #[])
                              (GoLean.GoCore.Stmt.breakStmt),
                            GoLean.GoCore.Stmt.block
                              #[]
                              #[GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "v",
                                        typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                    GoLean.GoCore.Stmt.assign
                                      (GoLean.GoCore.Assignee.var "v")
                                      (GoLean.GoCore.Expr.add
                                        (GoLean.GoCore.Expr.var "seed")
                                        (GoLean.GoCore.Expr.var "i"))],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.call
                                      #[GoLean.GoCore.Assignee.var "q"]
                                      { key := "enqueue" }
                                      #[GoLean.GoCore.Expr.var "q", GoLean.GoCore.Expr.var "v"]],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.assign
                                      (GoLean.GoCore.Assignee.addr
                                        (GoLean.GoCore.Expr.indexAddr
                                          (GoLean.GoCore.Expr.ref "enqueued")
                                          (GoLean.GoCore.Expr.var "i")))
                                      (GoLean.GoCore.Expr.var "v")]]])]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "d", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "d") (GoLean.GoCore.Expr.var "k")],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.lessCmp (GoLean.GoCore.Expr.var "n") (GoLean.GoCore.Expr.var "k"))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "d")
                          (GoLean.GoCore.Expr.var "n")]])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "dequeued",
                      typ := GoLean.GoCore.Ty.array
                               8
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) }],
              GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.seqn
                    #[GoLean.GoCore.Stmt.initialization
                        { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                      GoLean.GoCore.Stmt.assign
                        (GoLean.GoCore.Assignee.var "i")
                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.initialization
                        { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                      GoLean.GoCore.Stmt.assign
                        (GoLean.GoCore.Assignee.var "$forFirst")
                        (GoLean.GoCore.Expr.boolLit true),
                      GoLean.GoCore.Stmt.while
                        (GoLean.GoCore.Expr.boolLit true)
                        (GoLean.GoCore.Stmt.block
                          #[]
                          #[GoLean.GoCore.Stmt.ifThenElse
                              (GoLean.GoCore.Expr.var "$forFirst")
                              (GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "$forFirst")
                                (GoLean.GoCore.Expr.boolLit false))
                              (GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "i")
                                (GoLean.GoCore.Expr.add
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                            GoLean.GoCore.Stmt.seqn #[],
                            GoLean.GoCore.Stmt.ifThenElse
                              (GoLean.GoCore.Expr.lessCmp
                                (GoLean.GoCore.Expr.var "i")
                                (GoLean.GoCore.Expr.var "d"))
                              (GoLean.GoCore.Stmt.seqn #[])
                              (GoLean.GoCore.Stmt.breakStmt),
                            GoLean.GoCore.Stmt.block
                              #[]
                              #[GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "v",
                                        typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.call
                                      #[GoLean.GoCore.Assignee.var "q", GoLean.GoCore.Assignee.var "v"]
                                      { key := "dequeue" }
                                      #[GoLean.GoCore.Expr.var "q"]],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.assign
                                      (GoLean.GoCore.Assignee.addr
                                        (GoLean.GoCore.Expr.indexAddr
                                          (GoLean.GoCore.Expr.ref "dequeued")
                                          (GoLean.GoCore.Expr.var "i")))
                                      (GoLean.GoCore.Expr.var "v")]]])]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c8", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c8"]
                    { key := "qsize" }
                    #[GoLean.GoCore.Expr.var "q"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "enqueued"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res1")
                    (GoLean.GoCore.Expr.var "dequeued"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res2")
                    (GoLean.GoCore.Expr.var "$c8"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem queueHarnessRFunc_pin :
    findFunctionIn? queueLowered.funcs ⟨"queue_harness_r"⟩
    = some queueHarnessRFunc := rfl

open GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64
abbrev sliceU : Ty := .slice tU64

/-! ## The statement vocabulary -/

/-- The returned fixed-cap array: the observed value list, zero-padded to
the harness's `queueCapN = 8` slots. Deliberately NOT shared with the
identically shaped arrays of other examples (the §11 closure rule). -/
def qArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map (fun v => .int v .uint64)⟩

/-! ## The subject `Func`s, verbatim from the pinned lowering -/

/-- `enqueue(q, v) = append(q, v)` — the frontend lowers the appended
element through a one-element temporary slice `$c0`. Verbatim from the
pinned lowering (the pin below ties it by `rfl`). -/
def enqueueFunc : Func :=
  { id := { key := "enqueue" },
    args := #[{ id := "q", typ := sliceU }, { id := "v", typ := tU64 }],
    results := #[{ id := "$res0", typ := sliceU }],
    body := .block #[]
      #[.seqn #[.initialization { id := "$c0", typ := sliceU },
                .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
                  (some (.intLit 1 .int)),
                .assign (.addr (.indexAddr (.var "$c0") (.intLit 0 .int)))
                  (.var "v")],
        .seqn #[.initialization { id := "$c1", typ := sliceU },
                .appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0")],
        .seqn #[.assign (.var "$res0") (.var "$c1"), .returnStmt]],
    variadic := false,
    wrapper := false }

/-- `dequeue(q) = (q[1:len(q)], q[0])`. Verbatim from the pinned
lowering. -/
def dequeueFunc : Func :=
  { id := { key := "dequeue" },
    args := #[{ id := "q", typ := sliceU }],
    results := #[{ id := "$res0", typ := sliceU },
                 { id := "$res1", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "v", typ := tU64 },
                .assign (.var "v")
                  (.indexGet (.var "q") (.intLit 0 .int))],
        .seqn #[.assign (.var "$res0")
                  (.slice (.var "q") (.intLit 1 .int)
                    (.length (.var "q") (some sliceU)) none),
                .assign (.var "$res1") (.var "v"),
                .returnStmt]],
    variadic := false,
    wrapper := false }

/-- `qsize(q) = uint64(len(q))`. Verbatim from the pinned lowering. -/
def qsizeFunc : Func :=
  { id := { key := "qsize" },
    args := #[{ id := "q", typ := sliceU }],
    results := #[{ id := "$res0", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.assign (.var "$res0")
                  (.convert tU64 (.length (.var "q") (some sliceU))),
                .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The subject pin: `enqueue` IS the frontend's lowering. -/
theorem enqueue_pin :
    findFunctionIn? queueLowered.funcs ⟨"enqueue"⟩ = some enqueueFunc := rfl

/-- The subject pin: `dequeue` IS the frontend's lowering. -/
theorem dequeue_pin :
    findFunctionIn? queueLowered.funcs ⟨"dequeue"⟩ = some dequeueFunc := rfl

/-- The observation pin: `qsize` IS the frontend's lowering. -/
theorem qsize_pin :
    findFunctionIn? queueLowered.funcs ⟨"qsize"⟩ = some qsizeFunc := rfl

/-! ## The enqueue family and the fixed-cap prefixes

`qFam n seed = [seed+0, seed+1, …]` WRAPPED mod 2^64 elementwise.
Near-dup note (kit, GAP-P2b): `SliceMem.familyMod k` is `seed + i%k`;
the affine family `seed + i` still has no kit form — this module is its
5th consumer (after minmax, dotprod, and the two loop mirrors there);
re-derived minimally below, promotion still owed. The zero-padded
prefix reuses the kit's `prefixPad` generically (GAP-P2 lift). -/

def qFam (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))

theorem qFam_length (n seed : Nat) : (qFam n seed).length = n :=
  familyF_length id n seed

theorem qFam_range (n seed : Nat) :
    ∀ v ∈ qFam n seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  familyF_range id n seed

theorem qFam_succ (i seed : Nat) :
    qFam (i + 1) seed
      = qFam i seed ++ [(((seed + i) % 2 ^ 64 : Nat) : Int)] :=
  familyF_succ id i seed

theorem qFam_getD {n seed m : Nat} (hm : m < n) :
    (qFam n seed).getD m 0 = (((seed + m) % 2 ^ 64 : Nat) : Int) :=
  familyF_getD (f := id) hm

/-- FIFO's list form: the first `k` enqueued values are the family's
`min k n`-prefix. -/
theorem qFam_take (k n seed : Nat) :
    (qFam n seed).take k = qFam (min k n) seed := by
  simp [qFam, ← List.map_take, List.take_range]

/-- The `enqueued`/`dequeued` array after `m` stores: the family
prefix, zero tail (the kit's `prefixPad`). -/
def qPre (m seed : Nat) : List Int := prefixPad qFam 8 m seed

theorem qPre_zero (seed : Nat) : qPre 0 seed = List.replicate 8 0 :=
  prefixPad_zero rfl

theorem qPre_length {m seed : Nat} (h : m ≤ 8) : (qPre m seed).length = 8 :=
  prefixPad_length (qFam_length m seed) h

theorem qPre_range {m seed : Nat} :
    ∀ v ∈ qPre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (qFam_range m seed)

theorem qPre_set {seed m : Nat} (hm : m < 8) :
    (qPre m seed).set m (((seed + m) % 2 ^ 64 : Nat) : Int)
      = qPre (m + 1) seed :=
  prefixPad_familyF_set (f := id) hm

theorem qPre_full {n seed : Nat} :
    qPre n seed
      = qFam n seed ++ List.replicate (8 - (qFam n seed).length) 0 :=
  prefixPad_full (qFam_length n seed)

/-- The backing array of the queue slice after `i` enqueues at
capacity `C`: the family prefix, zero-filled to the capacity. -/
def qBack (C i seed : Nat) : List Int :=
  qFam i seed ++ List.replicate (C - i) 0

theorem qBack_length {C i seed : Nat} (h : i ≤ C) :
    (qBack C i seed).length = C := by
  rw [qBack, List.length_append, qFam_length, List.length_replicate]
  omega

theorem qBack_range {C i seed : Nat} :
    ∀ v ∈ qBack C i seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact qFam_range i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

/-- Reading the backing at an in-family index. -/
theorem qBack_getD {C i seed j : Nat} (hj : j < i) :
    (qBack C i seed).getD j 0 = (((seed + j) % 2 ^ 64 : Nat) : Int) := by
  rw [qBack, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [qFam_length]; omega),
    ← List.getD_eq_getElem?_getD, qFam_getD hj]

/-! ## Machine vocabulary: cells, fronts, states -/

abbrev u64cell (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev arrCellU (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev slCell (v : GoValue) : HeapCell := ⟨some sliceU, v⟩
abbrev zeros8 : List Int := List.replicate 8 0

/-- A queue slice handle: base `B`, offset `off`, length `len`,
capacity `cap`. -/
abbrev qslV (B off len cap : Nat) : GoValue :=
  .slice ⟨some (.base ⟨B⟩), off, len, cap⟩

/-- The PROGRAM-generic state form. -/
abbrev qSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-- The entry heap: three argument cells, three result cells. -/
def qHeap0 (nv sv kv : Int) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv), (.base ⟨2⟩, u64cell kv),
   (.base ⟨3⟩, arrCellU 8 zeros8), (.base ⟨4⟩, arrCellU 8 zeros8),
   (.base ⟨5⟩, u64cell 0)]

/-- The post-prelude FRONT: the twelve fixed-address cells every later
phase keeps (arguments, results, `$c7` and its empty backing, `q`,
`enqueued`, the enqueue loop's `i` and `$forFirst`). Everything the run
allocates after these lives in the symbolic tail BEHIND them. -/
def qFront (nv sv kv : Int) (r0 r1 : List Int) (r2 : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv), (.base ⟨2⟩, u64cell kv),
   (.base ⟨3⟩, arrCellU 8 r0), (.base ⟨4⟩, arrCellU 8 r1),
   (.base ⟨5⟩, u64cell r2),
   (.base ⟨6⟩, slCell (qslV 7 0 0 0)), (.base ⟨7⟩, arrCellU 0 []),
   (.base ⟨8⟩, slCell qv), (.base ⟨9⟩, arrCellU 8 lE),
   (.base ⟨10⟩, u64cell iv), (.base ⟨11⟩, bcell ff)]

/-- The enqueue-phase state: front (results still zero) + tail. -/
abbrev qStE (σ : ExecState) (nv sv kv : Int) (qv : GoValue) (lE : List Int)
    (iv : Int) (ff : Bool) (tail : Heap) (na : Nat) : ExecState :=
  qSt σ (qFront nv sv kv zeros8 zeros8 0 qv lE iv ff ++ tail) na

/-- The front misses every address from 12 up. -/
theorem qFront_miss {nv sv kv : Int} {r0 r1 : List Int} {r2 : Int}
    {qv : GoValue} {lE : List Int} {iv : Int} {ff : Bool} {x : Nat}
    (hx : 12 ≤ x) :
    Heap.lookup (qFront nv sv kv r0 r1 r2 qv lE iv ff) (.base ⟨x⟩) = none := by
  simp only [qFront]
  rw [lookup_cons_ne (base_beq_false (by omega : 0 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 3 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 4 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 5 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 6 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 7 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 8 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 9 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 10 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : 11 ≠ x))]
  rfl

/-- Freshness of a front + tail heap from `na` up. -/
theorem qHeap_dead {nv sv kv : Int} {r0 r1 : List Int} {r2 : Int}
    {qv : GoValue} {lE : List Int} {iv : Int} {ff : Bool} {tail : Heap}
    {na : Nat} (h12 : 12 ≤ na) (htail : DeadFrom tail na) :
    DeadFrom (qFront nv sv kv r0 r1 r2 qv lE iv ff ++ tail) na := by
  intro x hx
  rw [lookup_append_right (qFront_miss (by omega))]
  exact htail x hx

/-! ## The harness body's statement pieces (readable spellings; the raw
segments below re-check every transcription by `rfl` against the pinned
lowering's monolith). -/

def qeVSeqn : Stmt :=
  .seqn #[.initialization { id := "v", typ := tU64 },
          .assign (.var "v") (.add (.var "seed") (.var "i"))]
def qeCallSeqn : Stmt :=
  .seqn #[.call #[.var "q"] ⟨"enqueue"⟩ #[.var "q", .var "v"]]
def qeStoreSeqn : Stmt :=
  .seqn #[.assign (.addr (.indexAddr (.ref "enqueued") (.var "i")))
    (.var "v")]
def qeFill : Stmt := .block #[] #[qeVSeqn, qeCallSeqn, qeStoreSeqn]
def qeBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
      qeFill]

def qdVSeqn : Stmt := .seqn #[.initialization { id := "v", typ := tU64 }]
def qdCallSeqn : Stmt :=
  .seqn #[.call #[.var "q", .var "v"] ⟨"dequeue"⟩ #[.var "q"]]
def qdStoreSeqn : Stmt :=
  .seqn #[.assign (.addr (.indexAddr (.ref "dequeued") (.var "i")))
    (.var "v")]
def qdFill : Stmt := .block #[] #[qdVSeqn, qdCallSeqn, qdStoreSeqn]
def qdBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[]) .breakStmt,
      qdFill]

def qT5 : Stmt :=
  .seqn #[.initialization { id := "d", typ := tU64 },
          .assign (.var "d") (.var "k")]
def qT6 : Stmt :=
  .ifThenElse (.lessCmp (.var "n") (.var "k"))
    (.block #[] #[.seqn #[.assign (.var "d") (.var "n")]])
    (.seqn #[])
def qT7 : Stmt :=
  .seqn #[.initialization { id := "dequeued", typ := .array 8 tU64 }]
def qT8 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) qdBody]]
def qT9 : Stmt :=
  .seqn #[.initialization { id := "$c8", typ := tU64 },
          .call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"]]
def qT10 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "enqueued"),
          .assign (.var "$res1") (.var "dequeued"),
          .assign (.var "$res2") (.var "$c8"),
          .returnStmt]

/-! ## Environments -/

def baseScope : Scope :=
  [("$res2", .base ⟨5⟩), ("$res1", .base ⟨4⟩), ("$res0", .base ⟨3⟩),
   ("k", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def hScope : Scope :=
  [("enqueued", .base ⟨9⟩), ("q", .base ⟨8⟩), ("$c7", .base ⟨6⟩)]
def qeEnv : LocalEnv :=
  [[("$forFirst", .base ⟨11⟩)], [("i", .base ⟨10⟩)], hScope, baseScope]
def qeEnv1 : LocalEnv := [] :: qeEnv
def qeEnv2 : LocalEnv := [] :: qeEnv1
/-- The fill env after `v` is declared at the (symbolic) address `a`. -/
def qeEnvV (a : Nat) : LocalEnv := [("v", .base ⟨a⟩)] :: qeEnv1

/-- The `enqueue` callee frame scope (params `q`,`v`, result `$res0`,
allocated at `a+1..a+3` where `a` is the caller's `v` cell). -/
def eqScope (a : Nat) : Scope :=
  [("$res0", .base ⟨a + 3⟩), ("v", .base ⟨a + 2⟩), ("q", .base ⟨a + 1⟩)]
def eqEnv (a : Nat) : LocalEnv := [eqScope a]
def eqEnvC0 (a : Nat) : LocalEnv := [("$c0", .base ⟨a + 4⟩)] :: eqEnv a
def eqEnvC1 (a : Nat) : LocalEnv :=
  [("$c1", .base ⟨a + 6⟩), ("$c0", .base ⟨a + 4⟩)] :: eqEnv a

/-! ## Continuations (enqueue phase) -/

def qStop : Cont := .frame [] [] [] [] .stop

/-- After the enqueue loop: the remaining six top-level statements. -/
def tailAfterEnq : Cont := .seq [qT5, qT6, qT7, qT8, qT9, qT10]
  [hScope, baseScope] qStop
def qeHeadTail : Cont :=
  .seq [] qeEnv
    (.seq [] [[("i", .base ⟨10⟩)], hScope, baseScope] tailAfterEnq)
def qeHeadCfg : Config := .exec (.while (.boolLit true) qeBody) qeEnv qeHeadTail
def qeLoopK : Cont := .loop (.boolLit true) qeBody qeEnv qeHeadTail
def qeCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt qeEnv1 (.seq [qeFill] qeEnv1 qeLoopK)

def qePlans : List (TargetShape × List Expr) := [(.chain [], [.ref "q"])]
/-- The caller continuation the `enqueue` frame returns into. -/
def qeAfterCallK (a : Nat) : Cont :=
  .seq [qeStoreSeqn] (qeEnvV a) (.seq [] qeEnv1 qeLoopK)
def qeVTail (a : Nat) : Cont :=
  .seq [qeCallSeqn, qeStoreSeqn] (qeEnvV a) (.seq [] qeEnv1 qeLoopK)
def qeCallArgsK (a : Nat) (qv : GoValue) : Cont :=
  .callArgsK ⟨"enqueue"⟩ qePlans [qv] [] (qeEnvV a) (qeAfterCallK a)
def qeFrameK (a : Nat) : Cont :=
  .frame qePlans (qeEnvV a) [.base ⟨a + 3⟩] [] (qeAfterCallK a) false

/-! ### The `enqueue` callee's statement pieces and continuations -/

def eqC0Assign : Stmt :=
  .assign (.addr (.indexAddr (.var "$c0") (.intLit 0 .int))) (.var "v")
def eqC1Seqn : Stmt :=
  .seqn #[.initialization { id := "$c1", typ := sliceU },
          .appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0")]
def eqRetSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c1"), .returnStmt]

/-- After `$c0` is declared: the makeSlice statement is next. -/
def eqKmk (a : Nat) : Cont :=
  .seq [eqC0Assign, eqC1Seqn, eqRetSeqn] (eqEnvC0 a) (qeFrameK a)
/-- After the make: the `$c0[0] = v` store statement's continuation. -/
def eqTail2 (a : Nat) : Cont :=
  .seq [eqC1Seqn, eqRetSeqn] (eqEnvC0 a) (qeFrameK a)
/-- The `$c0[0]` target spine at the `$c0` read. -/
def eqTgtK (a : Nat) : Cont :=
  .tgtOpK (.chain [.index]) [] [.intLit 0 .int] [] [] .vals [.var "v"] []
    (.seqn #[]) (eqEnvC0 a) (eqTail2 a)
/-- The `$c0[0] = v` rhs spine at the `v` read. -/
def eqRhsK (a : Nat) : Cont :=
  .rhsK .vals [.chain (qslV (a + 5) 0 1 1) [.int 0 .int] [.index]] [] []
    (.seqn #[]) (eqEnvC0 a) (eqTail2 a)
/-- After the append: the return sequence. -/
def eqKapp (a : Nat) : Cont :=
  .seq [eqRetSeqn] (eqEnvC1 a) (qeFrameK a)
/-- The append operand spine at the `q` read. -/
def eqAppK1 (a : Nat) : Cont :=
  .stmtOpK (.appendSlice tU64) 1 [.addr (.base ⟨a + 6⟩)] [.var "$c0"]
    (eqEnvC1 a) (eqKapp a)
/-- The append operand spine at the `$c0` read. -/
def eqAppK2 (a : Nat) (qv : GoValue) : Cont :=
  .stmtOpK (.appendSlice tU64) 1 [qv, .addr (.base ⟨a + 6⟩)] []
    (eqEnvC1 a) (eqKapp a)
/-- After `$res0 = $c1` is dispatched: the return statement. -/
def eqKret (a : Nat) : Cont :=
  .seq [.returnStmt] (eqEnvC1 a) (qeFrameK a)
/-- The `$res0 = $c1` rhs spine at the `$c1` read. -/
def eqResRhsK (a : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨a + 3⟩)) [] []] [] [] (.seqn #[])
    (eqEnvC1 a) (eqKret a)
/-- The frame write-back's target spine at the `.ref q` resolution
(`rv` is the loaded `$res0` value). -/
def qeWbK (a : Nat) (rv : GoValue) : Cont :=
  .tgtOpK (.chain []) [] [] [] [] .vals [] [rv] (.seqn #[]) (qeEnvV a)
    (qeAfterCallK a)
/-- The caller's `enqueued[i] = v` continuation. -/
def qeEndTail (a : Nat) : Cont :=
  .seq [] (qeEnvV a) (.seq [] qeEnv1 qeLoopK)
/-- The `enqueued[i] = v` rhs spine at the `v` read. -/
def qeStRhsK (a : Nat) (iv : Int) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨9⟩)) [.int iv .uint64] [.index]] [] []
    (.seqn #[]) (qeEnvV a) (qeEndTail a)

/-! ## Small executable normal-form facts -/

/-- uint64 cell normalization at an in-range value is the identity. -/
theorem normVal_u64 (σ : ExecState) {w : Int} (h0 : 0 ≤ w) (h1 : w < 2 ^ 64) :
    normalizeValueForTy σ tU64 (.int w .uint64) = .ok (.int w .uint64) := by
  rw [normalizeValueForTy, typeResolutionFuel]
  simp [normalizeValueForTyFuel, unorm_of_range h0 h1]

/-- Slice-typed cells never renormalize their handle (the normalizer's
catch-all arm). -/
theorem normVal_slice (σ : ExecState) (v : GoValue) :
    normalizeValueForTy σ sliceU v = .ok v := by
  with_unfolding_all rfl

/-! Micro one-step facts the chained segments below glue with (all
plain `rfl` arms of `stepFn`; none consults the environment's
`DecidableEq`, so they hold at symbolic addresses). -/

theorem stepFn_seq_nil {σ : ExecState} {env : LocalEnv} {k : Cont}
    {ch : Choices} :
    stepFn σ (.next (.seq [] env k)) ch = .ok (.next k, σ, ch) := rfl

/-! ## The entry segment and the loop-head segments -/

/-- Entry E0: harness body start (post-prelude) → the enqueue loop's
head, all twelve front cells built. 59 steps, fully concrete but for
the argument values. -/
theorem qe_E0_raw (σ : ExecState) (nv sv kv : Int) (ch : Choices) :
    stepFnIter 59 (qSt σ (qHeap0 nv sv kv) 6)
      (.exec queueHarnessRFunc.body [baseScope] qStop) ch
      = .ok (qeHeadCfg,
          qStE σ nv sv kv (qslV 7 0 0 0) zeros8 0 true [] 12, ch) := by
  with_unfolding_all rfl

/-- Loop head A0: head → the exit test's delivery (the `$forFirst`
first-iteration arm). 25 steps. -/
theorem qe_A0_raw (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (qStE σ nv sv kv qv lE iv true tail na) qeHeadCfg ch
      = .ok (.retV (.bool (decide (iv < nv))) qeCmpK,
          qStE σ nv sv kv qv lE iv false tail na, ch) := by
  with_unfolding_all rfl

/-! ## The enqueue-iteration raw segments (per-iteration, capacity- and
address-generic: the `v` cell lands at the SYMBOLIC `nextAddr` `a`, the
callee frame after it; every heap access at a symbolic address is a
separate conditioned step between these `rfl` pieces). -/

/-- Qe1: test true → the `v` initialization. 7 steps. -/
theorem qe_S1_raw (σ : ExecState) (ch : Choices) :
    stepFnIter 7 σ (.retV (.bool true) qeCmpK) ch
      = .ok (.exec (.initialization { id := "v", typ := tU64 }) qeEnv2
          (.seq [.assign (.var "v") (.add (.var "seed") (.var "i")),
            qeCallSeqn, qeStoreSeqn] qeEnv2 (.seq [] qeEnv1 qeLoopK)),
        σ, ch) := by
  with_unfolding_all rfl

/-- Qe2: `v` declared (at `a`) → the `v := seed + i` store point; the
add rides wrapped. 10 steps. -/
theorem qe_S2_raw (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na a : Nat) (ch : Choices) :
    stepFnIter 10 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.seq [.assign (.var "v") (.add (.var "seed") (.var "i")),
        qeCallSeqn, qeStoreSeqn] (qeEnvV a) (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a⟩)) [] []]
            [.int (IntKind.normalize .uint64 (sv + iv)) .uint64]
            (.seqn #[]) (qeEnvV a) (qeVTail a)),
          qStE σ nv sv kv qv lE iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Qe3: the `v` store drained → the call's `q` argument delivered, the
`v` argument's read pending. 8 steps. -/
theorem qe_S3_raw (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na a : Nat) (ch : Choices) :
    stepFnIter 8 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (qeEnvV a) (qeVTail a))) ch
      = .ok (.evalE (.var "v") (qeEnvV a) (qeCallArgsK a qv),
          qStE σ nv sv kv qv lE iv false tail na, ch) := by
  have h1 : stepFnIter 1 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (qeEnvV a) (qeVTail a))) ch
      = .ok (.exec (.seqn #[]) (qeEnvV a) (qeVTail a),
          qStE σ nv sv kv qv lE iv false tail na, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have h2 : stepFnIter 1 (qStE σ nv sv kv qv lE iv false tail na)
      (.exec (.seqn #[]) (qeEnvV a) (qeVTail a)) ch
      = .ok (.next (.seq [qeCallSeqn, qeStoreSeqn] (qeEnvV a)
          (.seq [] qeEnv1 qeLoopK)),
        qStE σ nv sv kv qv lE iv false tail na, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice
      (σ := qStE σ nv sv kv qv lE iv false tail na) (ss := #[])
      (env := qeEnvV a) (rest := [qeCallSeqn, qeStoreSeqn])
      (k := .seq [] qeEnv1 qeLoopK) (ch := ch))
    simpa [qeVTail] using this
  have h3 : stepFnIter 1 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.seq [qeCallSeqn, qeStoreSeqn] (qeEnvV a)
        (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.exec qeCallSeqn (qeEnvV a)
          (.seq [qeStoreSeqn] (qeEnvV a) (.seq [] qeEnv1 qeLoopK)),
        qStE σ nv sv kv qv lE iv false tail na, ch) :=
    stepFnIter_one stepFn_seq_pop
  have h4 : stepFnIter 1 (qStE σ nv sv kv qv lE iv false tail na)
      (.exec qeCallSeqn (qeEnvV a)
        (.seq [qeStoreSeqn] (qeEnvV a) (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.next (.seq [.call #[.var "q"] ⟨"enqueue"⟩
            #[.var "q", .var "v"], qeStoreSeqn] (qeEnvV a)
          (.seq [] qeEnv1 qeLoopK)),
        qStE σ nv sv kv qv lE iv false tail na, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice
      (σ := qStE σ nv sv kv qv lE iv false tail na)
      (ss := #[.call #[.var "q"] ⟨"enqueue"⟩ #[.var "q", .var "v"]])
      (env := qeEnvV a) (rest := [qeStoreSeqn])
      (k := .seq [] qeEnv1 qeLoopK) (ch := ch))
    simpa [qeCallSeqn] using this
  have h5 : stepFnIter 4 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.seq [.call #[.var "q"] ⟨"enqueue"⟩ #[.var "q", .var "v"],
        qeStoreSeqn] (qeEnvV a) (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.evalE (.var "v") (qeEnvV a) (qeCallArgsK a qv),
          qStE σ nv sv kv qv lE iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- Qe4: callee body entry → the `$c0` initialization. 4 steps. -/
theorem qe_S4_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 4 σ (.exec enqueueFunc.body (eqEnv a) (qeFrameK a)) ch
      = .ok (.exec (.initialization { id := "$c0", typ := sliceU })
          ([] :: eqEnv a)
          (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
              (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn]
            ([] :: eqEnv a) (qeFrameK a)),
        σ, ch) := by
  have h1 : stepFnIter 2 σ (.exec enqueueFunc.body (eqEnv a) (qeFrameK a)) ch
      = .ok (.exec (.seqn #[.initialization { id := "$c0", typ := sliceU },
            .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
              (some (.intLit 1 .int)), eqC0Assign]) ([] :: eqEnv a)
          (.seq [eqC1Seqn, eqRetSeqn] ([] :: eqEnv a) (qeFrameK a)),
        σ, ch) := by
    with_unfolding_all rfl
  have h2 : stepFnIter 1 σ
      (.exec (.seqn #[.initialization { id := "$c0", typ := sliceU },
          .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)), eqC0Assign]) ([] :: eqEnv a)
        (.seq [eqC1Seqn, eqRetSeqn] ([] :: eqEnv a) (qeFrameK a))) ch
      = .ok (.next (.seq [.initialization { id := "$c0", typ := sliceU },
            .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
              (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn]
          ([] :: eqEnv a) (qeFrameK a)), σ, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice (σ := σ)
      (ss := #[.initialization { id := "$c0", typ := sliceU },
        .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
          (some (.intLit 1 .int)), eqC0Assign])
      (env := [] :: eqEnv a) (rest := [eqC1Seqn, eqRetSeqn])
      (k := qeFrameK a) (ch := ch))
    simpa using this
  have h3 : stepFnIter 1 σ
      (.next (.seq [.initialization { id := "$c0", typ := sliceU },
          .makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn]
        ([] :: eqEnv a) (qeFrameK a))) ch
      = .ok (.exec (.initialization { id := "$c0", typ := sliceU })
          ([] :: eqEnv a)
          (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
              (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn]
            ([] :: eqEnv a) (qeFrameK a)), σ, ch) :=
    stepFnIter_one stepFn_seq_pop
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- Qe5: `$c0` declared (at `a+4`) → the `make([]uint64, 1, 1)` apply
point. 7 steps. -/
theorem qe_S5_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 7 σ
      (.next (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
          (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn]
        (eqEnvC0 a) (qeFrameK a))) ch
      = .ok (.retV (.int 1 .int)
          (.stmtOpK (.makeSlice tU64 true) 1
            [.int 1 .int, .addr (.base ⟨a + 4⟩)] [] (eqEnvC0 a) (eqKmk a)),
        σ, ch) := by
  with_unfolding_all rfl

/-- Qe6: the make drained → the `$c0[0]` target's `$c0` read. 2
steps. -/
theorem qe_S6_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 2 σ (.next (eqKmk a)) ch
      = .ok (.evalE (.var "$c0") (eqEnvC0 a) (eqTgtK a), σ, ch) := by
  with_unfolding_all rfl

/-- Qe7: the `$c0` handle delivered → the rhs `v` read (the index-0
chain is built in between). 3 steps. -/
theorem qe_S7_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (qslV (a + 5) 0 1 1) (eqTgtK a)) ch
      = .ok (.evalE (.var "v") (eqEnvC0 a) (eqRhsK a), σ, ch) := by
  with_unfolding_all rfl

/-- Qe8: the rhs value delivered → the `$c0[0]` store point. 1 step. -/
theorem qe_S8_raw (σ : ExecState) (a : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 σ (.retV w (eqRhsK a)) ch
      = .ok (.next (.storeK
            [.chain (qslV (a + 5) 0 1 1) [.int 0 .int] [.index]] [w]
            (.seqn #[]) (eqEnvC0 a) (eqTail2 a)), σ, ch) := by
  with_unfolding_all rfl

/-- Qe9: the `$c0[0]` store drained → the `$c1` initialization. 5
steps. -/
theorem qe_S9_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.next (.storeK [] [] (.seqn #[]) (eqEnvC0 a) (eqTail2 a))) ch
      = .ok (.exec (.initialization { id := "$c1", typ := sliceU })
          (eqEnvC0 a)
          (.seq [.appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0"),
            eqRetSeqn] (eqEnvC0 a) (qeFrameK a)),
        σ, ch) := by
  have h1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (eqEnvC0 a) (eqTail2 a))) ch
      = .ok (.exec (.seqn #[]) (eqEnvC0 a) (eqTail2 a), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have h2 : stepFnIter 1 σ (.exec (.seqn #[]) (eqEnvC0 a) (eqTail2 a)) ch
      = .ok (.next (.seq [eqC1Seqn, eqRetSeqn] (eqEnvC0 a) (qeFrameK a)),
          σ, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := #[])
      (env := eqEnvC0 a) (rest := [eqC1Seqn, eqRetSeqn])
      (k := qeFrameK a) (ch := ch))
    simpa [eqTail2] using this
  have h3 : stepFnIter 1 σ
      (.next (.seq [eqC1Seqn, eqRetSeqn] (eqEnvC0 a) (qeFrameK a))) ch
      = .ok (.exec eqC1Seqn (eqEnvC0 a)
          (.seq [eqRetSeqn] (eqEnvC0 a) (qeFrameK a)), σ, ch) :=
    stepFnIter_one stepFn_seq_pop
  have h4 : stepFnIter 1 σ
      (.exec eqC1Seqn (eqEnvC0 a)
        (.seq [eqRetSeqn] (eqEnvC0 a) (qeFrameK a))) ch
      = .ok (.next (.seq [.initialization { id := "$c1", typ := sliceU },
            .appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0"),
            eqRetSeqn] (eqEnvC0 a) (qeFrameK a)), σ, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice (σ := σ)
      (ss := #[.initialization { id := "$c1", typ := sliceU },
        .appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0")])
      (env := eqEnvC0 a) (rest := [eqRetSeqn])
      (k := qeFrameK a) (ch := ch))
    simpa [eqC1Seqn] using this
  have h5 : stepFnIter 1 σ
      (.next (.seq [.initialization { id := "$c1", typ := sliceU },
          .appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0"),
          eqRetSeqn] (eqEnvC0 a) (qeFrameK a))) ch
      = .ok (.exec (.initialization { id := "$c1", typ := sliceU })
          (eqEnvC0 a)
          (.seq [.appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0"),
            eqRetSeqn] (eqEnvC0 a) (qeFrameK a)), σ, ch) :=
    stepFnIter_one stepFn_seq_pop
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- Qe10: `$c1` declared (at `a+6`) → the append's `q` operand read. 4
steps. -/
theorem qe_S10_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.seq [.appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0"),
        eqRetSeqn] (eqEnvC1 a) (qeFrameK a))) ch
      = .ok (.evalE (.var "q") (eqEnvC1 a) (eqAppK1 a), σ, ch) := by
  with_unfolding_all rfl

/-- Qe11: the `q` operand delivered → the `$c0` operand read. 1
step. -/
theorem qe_S11_raw (σ : ExecState) (a : Nat) (qv : GoValue)
    (ch : Choices) :
    stepFnIter 1 σ (.retV qv (eqAppK1 a)) ch
      = .ok (.evalE (.var "$c0") (eqEnvC1 a) (eqAppK2 a qv), σ, ch) := by
  with_unfolding_all rfl

/-- Qe12: the append drained → the `$res0 = $c1` rhs read. 6 steps. -/
theorem qe_S12_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 6 σ (.next (eqKapp a)) ch
      = .ok (.evalE (.var "$c1") (eqEnvC1 a) (eqResRhsK a), σ, ch) := by
  have h1 : stepFnIter 1 σ (.next (eqKapp a)) ch
      = .ok (.exec eqRetSeqn (eqEnvC1 a)
          (.seq [] (eqEnvC1 a) (qeFrameK a)), σ, ch) :=
    stepFnIter_one stepFn_seq_pop
  have h2 : stepFnIter 1 σ
      (.exec eqRetSeqn (eqEnvC1 a) (.seq [] (eqEnvC1 a) (qeFrameK a))) ch
      = .ok (.next (.seq [.assign (.var "$res0") (.var "$c1"),
            .returnStmt] (eqEnvC1 a) (qeFrameK a)), σ, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice (σ := σ)
      (ss := #[.assign (.var "$res0") (.var "$c1"), .returnStmt])
      (env := eqEnvC1 a) (rest := []) (k := qeFrameK a) (ch := ch))
    simpa [eqRetSeqn] using this
  have h3 : stepFnIter 4 σ
      (.next (.seq [.assign (.var "$res0") (.var "$c1"), .returnStmt]
        (eqEnvC1 a) (qeFrameK a))) ch
      = .ok (.evalE (.var "$c1") (eqEnvC1 a) (eqResRhsK a), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- Qe13: the `$c1` handle delivered → the `$res0` store point. 1
step. -/
theorem qe_S13_raw (σ : ExecState) (a : Nat) (w : GoValue) (ch : Choices) :
    stepFnIter 1 σ (.retV w (eqResRhsK a)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 3⟩)) [] []] [w]
            (.seqn #[]) (eqEnvC1 a) (eqKret a)), σ, ch) := by
  with_unfolding_all rfl

/-- Qe14: the `$res0` store drained → the callee's `return`, unwound to
the frame. 5 steps. -/
theorem qe_S14_raw (σ : ExecState) (a : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.next (.storeK [] [] (.seqn #[]) (eqEnvC1 a) (eqKret a))) ch
      = .ok (.returning (qeFrameK a), σ, ch) := by
  have h1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (eqEnvC1 a) (eqKret a))) ch
      = .ok (.exec (.seqn #[]) (eqEnvC1 a) (eqKret a), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have h2 : stepFnIter 1 σ (.exec (.seqn #[]) (eqEnvC1 a) (eqKret a)) ch
      = .ok (.next (.seq [.returnStmt] (eqEnvC1 a) (qeFrameK a)),
          σ, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := #[])
      (env := eqEnvC1 a) (rest := [.returnStmt]) (k := qeFrameK a)
      (ch := ch))
    simpa [eqKret] using this
  have h3 : stepFnIter 3 σ
      (.next (.seq [.returnStmt] (eqEnvC1 a) (qeFrameK a))) ch
      = .ok (.returning (qeFrameK a), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- Qe15: the write-back target resolved → the `enqueued[i] = v` rhs
read (`q := <returned handle>` stores THROUGH the concrete front cell 8
inside this segment; `rv` is the loaded result handle). 13 steps. -/
theorem qe_S15_raw (σ : ExecState) (nv sv kv : Int) (qv rv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na a : Nat) (ch : Choices) :
    stepFnIter 13 (qStE σ nv sv kv qv lE iv false tail na)
      (.evalE (.ref "q") (qeEnvV a) (qeWbK a rv)) ch
      = .ok (.evalE (.var "v") (qeEnvV a) (qeStRhsK a iv),
          qStE σ nv sv kv rv lE iv false tail na, ch) := by
  have h1 : stepFnIter 3 (qStE σ nv sv kv qv lE iv false tail na)
      (.evalE (.ref "q") (qeEnvV a) (qeWbK a rv)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qeEnvV a)
          (qeAfterCallK a)),
        qStE σ nv sv kv rv lE iv false tail na, ch) := by
    with_unfolding_all rfl
  have h2 : stepFnIter 1 (qStE σ nv sv kv rv lE iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (qeEnvV a) (qeAfterCallK a))) ch
      = .ok (.exec (.seqn #[]) (qeEnvV a) (qeAfterCallK a),
          qStE σ nv sv kv rv lE iv false tail na, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have h3 : stepFnIter 1 (qStE σ nv sv kv rv lE iv false tail na)
      (.exec (.seqn #[]) (qeEnvV a) (qeAfterCallK a)) ch
      = .ok (.next (.seq [qeStoreSeqn] (qeEnvV a)
          (.seq [] qeEnv1 qeLoopK)),
        qStE σ nv sv kv rv lE iv false tail na, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice
      (σ := qStE σ nv sv kv rv lE iv false tail na) (ss := #[])
      (env := qeEnvV a) (rest := [qeStoreSeqn])
      (k := .seq [] qeEnv1 qeLoopK) (ch := ch))
    simpa [qeAfterCallK] using this
  have h4 : stepFnIter 1 (qStE σ nv sv kv rv lE iv false tail na)
      (.next (.seq [qeStoreSeqn] (qeEnvV a) (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.exec qeStoreSeqn (qeEnvV a)
          (.seq [] (qeEnvV a) (.seq [] qeEnv1 qeLoopK)),
        qStE σ nv sv kv rv lE iv false tail na, ch) :=
    stepFnIter_one stepFn_seq_pop
  have h5 : stepFnIter 1 (qStE σ nv sv kv rv lE iv false tail na)
      (.exec qeStoreSeqn (qeEnvV a)
        (.seq [] (qeEnvV a) (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.next (.seq [.assign
            (.addr (.indexAddr (.ref "enqueued") (.var "i"))) (.var "v")]
          (qeEnvV a) (.seq [] qeEnv1 qeLoopK)),
        qStE σ nv sv kv rv lE iv false tail na, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice
      (σ := qStE σ nv sv kv rv lE iv false tail na)
      (ss := #[.assign (.addr (.indexAddr (.ref "enqueued") (.var "i")))
        (.var "v")])
      (env := qeEnvV a) (rest := []) (k := .seq [] qeEnv1 qeLoopK)
      (ch := ch))
    simpa [qeStoreSeqn] using this
  have h6 : stepFnIter 6 (qStE σ nv sv kv rv lE iv false tail na)
      (.next (.seq [.assign
          (.addr (.indexAddr (.ref "enqueued") (.var "i"))) (.var "v")]
        (qeEnvV a) (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.evalE (.var "v") (qeEnvV a) (qeStRhsK a iv),
          qStE σ nv sv kv rv lE iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6

/-- Qe16: the rhs value delivered → the `enqueued[i]` store point. 1
step. -/
theorem qe_S16_raw (σ : ExecState) (a : Nat) (iv : Int) (w : GoValue)
    (ch : Choices) :
    stepFnIter 1 σ (.retV w (qeStRhsK a iv)) ch
      = .ok (.next (.storeK
            [.chain (.addr (.base ⟨9⟩)) [.int iv .uint64] [.index]] [w]
            (.seqn #[]) (qeEnvV a) (qeEndTail a)), σ, ch) := by
  with_unfolding_all rfl

/-- Qe17: the `enqueued[i]` store drained → the incremented dispatch and
the next exit test's delivery. 34 steps. -/
theorem qe_S17_raw (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na a : Nat) (ch : Choices) :
    stepFnIter 34 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (qeEnvV a) (qeEndTail a))) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) qeCmpK,
          qStE σ nv sv kv qv lE
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false tail na, ch) := by
  have h1 : stepFnIter 1 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (qeEnvV a) (qeEndTail a))) ch
      = .ok (.exec (.seqn #[]) (qeEnvV a) (qeEndTail a),
          qStE σ nv sv kv qv lE iv false tail na, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have h2 : stepFnIter 1 (qStE σ nv sv kv qv lE iv false tail na)
      (.exec (.seqn #[]) (qeEnvV a) (qeEndTail a)) ch
      = .ok (.next (.seq [] (qeEnvV a) (.seq [] qeEnv1 qeLoopK)),
          qStE σ nv sv kv qv lE iv false tail na, ch) := by
    have := stepFnIter_one (stepFn_seqn_splice
      (σ := qStE σ nv sv kv qv lE iv false tail na) (ss := #[])
      (env := qeEnvV a) (rest := []) (k := .seq [] qeEnv1 qeLoopK)
      (ch := ch))
    simpa [qeEndTail] using this
  have h3 : stepFnIter 2 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.seq [] (qeEnvV a) (.seq [] qeEnv1 qeLoopK))) ch
      = .ok (.next qeLoopK, qStE σ nv sv kv qv lE iv false tail na, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_seq_nil)
      (stepFnIter_one stepFn_seq_nil)
  have h4 : stepFnIter 30 (qStE σ nv sv kv qv lE iv false tail na)
      (.next qeLoopK) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) qeCmpK,
          qStE σ nv sv kv qv lE
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4

/-! ## Executable facts for `append` and slice re-slicing

GAP-WITNESS (new kit-gap class, reported by this module): the gallery
has never proved through a GROWING slice or a MOVING offset before, so
none of the facts below have kit forms. Shapes wanted, with `stack` as
the co-consumer for the append family and any future `q[a:b]`-using
example for the re-slice fact. -/

/-- Value-exact push-loop evaluation (the value-exact strengthening of
`forIn_yield_push_size`, which only reports the size). -/
private theorem forIn_yield_push_eq {α : Type}
    {body : α → Array GoValue → Except GoError (ForInStep (Array GoValue))}
    {g : α → GoValue} :
    ∀ (l : List α), (∀ x ∈ l, ∀ r, body x r = .ok (.yield (r.push (g x)))) →
    ∀ (acc : Array GoValue),
      forIn l acc body = .ok (acc ++ (l.map g).toArray)
  | [], _, acc => by simp [List.forIn_nil, pure, Except.pure]
  | x :: xs, hshape, acc => by
      rw [List.forIn_cons, hshape x (by simp) acc]
      simp only [Bind.bind, Except.bind]
      rw [forIn_yield_push_eq xs
        (fun y hy r => hshape y (by simp [hy]) r) (acc.push (g x))]
      simp

/-- The visible elements of an offset-0 `[]uint64` slice over a mapped
backing: the length-prefix of the backing list. -/
private theorem sliceVisibleValues_u64 {σ : ExecState} {b : Addr}
    {dty : Option Ty} {len cap : Nat} {l : List Int}
    (hlook : Heap.lookup σ.heap (.base b)
      = some ⟨dty, .array ⟨l.map (fun v => .int v .uint64)⟩⟩)
    (hcap : len ≤ cap) (hsz : len ≤ l.length) :
    sliceVisibleValues σ ⟨some (.base b), 0, len, cap⟩
      = .ok ⟨(l.take len).map (fun v => .int v .uint64)⟩ := by
  unfold sliceVisibleValues
  have hval : validateSlice
      (⟨some (.base b), 0, len, cap⟩ : SliceValue) = .ok () := by
    simp [validateSlice, Nat.not_lt.mpr hcap, Bind.bind, Except.bind]
  rw [hval]
  simp only [Bind.bind, Except.bind, Std.Legacy.Range.forIn_eq_forIn_range',
    pure, Except.pure]
  rw [show ([:len] : Std.Legacy.Range).size = len from by
    simp [Std.Legacy.Range.size]]
  rw [GoLean.Iris.forIn_range'_inv (N := len) (n := len) (j := 0)
    (b := (#[] : Array GoValue))
    (Q := fun i acc => acc = ⟨(l.take i).map (fun v => .int v .uint64)⟩)
    (out := fun i acc => acc.push (.int (l.getD i 0) .uint64))
    (res := ⟨(l.take len).map (fun v => .int v .uint64)⟩)
    ?hfill (by omega) (by simp) ?hdet]
  case hfill =>
      intro i acc hi hacc
      have hil : i < l.length := by omega
      constructor
      · rw [GoLean.Iris.sliceIndexLoc_prefix hi hcap]
        dsimp only
        have hload : loadLoc σ (.index (.base b) (Int.ofNat i))
            = .ok (.int (l.getD i 0) .uint64) := by
          have hidx : arrayIndexNat
              (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)
              (Int.ofNat i) = .ok i := by
            simp only [arrayIndexNat, Bind.bind, Except.bind,
              Int.ofNat_eq_natCast]
            rw [if_neg (by omega), Int.toNat_natCast,
              if_pos (by simpa using hil)]
            rfl
          simp only [loadLoc, hlook, arrayGet, hidx, Bind.bind, Except.bind,
            getElem?_mapU l i hil, pure, Except.pure]
        rw [hload]
      · rw [hacc]
        have : l.take (i + 1)
            = l.take i ++ [l.getD i 0] := by
          rw [List.take_add_one]
          congr 1
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
          simp [Option.toList]
        rw [this]
        apply Array.ext'
        simp
  case hdet =>
      intro b' hb'
      simpa using hb'

/-- The append backing build at `[]uint64`: normalize is the identity
on in-range values, the padding is zeros. -/
private theorem buildAppendBacking_u64 {σ : ExecState} {l₁ l₂ : List Int}
    {newCap : Nat}
    (h₁ : ∀ v ∈ l₁, 0 ≤ v ∧ v < 2 ^ 64) (h₂ : ∀ v ∈ l₂, 0 ≤ v ∧ v < 2 ^ 64)
    (hcap : l₁.length + l₂.length ≤ newCap) :
    buildAppendBackingValue σ tU64 ⟨l₁.map (fun v => .int v .uint64)⟩
        ⟨l₂.map (fun v => .int v .uint64)⟩ newCap
      = .ok (.array ⟨(l₁ ++ l₂
          ++ List.replicate (newCap - (l₁.length + l₂.length)) 0).map
            (fun v => .int v .uint64)⟩) := by
  unfold buildAppendBackingValue
  have happ : (⟨l₁.map (fun v => .int v .uint64)⟩ : Array GoValue)
      ++ (⟨l₂.map (fun v => .int v .uint64)⟩ : Array GoValue)
      = ⟨(l₁ ++ l₂).map (fun v => .int v .uint64)⟩ := by
    apply Array.ext'
    simp
  have h₁₂ : ∀ v ∈ l₁ ++ l₂, 0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact h₁ v hv
    · exact h₂ v hv
  simp only [Bind.bind, Except.bind, happ, ← Array.forIn_toList]
  rw [forIn_yield_push_eq (g := fun v : GoValue => v)
    ((l₁ ++ l₂).map (fun v => GoValue.int v IntKind.uint64)) ?hsh1 #[]]
  case hsh1 =>
    intro x hx r
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    have := h₁₂ v hv
    simp only [normVal_u64 σ this.1 this.2, pure, Except.pure]
  simp only [List.map_id']
  have hsz : ((#[] : Array GoValue)
      ++ ((l₁ ++ l₂).map (fun v => GoValue.int v IntKind.uint64)).toArray).size
      = l₁.length + l₂.length := by simp
  rw [if_neg (by rw [hsz]; omega)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show ([:newCap - ((#[] : Array GoValue)
      ++ ((l₁ ++ l₂).map (fun v => GoValue.int v IntKind.uint64)).toArray).size] :
      Std.Legacy.Range).size
    = newCap - (l₁.length + l₂.length) from by
      simp [Std.Legacy.Range.size]]
  rw [forIn_yield_push_eq
    (g := fun _ : Nat => (GoValue.int 0 IntKind.uint64 : GoValue))
    (List.range' 0 (newCap - (l₁.length + l₂.length)) 1) ?hsh2
    ((#[] : Array GoValue)
      ++ ((l₁ ++ l₂).map (fun v => GoValue.int v IntKind.uint64)).toArray)]
  case hsh2 =>
    intro x _ r
    rw [show defaultValue σ tU64 = .ok (.int 0 .uint64) from by
      with_unfolding_all rfl]
    rfl
  have hmapz : (List.range' 0 (newCap - (l₁.length + l₂.length)) 1).map
        (fun _ => (.int 0 .uint64 : GoValue))
      = (List.replicate (newCap - (l₁.length + l₂.length)) (0 : Int)).map
          (fun v => .int v .uint64) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj2
      simp
  rw [hmapz]
  simp only [pure, Except.pure, Except.ok.injEq, GoValue.array.injEq]
  apply Array.ext'
  simp

/-- `arraySet` on a mapped `[]uint64` backing at an in-range index. -/
private theorem qArraySet_u64 {l : List Int} {i : Nat} {w : Int}
    (hi : i < l.length) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    arraySet (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)
        (Int.ofNat i) (.int w .uint64)
      = .ok ⟨(l.set i w).map (fun v => .int v .uint64)⟩ := by
  have hglist : l[i]? = some (l[i]'hi) := List.getElem?_eq_getElem hi
  have hidx : arrayIndexNat (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)
      (Int.ofNat i) = .ok i := by
    simp only [arrayIndexNat, Bind.bind, Except.bind, Int.ofNat_eq_natCast]
    rw [if_neg (by omega), Int.toNat_natCast, if_pos (by simpa using hi)]
    rfl
  simp only [arraySet, Bind.bind, Except.bind, hidx]
  rw [getElem?_mapU l i hi]
  simp only [coerceStoredValue, unorm_of_range hw.1 hw.2, Array.set!, pure,
    Except.pure, Except.ok.injEq]
  apply Array.ext'
  simp [List.map_set]

/-- One enqueue's store advances the backing prefix (the affine-family
mirror of the kit's `prefixPad_familyMod_set`; GAP-P2b). -/
theorem qBack_set {C i seed : Nat} (hi : i < C) :
    (qBack C i seed).set i (((seed + i) % 2 ^ 64 : Nat) : Int)
      = qBack C (i + 1) seed := by
  have hlen : (qFam i seed).length = i := qFam_length i seed
  have hnm : C - i = (C - (i + 1)) + 1 := by omega
  rw [qBack, List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero]
  rw [qBack, qFam_succ]
  simp

/-- **The IN-PLACE `append` apply fact** (`newLen ≤ cap`): the appended
element lands in the backing at index `len`, the target cell gets the
lengthened handle, NO choice is consumed. -/
theorem qappend_inplace {σ : ExecState} {H : Heap} {na : Nat}
    {B bc tc : Nat} {i C : Nat}
    {lq : List Int} {w : Int} {dty2 : Option Ty} {old : GoValue}
    {ch : Choices}
    (hB : Heap.lookup H (.base ⟨B⟩)
      = some ⟨some (.array C tU64),
          .array ⟨lq.map (fun v => .int v .uint64)⟩⟩)
    (hbc : Heap.lookup H (.base ⟨bc⟩)
      = some ⟨dty2, .array ⟨[w].map (fun v => .int v .uint64)⟩⟩)
    (htc : Heap.lookup H (.base ⟨tc⟩) = some ⟨some sliceU, old⟩)
    (htcB : tc ≠ B)
    (hlen : lq.length = C) (hiC : i < C)
    (hrq : ∀ v ∈ lq, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    applyStmtOp (qSt σ H na) ch (.appendSlice tU64) 1
      [.addr (.base ⟨tc⟩), qslV B 0 i C, qslV bc 0 1 1]
      = .ok (qSt σ
          (Heap.set (Heap.set H (.base ⟨B⟩)
            ⟨some (.array C tU64),
             .array ⟨(lq.set i w).map (fun v => .int v .uint64)⟩⟩)
            (.base ⟨tc⟩) ⟨some sliceU, qslV B 0 (i + 1) C⟩)
          na, ch) := by
  have hvalq : validateSlice
      (⟨some (.base ⟨B⟩), 0, i, C⟩ : SliceValue) = .ok () := by
    simp [validateSlice, Nat.not_lt.mpr (by omega : i ≤ C), Bind.bind,
      Except.bind]
  have hvalc : validateSlice
      (⟨some (.base ⟨bc⟩), 0, 1, 1⟩ : SliceValue) = .ok () := by
    simp [validateSlice, Bind.bind, Except.bind]
  have hvis : sliceVisibleValues (qSt σ H na) ⟨some (.base ⟨bc⟩), 0, 1, 1⟩
      = .ok ⟨[GoValue.int w IntKind.uint64]⟩ := by
    have hbc' : Heap.lookup (qSt σ H na).heap (.base ⟨bc⟩)
        = some ⟨dty2, .array ⟨[w].map (fun v => .int v .uint64)⟩⟩ := hbc
    have := sliceVisibleValues_u64 hbc'
      (len := 1) (cap := 1) (l := [w]) (by omega) (by simp)
    simpa using this
  have hsetB : ∀ v ∈ lq.set i w, 0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases mem_set_of_mem hv with rfl | hv
    · exact hw
    · exact hrq v hv
  have hstore1 : storeLoc (qSt σ H na)
      (.index (.base ⟨B⟩) (Int.ofNat (0 + i + 0)))
      (.int w .uint64)
      = .ok (qSt σ (Heap.set H (.base ⟨B⟩)
          ⟨some (.array C tU64),
           .array ⟨(lq.set i w).map (fun v => .int v .uint64)⟩⟩)
        na) := by
    have hset : arraySet (⟨lq.map (fun v => .int v .uint64)⟩ : Array GoValue)
        (Int.ofNat (0 + i + 0)) (.int w .uint64)
        = .ok ⟨(lq.set i w).map (fun v => .int v .uint64)⟩ := by
      rw [show (0 + i + 0) = i from by omega]
      exact qArraySet_u64 (by omega) hw
    have hnorm := normalizeValueForTy_arr_u64 (σ := qSt σ H na) (N := C)
      (lp := lq.set i w) (by rw [List.length_set]; exact hlen) hsetB
    simp only [storeLoc, loadLoc, qSt, hB, hset, Bind.bind, Except.bind,
      hnorm, pure, Except.pure]
  have hstore2 : storeLoc
      (qSt σ (Heap.set H (.base ⟨B⟩)
          ⟨some (.array C tU64),
           .array ⟨(lq.set i w).map (fun v => .int v .uint64)⟩⟩)
        na)
      (.base ⟨tc⟩) (.slice ⟨some (.base ⟨B⟩), 0, i + 1, C⟩)
      = .ok (qSt σ
          (Heap.set (Heap.set H (.base ⟨B⟩)
            ⟨some (.array C tU64),
             .array ⟨(lq.set i w).map (fun v => .int v .uint64)⟩⟩)
            (.base ⟨tc⟩) ⟨some sliceU, qslV B 0 (i + 1) C⟩)
          na) := by
    have hlk : Heap.lookup (Heap.set H (.base ⟨B⟩)
        ⟨some (.array C tU64),
         .array ⟨(lq.set i w).map (fun v => .int v .uint64)⟩⟩)
        (.base ⟨tc⟩) = some ⟨some sliceU, old⟩ := by
      rw [Machine.Heap.lookup_set_ne (by simp [htcB.symm])]
      exact htc
    simp only [storeLoc, hlk, normVal_slice, Bind.bind, Except.bind, pure,
      Except.pure]
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind, Except.bind,
    pure, Except.pure, hvalq, hvalc, hvis]
  rw [show (⟨[GoValue.int w IntKind.uint64]⟩ : Array GoValue).size = 1
    from rfl]
  rw [if_pos (by omega : i + 1 ≤ C)]
  rw [← Array.forIn_toList]
  simp only [show (⟨[GoValue.int w IntKind.uint64]⟩ :
      Array GoValue).toList = [GoValue.int w IntKind.uint64] from rfl]
  simp only [List.forIn_cons, List.forIn_nil, Bind.bind, Except.bind,
    hstore1, pure, Except.pure]
  simp only [hstore2, pure, Except.pure]

/-- The realized SPILL capacity at choice head `e`. -/
def qSpillCap (C e : Nat) : Nat :=
  (C + 1) + ((appendGrowthCap C (C + 1) - (C + 1) + e)
    % appendSpillWidth C (C + 1))

theorem qSpillCap_ge (C e : Nat) : C + 1 ≤ qSpillCap C e := by
  rw [qSpillCap]; omega

/-- **The SPILL `append` apply fact** (`len = cap`, the full-backing
case — the only way this harness spills): ONE choice is consumed, a
fresh backing at the envelope capacity `qSpillCap C extra` is allocated
at `nextAddr`, the target cell gets a handle onto it. -/
theorem qappend_spill {σ : ExecState} {H : Heap} {na : Nat}
    {B bc tc : Nat} {C : Nat}
    {lq : List Int} {w : Int} {dty2 : Option Ty} {old : GoValue}
    {ch : Choices}
    (hB : Heap.lookup H (.base ⟨B⟩)
      = some ⟨some (.array C tU64),
          .array ⟨lq.map (fun v => .int v .uint64)⟩⟩)
    (hbc : Heap.lookup H (.base ⟨bc⟩)
      = some ⟨dty2, .array ⟨[w].map (fun v => .int v .uint64)⟩⟩)
    (htc : Heap.lookup H (.base ⟨tc⟩) = some ⟨some sliceU, old⟩)
    (hdead : DeadFrom H na)
    (hlen : lq.length = C)
    (hrq : ∀ v ∈ lq, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    applyStmtOp (qSt σ H na) ch (.appendSlice tU64) 1
      [.addr (.base ⟨tc⟩), qslV B 0 C C, qslV bc 0 1 1]
      = .ok (qSt σ
          (Heap.set H (.base ⟨tc⟩)
            ⟨some sliceU,
             qslV na 0 (C + 1)
               (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)⟩
          ++ [(.base ⟨na⟩,
               ⟨some (.array (qSpillCap C
                   (ch.consume (appendSpillWidth C (C + 1))).1) tU64),
                .array ⟨(lq ++ [w] ++ List.replicate
                    (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1
                      - (C + 1)) 0).map (fun v => .int v .uint64)⟩⟩)])
          (na + 1),
        (ch.consume (appendSpillWidth C (C + 1))).2) := by
  have hvalq : validateSlice
      (⟨some (.base ⟨B⟩), 0, C, C⟩ : SliceValue) = .ok () := by
    simp [validateSlice, Bind.bind, Except.bind]
  have hvalc : validateSlice
      (⟨some (.base ⟨bc⟩), 0, 1, 1⟩ : SliceValue) = .ok () := by
    simp [validateSlice, Bind.bind, Except.bind]
  have hbc' : Heap.lookup (qSt σ H na).heap (.base ⟨bc⟩)
      = some ⟨dty2, .array ⟨[w].map (fun v => .int v .uint64)⟩⟩ := hbc
  have hB' : Heap.lookup (qSt σ H na).heap (.base ⟨B⟩)
      = some ⟨some (.array C tU64),
          .array ⟨lq.map (fun v => .int v .uint64)⟩⟩ := hB
  have hvis : sliceVisibleValues (qSt σ H na) ⟨some (.base ⟨bc⟩), 0, 1, 1⟩
      = .ok ⟨[GoValue.int w IntKind.uint64]⟩ := by
    have := sliceVisibleValues_u64 hbc'
      (len := 1) (cap := 1) (l := [w]) (by omega) (by simp)
    simpa using this
  have hvisq : sliceVisibleValues (qSt σ H na) ⟨some (.base ⟨B⟩), 0, C, C⟩
      = .ok ⟨lq.map (fun v => .int v .uint64)⟩ := by
    have := sliceVisibleValues_u64 hB' (len := C) (cap := C) (l := lq)
      (by omega) (by omega)
    rwa [List.take_of_length_le (by omega)] at this
  have hbuild := buildAppendBacking_u64 (σ := qSt σ H na) (l₁ := lq) (l₂ := [w])
    (newCap := qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)
    hrq (by intro v hv; simp at hv; omega)
    (by have := qSpillCap_ge C (ch.consume (appendSpillWidth C (C + 1))).1
        simp [hlen]; omega)
  have hstore : storeLoc
      (qSt σ (H ++ [(.base ⟨na⟩,
          ⟨some (.array (qSpillCap C
              (ch.consume (appendSpillWidth C (C + 1))).1) tU64),
           .array ⟨(lq ++ [w] ++ List.replicate
               (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1
                 - (C + 1)) 0).map (fun v => .int v .uint64)⟩⟩)])
        (na + 1))
      (.base ⟨tc⟩)
      (.slice ⟨some (.base ⟨na⟩), 0, C + 1,
        qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1⟩)
      = .ok (qSt σ
          (Heap.set H (.base ⟨tc⟩)
            ⟨some sliceU,
             qslV na 0 (C + 1)
               (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)⟩
          ++ [(.base ⟨na⟩,
               ⟨some (.array (qSpillCap C
                   (ch.consume (appendSpillWidth C (C + 1))).1) tU64),
                .array ⟨(lq ++ [w] ++ List.replicate
                    (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1
                      - (C + 1)) 0).map (fun v => .int v .uint64)⟩⟩)])
          (na + 1)) := by
    have hlk : Heap.lookup (H ++ [(.base ⟨na⟩,
        (⟨some (.array (qSpillCap C
            (ch.consume (appendSpillWidth C (C + 1))).1) tU64),
         .array ⟨(lq ++ [w] ++ List.replicate
             (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1
               - (C + 1)) 0).map (fun v => .int v .uint64)⟩⟩ : HeapCell))])
        (.base ⟨tc⟩) = some ⟨some sliceU, old⟩ :=
      lookup_append_left htc
    have hset := set_append_left (h₂ := [(.base ⟨na⟩,
        (⟨some (.array (qSpillCap C
            (ch.consume (appendSpillWidth C (C + 1))).1) tU64),
         .array ⟨(lq ++ [w] ++ List.replicate
             (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1
               - (C + 1)) 0).map (fun v => .int v .uint64)⟩⟩ : HeapCell))])
      (c := (⟨some sliceU,
        qslV na 0 (C + 1)
          (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)⟩ :
          HeapCell)) htc
    simp only [storeLoc, hlk, normVal_slice, Bind.bind, Except.bind, pure,
      Except.pure, hset]
  simp only [applyStmtOp, valueAsSlice, valueAsLoc, Bind.bind, Except.bind,
    pure, Except.pure, hvalq, hvalc, hvis, hvisq]
  rw [show (⟨[GoValue.int w IntKind.uint64]⟩ : Array GoValue).size = 1
    from rfl]
  rw [if_neg (by omega : ¬ (C + 1 ≤ C))]
  rw [show C + 1 + (appendGrowthCap C (C + 1) - (C + 1)
        + (ch.consume (appendSpillWidth C (C + 1))).fst)
        % appendSpillWidth C (C + 1)
      = qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1 from rfl]
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    hlen] at hbuild
  rw [show C + (0 + 1) = C + 1 from by omega] at hbuild
  simp only [hbuild]
  simp only [ExecState.alloc, ExecState.freshLoc]
  rw [set_fresh (hdead _ (Nat.le_refl _))]
  simp only [hstore, Bind.bind, Except.bind, pure, Except.pure]

/-- **The re-slice fact** `q[1:len(q)]` at a slice base (GAP-WITNESS:
the kit's `applyStrictOp_sliceExpr_array` covers only pointer-to-array
bases; the MOVING-OFFSET slice-base form is new with this example): the
SAME backing, offset advanced, length and capacity down one. -/
theorem applyStrictOp_sliceExpr_slice {σ : ExecState} {b : Loc}
    {off len cap : Nat} {ik ik' : IntKind}
    (h1 : 1 ≤ len) (hcap : len ≤ cap) :
    applyStrictOp σ (.sliceExpr false)
      [.slice ⟨some b, off, len, cap⟩, .int 1 ik, .int (len : Nat) ik']
      = .ok (.slice ⟨some b, off + 1, len - 1, cap - 1⟩, σ) := by
  have hval : validateSlice (⟨some b, off, len, cap⟩ : SliceValue)
      = .ok () := by
    simp [validateSlice, Nat.not_lt.mpr hcap, Bind.bind, Except.bind]
  have hbounds : checkSliceBounds "capacity" cap 1 (len : Int)
      = .ok (1, len) := by
    simp only [checkSliceBounds, Bind.bind, Except.bind, pure, Except.pure]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    simp
  simp only [applyStrictOp, valueAsInt, applySlice, sliceFromSlice, hval,
    hbounds, Bind.bind, Except.bind, pure, Except.pure]

-- The latent `applyStrictOp_convert_u64` copy that sat here (declared,
-- never called — the GAP-CONVERT grading, g1.md §Unit G1.8b) was
-- DELETED in WP arc s1 lift 1; the kit form is
-- `SliceMem.applyStrictOp_convert_u64`.

/-- The frame-return step, conditioned on the result loads: `.returning`
at a target-bearing frame loads the pinned results and starts the
post-call target walk.

GAP-WITNESS (GAP-FRAME, see docs/gallery-campaign-log/g1.md
§ KIT GAPS (unit G1.8b)): stack re-derives the same fact; the kit has
no frame-exit step lemma. -/
theorem stepFn_return_frame {σ : ExecState} {sh : TargetShape} {e : Expr}
    {ops : List Expr} {rest : List (TargetShape × List Expr)}
    {tenv : LocalEnv} {results : List Loc} {k' : Cont} {w : Bool}
    {vs : List GoValue} {ch : Choices}
    (h : loadMany σ results = .ok vs) :
    stepFn σ (.returning (.frame ((sh, e :: ops) :: rest) tenv results []
      k' w)) ch
      = .ok (.evalE e tenv
          (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'),
        σ, ch) := by
  simp only [stepFn, h, Bind.bind, Except.bind, pure, Except.pure]

/-- One-cell `loadMany`. -/
theorem loadMany_one {σ : ExecState} {a : Addr} {c : HeapCell}
    (h : Heap.lookup σ.heap (.base a) = some c) :
    loadMany σ [.base a] = .ok [c.value] := by
  simp only [loadMany, loadLoc, h, Bind.bind, Except.bind, pure, Except.pure]

/-- Two-cell `loadMany`. -/
theorem loadMany_two {σ : ExecState} {a b : Addr} {c d : HeapCell}
    (ha : Heap.lookup σ.heap (.base a) = some c)
    (hb : Heap.lookup σ.heap (.base b) = some d) :
    loadMany σ [.base a, .base b] = .ok [c.value, d.value] := by
  simp only [loadMany, loadLoc, ha, hb, Bind.bind, Except.bind, pure,
    Except.pure]

/-- `defaultValue` at the two scalar shapes the callees declare
(state-generic: the fuel constant is concrete and the types consult
nothing). -/
theorem defVal_sliceU (σ : ExecState) :
    defaultValue σ sliceU = .ok (.slice ⟨none, 0, 0, 0⟩) := by
  with_unfolding_all rfl

theorem defVal_u64 (σ : ExecState) :
    defaultValue σ tU64 = .ok (.int 0 .uint64) := by
  with_unfolding_all rfl

/-- The callee's `make([]uint64, 1, 1)` apply: one fresh backing cell
`[0]` at `na`, the handle stored into the (symbolic-address) `$c0`
cell. -/
theorem qmake11_apply {σ : ExecState} {H : Heap} {na : Nat} {a4 : Nat}
    {old : GoValue} {ch : Choices}
    (h4 : Heap.lookup H (.base ⟨a4⟩) = some ⟨some sliceU, old⟩)
    (hdead : DeadFrom H na) :
    applyStmtOp (qSt σ H na) ch (.makeSlice tU64 true) 1
      [.addr (.base ⟨a4⟩), .int 1 .int, .int 1 .int]
      = .ok (qSt σ
          (Heap.set H (.base ⟨a4⟩)
            ⟨some sliceU, qslV na 0 1 1⟩
          ++ [(.base ⟨na⟩, arrCellU 1 [0])])
          (na + 1), ch) := by
  have hb : buildDefaultArrayValue (qSt σ H na) 1 (.int .uint64)
      = .ok (.array #[.int 0 .uint64]) := by
    with_unfolding_all rfl
  have hstore : storeLoc
      (qSt σ (H ++ [(.base ⟨na⟩,
        (⟨some (.array 1 tU64), .array #[.int 0 .uint64]⟩ : HeapCell))])
        (na + 1))
      (.base ⟨a4⟩) (.slice ⟨some (.base ⟨na⟩), 0, 1, 1⟩)
      = .ok (qSt σ
          (Heap.set H (.base ⟨a4⟩)
            ⟨some sliceU, qslV na 0 1 1⟩
          ++ [(.base ⟨na⟩, arrCellU 1 [0])])
          (na + 1)) := by
    have hlk : Heap.lookup (H ++ [(.base ⟨na⟩,
        (⟨some (.array 1 tU64),
          .array #[.int 0 .uint64]⟩ : HeapCell))]) (.base ⟨a4⟩)
        = some ⟨some sliceU, old⟩ := lookup_append_left h4
    have hset := set_append_left
      (h₂ := [(.base ⟨na⟩, (⟨some (.array 1 tU64),
        .array #[.int 0 .uint64]⟩ : HeapCell))])
      (c := (⟨some sliceU, qslV na 0 1 1⟩ : HeapCell)) h4
    simp only [storeLoc, qSt, hlk, normVal_slice, Bind.bind, Except.bind,
      pure, Except.pure, hset]
    rfl
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
    Bind.bind, Except.bind, pure, Except.pure, hb,
    show natFromNonnegativeInt
      "runtime error: makeslice: len out of range" (1 : Int) = .ok 1
      from rfl,
    show natFromNonnegativeInt
      "runtime error: makeslice: cap out of range" (1 : Int) = .ok 1
      from rfl,
    show ((1 : Nat) < (1 : Nat)) = False from by simp,
    if_false, ExecState.alloc, ExecState.freshLoc, qSt]
  rw [set_fresh (hdead _ (Nat.le_refl _))]
  simp only [hstore, qSt, Bind.bind, Except.bind, pure, Except.pure]

/-! ## The conditioned frame entries (the one program-consulting step of
each call; the `findFunctionIn?` hypotheses are discharged ONCE at the
pinned program, by the subject pins). -/

/-- `enterFrame` for `enqueue(q, v)`: three fresh cells (the two
parameters, the `$res0` result). -/
theorem qenq_enterFrame {σ : ExecState} {H : Heap} {na : Nat}
    {qv : GoValue} {w : Int}
    (hfn : findFunctionIn? σ.functions ⟨"enqueue"⟩ = some enqueueFunc)
    (hm : σ.methods = #[]) (hdead : DeadFrom H na)
    (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    enterFrame (qSt σ H na) ⟨"enqueue"⟩ [qv, .int w .uint64]
      = .ok (enqueueFunc,
          [[("$res0", .base ⟨na + 2⟩), ("v", .base ⟨na + 1⟩),
            ("q", .base ⟨na⟩)]],
          [.base ⟨na + 2⟩],
          qSt σ (H ++ [(.base ⟨na⟩, slCell qv),
            (.base ⟨na + 1⟩, u64cell w),
            (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 3)) := by
  have hdd : dynamicDispatch? (qSt σ H na) enqueueFunc
      #[qv, .int w .uint64] = .ok none := by
    simp [dynamicDispatch?, methodInfoByFuncId?, qSt, hm]
  simp only [enterFrame, hfn, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp [enqueueFunc])]
  rw [show List.toArray [qv, GoValue.int w IntKind.uint64]
    = #[qv, GoValue.int w IntKind.uint64] from rfl]
  simp only [hdd, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp [enqueueFunc])]
  simp only [enqueueFunc, bindParams, normVal_slice,
    normVal_u64 _ hw.1 hw.2, defVal_sliceU, defVal_u64, allocDecls,
    pinResultLocs, LocalEnv.declare, LocalEnv.lookup, Scope.lookup,
    ExecState.alloc, ExecState.freshLoc, qSt, Bind.bind, Except.bind,
    pure, Except.pure]
  rw [set_fresh (hdead _ (Nat.le_refl _))]
  rw [set_fresh ((hdead.push (c := slCell qv)) _ (Nat.le_refl _))]
  rw [set_fresh (((hdead.push (c := slCell qv)).push
    (c := u64cell w)) _ (Nat.le_refl _))]
  rw [show na + 1 + 1 = na + 2 from rfl,
    show na + 1 + 1 + 1 = na + 3 from rfl]
  simp [List.append_assoc]

/-- `enterFrame` for `dequeue(q)`: three fresh cells (the parameter,
the two results). -/
theorem qdeq_enterFrame {σ : ExecState} {H : Heap} {na : Nat}
    {qv : GoValue}
    (hfn : findFunctionIn? σ.functions ⟨"dequeue"⟩ = some dequeueFunc)
    (hm : σ.methods = #[]) (hdead : DeadFrom H na) :
    enterFrame (qSt σ H na) ⟨"dequeue"⟩ [qv]
      = .ok (dequeueFunc,
          [[("$res1", .base ⟨na + 2⟩),
            ("$res0", .base ⟨na + 1⟩), ("q", .base ⟨na⟩)]],
          [.base ⟨na + 1⟩, .base ⟨na + 2⟩],
          qSt σ (H ++ [(.base ⟨na⟩, slCell qv),
            (.base ⟨na + 1⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 2⟩, u64cell 0)])
            (na + 3)) := by
  have hdd : dynamicDispatch? (qSt σ H na) dequeueFunc #[qv]
      = .ok none := by
    simp [dynamicDispatch?, methodInfoByFuncId?, qSt, hm]
  simp only [enterFrame, hfn, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp [dequeueFunc])]
  rw [show List.toArray [qv] = #[qv] from rfl]
  simp only [hdd, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp [dequeueFunc])]
  simp only [dequeueFunc, bindParams, normVal_slice, defVal_sliceU,
    defVal_u64, allocDecls, pinResultLocs, LocalEnv.declare,
    LocalEnv.lookup, Scope.lookup, ExecState.alloc, ExecState.freshLoc,
    qSt, Bind.bind, Except.bind, pure, Except.pure]
  rw [set_fresh (hdead _ (Nat.le_refl _))]
  rw [set_fresh ((hdead.push (c := slCell qv)) _ (Nat.le_refl _))]
  rw [set_fresh (((hdead.push (c := slCell qv)).push
    (c := slCell (.slice ⟨none, 0, 0, 0⟩))) _ (Nat.le_refl _))]
  rw [show na + 1 + 1 = na + 2 from rfl,
    show na + 1 + 1 + 1 = na + 3 from rfl]
  simp [List.append_assoc]

/-- `enterFrame` for `qsize(q)`: two fresh cells. -/
theorem qsize_enterFrame {σ : ExecState} {H : Heap} {na : Nat}
    {qv : GoValue}
    (hfn : findFunctionIn? σ.functions ⟨"qsize"⟩ = some qsizeFunc)
    (hm : σ.methods = #[]) (hdead : DeadFrom H na) :
    enterFrame (qSt σ H na) ⟨"qsize"⟩ [qv]
      = .ok (qsizeFunc,
          [[("$res0", .base ⟨na + 1⟩), ("q", .base ⟨na⟩)]],
          [.base ⟨na + 1⟩],
          qSt σ (H ++ [(.base ⟨na⟩, slCell qv),
            (.base ⟨na + 1⟩, u64cell 0)])
            (na + 2)) := by
  have hdd : dynamicDispatch? (qSt σ H na) qsizeFunc #[qv]
      = .ok none := by
    simp [dynamicDispatch?, methodInfoByFuncId?, qSt, hm]
  simp only [enterFrame, hfn, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp [qsizeFunc])]
  rw [show List.toArray [qv] = #[qv] from rfl]
  simp only [hdd, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp [qsizeFunc])]
  simp only [qsizeFunc, bindParams, normVal_slice, defVal_sliceU,
    defVal_u64, allocDecls, pinResultLocs, LocalEnv.declare,
    LocalEnv.lookup, Scope.lookup, ExecState.alloc, ExecState.freshLoc,
    qSt, Bind.bind, Except.bind, pure, Except.pure]
  rw [set_fresh (hdead _ (Nat.le_refl _))]
  rw [set_fresh ((hdead.push (c := slCell qv)) _ (Nat.le_refl _))]
  rw [show na + 1 + 1 = na + 2 from rfl]
  simp [List.append_assoc]

/-- Setting a live low cell preserves deadness above. -/
theorem DeadFrom.set_low {dead : Heap} {na B : Nat} {c : HeapCell}
    (h : DeadFrom dead na) (hB : B < na) :
    DeadFrom (Heap.set dead (.base ⟨B⟩) c) na := by
  intro x hx
  rw [Machine.Heap.lookup_set_ne (by
    simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
    omega)]
  exact h x hx

/-! ## The enqueue iteration (capacity- and address-generic)

The lane-owner's corrected charter: the machine's `append` spill
capacity is a NONDETERMINISM ENVELOPE (one choice consumed per spill),
so the backing address `B`, the capacity `C` and the dead-cell tail are
existentially packaged, never concrete. The invariant:

* `q = ⟨some B, 0, i, C⟩` with `i ≤ C`;
* the cell at `B` holds `qBack C i seed` (family prefix + zero slack);
* either the pristine `make([]uint64,0,0)` backing (`B = 7`, `C = 0` —
  forced to spill on the next enqueue) or a tail-resident backing;
* the tail is dead from `nextAddr` up.

One iteration is EXACTLY 130 steps on BOTH the in-place and the spill
path (`append` is one apply step either way — why the fuel formula is
choice-independent). -/

/-- The enqueue-phase invariant on the existential package. -/
def qEnqInv (seed i : Nat) (B C na : Nat) (tail : Heap) : Prop :=
  i ≤ C ∧ 12 ≤ na ∧ B < na ∧ DeadFrom tail na ∧
    ((i = 0 ∧ B = 7 ∧ C = 0) ∨
     (12 ≤ B ∧ Heap.lookup tail (.base ⟨B⟩)
        = some (arrCellU C (qBack C i seed))))

/-- The 64-step PRE-APPEND segment of one enqueue iteration: test-true
through the callee's operand evaluation, ending AT the append apply
point, with the seven per-iteration cells built at `na..na+6`. -/
theorem qe_pre (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na : Nat) (ch : Choices)
    (w : Int)
    (hfn : findFunctionIn? σ.functions ⟨"enqueue"⟩ = some enqueueFunc)
    (hm : σ.methods = #[])
    (h12 : 12 ≤ na) (htail : DeadFrom tail na)
    (hwr : 0 ≤ w ∧ w < 2 ^ 64)
    (hwv : IntKind.normalize .uint64 (sv + iv) = w) :
    stepFnIter 64
      (qStE σ nv sv kv qv lE iv false tail na)
      (.retV (.bool true) qeCmpK) ch
      = .ok (.retV (qslV (na + 5) 0 1 1) (eqAppK2 na qv),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w),
              (.base ⟨na + 1⟩, slCell qv), (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w]),
              (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 7), ch) := by
  have hFdead : DeadFrom (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
      ++ tail) na := qHeap_dead h12 htail
  have h1 := qe_S1_raw (qStE σ nv sv kv qv lE iv false tail na) ch
  have h2 := stepFnIter_one (stepFn_init_seq
    (σ := qStE σ nv sv kv qv lE iv false tail na)
    (p := { id := "v", typ := tU64 })
    (rest := [.assign (.var "v") (.add (.var "seed") (.var "i")),
      qeCallSeqn, qeStoreSeqn])
    (env := qeEnv2) (k := .seq [] qeEnv1 qeLoopK) (ch := ch)
    (hdef := by with_unfolding_all rfl))
  rw [show LocalEnv.declare qeEnv2 "v"
      (.base ⟨(qStE σ nv sv kv qv lE iv false tail na).nextAddr⟩)
    = qeEnvV na from rfl] at h2
  rw [show Heap.set (qStE σ nv sv kv qv lE iv false tail na).heap
      (.base ⟨(qStE σ nv sv kv qv lE iv false tail na).nextAddr⟩)
      ⟨some tU64, .int 0 .uint64⟩
    = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell 0)]) from by
      rw [show (qStE σ nv sv kv qv lE iv false tail na).heap
        = qFront nv sv kv zeros8 zeros8 0 qv lE iv false ++ tail from rfl,
        set_fresh (hFdead _ (Nat.le_refl _)), List.append_assoc]] at h2
  have h12b := stepFnIter_chain h1 h2
  have h3 := qe_S2_raw σ nv sv kv qv lE iv
    (tail ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1) na ch
  rw [hwv] at h3
  have hlkv0 : Heap.lookup
      ((qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1)).heap) (.base ⟨na⟩)
      = some (u64cell 0) := by
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
      ++ (tail ++ [(.base ⟨na⟩, u64cell 0)])) (.base ⟨na⟩)
      = some (u64cell 0)
    rw [lookup_append_right (qFront_miss h12),
      lookup_append_right (htail _ (Nat.le_refl _))]
    exact lookup_singleton_self
  have hst4 : storeTarget
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
      (.chain (.addr (.base ⟨na⟩)) [] []) (.int w .uint64)
      = .ok (qSt σ (Heap.set (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell 0)])) (.base ⟨na⟩)
          ⟨some tU64, .int w .uint64⟩) (na + 1)) :=
    storeTarget_addr hlkv0 (normVal_u64 _ hwr.1 hwr.2)
  rw [show Heap.set (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
      ++ (tail ++ [(.base ⟨na⟩, u64cell 0)])) (.base ⟨na⟩)
      ⟨some tU64, .int w .uint64⟩
    = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w)]) from by
      rw [set_append_right (qFront_miss h12),
        set_append_right (htail _ (Nat.le_refl _)), set_singleton_self]]
    at hst4
  have h4 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.int w .uint64] (.seqn #[]) (qeEnvV na) (qeVTail na))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qeEnvV na) (qeVTail na)),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1), ch) :=
    stepFnIter_one (stepFn_store_step hst4)
  have h14 := stepFnIter_chain (stepFnIter_chain h12b h3) h4
  have h5 := qe_S3_raw σ nv sv kv qv lE iv
    (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1) na ch
  have h6 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1))
      (.evalE (.var "v") (qeEnvV na) (qeCallArgsK na qv)) ch
      = .ok (.retV (.int w .uint64) (qeCallArgsK na qv),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1), ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell w) rfl ?_)
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w)])) (.base ⟨na⟩)
      = some (u64cell w)
    rw [lookup_append_right (qFront_miss h12),
      lookup_append_right (htail _ (Nat.le_refl _))]
    exact lookup_singleton_self
  have hdead1 : DeadFrom (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1) :=
    htail.push
  have hef : enterFrame
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1))
      ⟨"enqueue"⟩ [qv, .int w .uint64]
      = .ok (enqueueFunc, eqEnv na, [.base ⟨na + 3⟩],
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 4)) := by
    have hdF1 : DeadFrom
        ((qStE σ nv sv kv qv lE iv false
          (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1)).heap)
        ((qStE σ nv sv kv qv lE iv false
          (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1)).nextAddr) := by
      show DeadFrom (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w)])) (na + 1)
      exact qHeap_dead (by omega) hdead1
    have h := qenq_enterFrame
      (σ := qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1))
      (qv := qv) (w := w) hfn hm hdF1 hwr
    rw [show (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1)).nextAddr
      = na + 1 from rfl] at h
    rw [show (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1)).heap
      = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell w)]) from rfl] at h
    rw [show na + 1 + 1 = na + 2 from by omega,
      show na + 1 + 2 = na + 3 from by omega,
      show na + 1 + 3 = na + 4 from by omega] at h
    rw [show qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w)])
        ++ [(.base ⟨na + 1⟩, slCell qv), (.base ⟨na + 2⟩, u64cell w),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]
      = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) from by
      simp [List.append_assoc]] at h
    exact h
  have h7 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w)]) (na + 1))
      (.retV (.int w .uint64) (qeCallArgsK na qv)) ch
      = .ok (.exec enqueueFunc.body (eqEnv na) (qeFrameK na),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 4), ch) :=
    stepFnIter_one (stepFn_call_enter hef)
  have h17 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h14 h5)
    h6) h7
  have h8 := qe_S4_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 4)) na ch
  have hdead4 : DeadFrom
      (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
        (.base ⟨na + 2⟩, u64cell w),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 4) := by
    intro x hx
    rw [lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x))]
    rfl
  have h9 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 4))
      (.exec (.initialization { id := "$c0", typ := sliceU })
        ([] :: eqEnv na)
        (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn]
          ([] :: eqEnv na) (qeFrameK na))) ch
      = .ok (.next (.seq [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn]
          (eqEnvC0 na) (qeFrameK na)),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 5), ch) := by
    have h := stepFnIter_one (stepFn_init_seq
      (σ := qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 4))
      (p := { id := "$c0", typ := sliceU })
      (rest := [.makeSlice (.var "$c0") tU64 (.intLit 1 .int)
        (some (.intLit 1 .int)), eqC0Assign, eqC1Seqn, eqRetSeqn])
      (env := [] :: eqEnv na) (k := qeFrameK na) (ch := ch)
      (hdef := by with_unfolding_all rfl))
    rw [show LocalEnv.declare ([] :: eqEnv na) "$c0"
        (.base ⟨(qStE σ nv sv kv qv lE iv false
          (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
            (.base ⟨na + 2⟩, u64cell w),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
          (na + 4)).nextAddr⟩) = eqEnvC0 na from rfl] at h
    rw [show Heap.set (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
        (na + 4)).heap
        (.base ⟨(qStE σ nv sv kv qv lE iv false
          (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
            (.base ⟨na + 2⟩, u64cell w),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
          (na + 4)).nextAddr⟩)
        ⟨some sliceU, .slice ⟨none, 0, 0, 0⟩⟩
      = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) from by
        rw [show (qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 4)).heap
          = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
              ++ (tail ++ [(.base ⟨na⟩, u64cell w),
                (.base ⟨na + 1⟩, slCell qv), (.base ⟨na + 2⟩, u64cell w),
                (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            from rfl,
          show (qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 4)).nextAddr = na + 4 from rfl,
          set_fresh ((qHeap_dead (by omega) hdead4) _ (Nat.le_refl _))]
        simp [List.append_assoc]] at h
    exact h
  have h10 := qe_S5_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 5)) na ch
  have h20 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h17 h8)
    h9) h10
  have hdead5 : DeadFrom
      (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
        (.base ⟨na + 2⟩, u64cell w),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 5) := by
    intro x hx
    rw [lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x))]
    rfl
  have hlk4 : Heap.lookup
      ((qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
        (na + 5)).heap)
      (.base ⟨na + 4⟩)
      = some ⟨some sliceU, .slice ⟨none, 0, 0, 0⟩⟩ := by
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
      ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
        (.base ⟨na + 2⟩, u64cell w),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
      (.base ⟨na + 4⟩)
      = some ⟨some sliceU, .slice ⟨none, 0, 0, 0⟩⟩
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
    simp [Heap.lookup]
  have hdF5 : DeadFrom
      ((qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
        (na + 5)).heap)
      ((qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
        (na + 5)).nextAddr) := by
    show DeadFrom (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
      ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
        (.base ⟨na + 2⟩, u64cell w),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])) (na + 5)
    exact qHeap_dead (by omega) hdead5
  have hmk : applyStmtOp
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 5))
      ch (.makeSlice tU64 true) 1
      [.addr (.base ⟨na + 4⟩), .int 1 .int, .int 1 .int]
      = .ok (qStE σ nv sv kv qv lE iv false
          (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
            (.base ⟨na + 2⟩, u64cell w),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6), ch) := by
    have h := qmake11_apply
      (σ := qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 5))
      (a4 := na + 4) (ch := ch) hlk4 hdF5
    rw [show (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
        (na + 5)).nextAddr = na + 5 from rfl] at h
    rw [show (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
        (na + 5)).heap
      = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
        from rfl] at h
    rw [show na + 5 + 1 = na + 6 from by omega] at h
    rw [show Heap.set (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
        (.base ⟨na + 4⟩) ⟨some sliceU, qslV (na + 5) 0 1 1⟩
        ++ [(.base ⟨na + 5⟩, arrCellU 1 [0])]
      = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [0])]) from by
        rw [set_append_right (qFront_miss (by omega)),
          set_append_right (htail _ (by omega))]
        rw [show Heap.set [(Loc.base ⟨na⟩, u64cell w),
            (Loc.base ⟨na + 1⟩, slCell qv), (Loc.base ⟨na + 2⟩, u64cell w),
            (Loc.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (Loc.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]
            (.base ⟨na + 4⟩) ⟨some sliceU, qslV (na + 5) 0 1 1⟩
          = [(Loc.base ⟨na⟩, u64cell w), (Loc.base ⟨na + 1⟩, slCell qv),
             (Loc.base ⟨na + 2⟩, u64cell w),
             (Loc.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
             (Loc.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1))] from by
            simp [Heap.set, base_beq_false (by omega : na ≠ na + 4),
              base_beq_false (by omega : na + 1 ≠ na + 4),
              base_beq_false (by omega : na + 2 ≠ na + 4),
              base_beq_false (by omega : na + 3 ≠ na + 4)]]
        simp [List.append_assoc]] at h
    exact h
  have h11 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 5))
      (.retV (.int 1 .int)
        (.stmtOpK (.makeSlice tU64 true) 1
          [.int 1 .int, .addr (.base ⟨na + 4⟩)] [] (eqEnvC0 na)
          (eqKmk na))) ch
      = .ok (.next (eqKmk na),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6), ch) :=
    stepFnIter_one (stepFn_stmtOp_apply hmk)
  have h21 := stepFnIter_chain h20 h11
  have h22 := qe_S6_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
      (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6)) na ch
  have h23 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6))
      (.evalE (.var "$c0") (eqEnvC0 na) (eqTgtK na)) ch
      = .ok (.retV (qslV (na + 5) 0 1 1) (eqTgtK na),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := slCell (qslV (na + 5) 0 1 1)) rfl ?_)
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])])) (.base ⟨na + 4⟩)
      = some (slCell (qslV (na + 5) 0 1 1))
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
    simp [Heap.lookup]
  have h24 := qe_S7_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
      (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6)) na ch
  have h25 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6))
      (.evalE (.var "v") (eqEnvC0 na) (eqRhsK na)) ch
      = .ok (.retV (.int w .uint64) (eqRhsK na),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6), ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell w) rfl ?_)
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])])) (.base ⟨na + 2⟩)
      = some (u64cell w)
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
    simp [Heap.lookup]
  have h26 := qe_S8_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
      (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6)) na
    (.int w .uint64) ch
  have hlk5 : Heap.lookup
      ((qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6)).heap)
      (.base ⟨na + 5⟩)
      = some ⟨some (.array 1 tU64),
          .array ⟨([0] : List Int).map (fun v => .int v .uint64)⟩⟩ := by
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
      ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
        (.base ⟨na + 2⟩, u64cell w),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩, arrCellU 1 [0])])) (.base ⟨na + 5⟩)
      = some ⟨some (.array 1 tU64),
          .array ⟨([0] : List Int).map (fun v => .int v .uint64)⟩⟩
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 5))]
    simp [Heap.lookup]
  have hstc0 : storeTarget
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6))
      (.chain (qslV (na + 5) 0 1 1) [.int 0 .int] [.index])
      (.int w .uint64)
      = .ok (qSt σ
          (Heap.set ((qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6)).heap)
            (.base ⟨na + 5⟩)
            ⟨some (.array 1 tU64),
             .array ⟨(([0] : List Int).set 0 w).map
               (fun v => .int v .uint64)⟩⟩)
          (na + 6)) := by
    have h := storeTarget_slice_u64
      (σ := qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6))
      (a := ⟨na + 5⟩) (off := 0) (len := 1) (cap := 1) (i := 0) (n := 1)
      (ik := .int) (l := [0]) (w := w)
      hlk5 (Nat.le_refl 1) (by omega) (by simp) (by simp)
      (by intro v hv; simp at hv; omega) hwr
    rw [show ((0 : Nat) + 0) = 0 from rfl] at h
    exact h
  have h27 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6))
      (.next (.storeK
        [.chain (qslV (na + 5) 0 1 1) [.int 0 .int] [.index]]
        [.int w .uint64] (.seqn #[]) (eqEnvC0 na) (eqTail2 na))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (eqEnvC0 na) (eqTail2 na)),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w])]) (na + 6), ch) := by
    have hs := stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
      (body := .seqn #[]) (env := eqEnvC0 na) (k := eqTail2 na)
      (ch := ch) hstc0)
    rw [show Heap.set ((qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6)).heap)
        (.base ⟨na + 5⟩)
        ⟨some (.array 1 tU64),
         .array ⟨(([0] : List Int).set 0 w).map (fun v => .int v .uint64)⟩⟩
      = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w])]) from by
        rw [show (qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [0])]) (na + 6)).heap
          = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
              ++ (tail ++ [(.base ⟨na⟩, u64cell w),
                (.base ⟨na + 1⟩, slCell qv), (.base ⟨na + 2⟩, u64cell w),
                (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
                (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
                (.base ⟨na + 5⟩, arrCellU 1 [0])]) from rfl,
          set_append_right (qFront_miss (by omega)),
          set_append_right (htail _ (by omega))]
        simp [Heap.set, base_beq_false (by omega : na ≠ na + 5),
          base_beq_false (by omega : na + 1 ≠ na + 5),
          base_beq_false (by omega : na + 2 ≠ na + 5),
          base_beq_false (by omega : na + 3 ≠ na + 5),
          base_beq_false (by omega : na + 4 ≠ na + 5)]] at hs
    exact hs
  have h30 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h21 h22) h23)
      h24) h25) h26) h27
  have h31 := qe_S9_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
      (.base ⟨na + 5⟩, arrCellU 1 [w])]) (na + 6)) na ch
  have hdead6 : DeadFrom
      (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
        (.base ⟨na + 2⟩, u64cell w),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩, arrCellU 1 [w])]) (na + 6) := by
    intro x hx
    rw [lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ x))]
    rfl
  have h32 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [w])]) (na + 6))
      (.exec (.initialization { id := "$c1", typ := sliceU })
        (eqEnvC0 na)
        (.seq [.appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0"),
          eqRetSeqn] (eqEnvC0 na) (qeFrameK na))) ch
      = .ok (.next (.seq [.appendSlice (.var "$c1") tU64 (.var "q")
            (.var "$c0"), eqRetSeqn] (eqEnvC1 na) (qeFrameK na)),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w]),
              (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 7), ch) := by
    have h := stepFnIter_one (stepFn_init_seq
      (σ := qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [w])]) (na + 6))
      (p := { id := "$c1", typ := sliceU })
      (rest := [.appendSlice (.var "$c1") tU64 (.var "q") (.var "$c0"),
        eqRetSeqn])
      (env := eqEnvC0 na) (k := qeFrameK na) (ch := ch)
      (hdef := by with_unfolding_all rfl))
    rw [show LocalEnv.declare (eqEnvC0 na) "$c1"
        (.base ⟨(qStE σ nv sv kv qv lE iv false
          (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
            (.base ⟨na + 2⟩, u64cell w),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩, arrCellU 1 [w])])
          (na + 6)).nextAddr⟩) = eqEnvC1 na from rfl] at h
    rw [show Heap.set (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [w])])
        (na + 6)).heap
        (.base ⟨(qStE σ nv sv kv qv lE iv false
          (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
            (.base ⟨na + 2⟩, u64cell w),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩, arrCellU 1 [w])])
          (na + 6)).nextAddr⟩)
        ⟨some sliceU, .slice ⟨none, 0, 0, 0⟩⟩
      = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w]),
              (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) from by
        rw [show (qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w])])
            (na + 6)).heap
          = qFront nv sv kv zeros8 zeros8 0 qv lE iv false
              ++ (tail ++ [(.base ⟨na⟩, u64cell w),
                (.base ⟨na + 1⟩, slCell qv), (.base ⟨na + 2⟩, u64cell w),
                (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
                (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
                (.base ⟨na + 5⟩, arrCellU 1 [w])])
            from rfl,
          show (qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w])])
            (na + 6)).nextAddr = na + 6 from rfl,
          set_fresh ((qHeap_dead (by omega) hdead6) _ (Nat.le_refl _))]
        simp [List.append_assoc]] at h
    exact h
  have h33 := qe_S10_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
      (.base ⟨na + 5⟩, arrCellU 1 [w]),
      (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7)) na ch
  have h34 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [w]),
          (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7))
      (.evalE (.var "q") (eqEnvC1 na) (eqAppK1 na)) ch
      = .ok (.retV qv (eqAppK1 na),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w]),
              (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 7), ch) := by
    refine stepFnIter_one (stepFn_var (c := slCell qv) rfl ?_)
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [w]),
          (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
        (.base ⟨na + 1⟩)
      = some (slCell qv)
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    simp [Heap.lookup]
  have h35 := qe_S11_raw (qStE σ nv sv kv qv lE iv false
    (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
      (.base ⟨na + 2⟩, u64cell w),
      (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
      (.base ⟨na + 5⟩, arrCellU 1 [w]),
      (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7)) na qv ch
  have h36 : stepFnIter 1
      (qStE σ nv sv kv qv lE iv false
        (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [w]),
          (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7))
      (.evalE (.var "$c0") (eqEnvC1 na) (eqAppK2 na qv)) ch
      = .ok (.retV (qslV (na + 5) 0 1 1) (eqAppK2 na qv),
          qStE σ nv sv kv qv lE iv false
            (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
              (.base ⟨na + 2⟩, u64cell w),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩, arrCellU 1 [w]),
              (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])
            (na + 7), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := slCell (qslV (na + 5) 0 1 1)) rfl ?_)
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨na⟩, u64cell w), (.base ⟨na + 1⟩, slCell qv),
          (.base ⟨na + 2⟩, u64cell w),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩, arrCellU 1 [w]),
          (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
        (.base ⟨na + 4⟩)
      = some (slCell (qslV (na + 5) 0 1 1))
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 4)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 4))]
    simp [Heap.lookup]
  have h40 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h30 h31) h32)
      h33) h34) h35) h36
  rw [show 7 + 1 + 10 + 1 + 8 + 1 + 1 + 4 + 1 + 7 + 1 + 2 + 1 + 3 + 1 + 1
      + 1 + 5 + 1 + 4 + 1 + 1 + 1 = 64 from by omega] at h40
  exact h40

/-- The 65-step POST-APPEND segment: the append's `.next` through the
callee return, the write-back into `q` (front cell 8), the
`enqueued[i] = v` store, and the incremented dispatch to the next exit
test. Generic in the post-append tail `T` (which differs between the
in-place and the spill branch) through three cell-lookup hypotheses. -/
theorem qe_post (σ : ExecState) (nv sv kv : Int) (qv rv : GoValue)
    (lE : List Int) (i : Nat) (tail2 : Heap) (na2 a : Nat) (ch : Choices)
    (w : Int)
    (h12 : 12 ≤ a)
    (hT3 : Heap.lookup tail2 (.base ⟨a + 3⟩)
      = some (slCell (.slice ⟨none, 0, 0, 0⟩)))
    (hT6 : Heap.lookup tail2 (.base ⟨a + 6⟩) = some (slCell rv))
    (hT0 : Heap.lookup tail2 (.base ⟨a⟩) = some (u64cell w))
    (hi8 : i < 8) (hlen : lE.length = 8)
    (hrE : ∀ v ∈ lE, 0 ≤ v ∧ v < 2 ^ 64) (hwr : 0 ≤ w ∧ w < 2 ^ 64) :
    stepFnIter 65
      (qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2)
      (.next (eqKapp a)) ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64 (((i : Nat) : Int) + 1)) < nv)))
          qeCmpK,
          qStE σ nv sv kv rv (lE.set i w)
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64 (((i : Nat) : Int) + 1)))
            false (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2, ch) := by
  -- S12 (6) + $c1 read (1) + S13 (1) + $res0 store (1) + S14 (5)
  have h1 := qe_S12_raw
    (qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2) a ch
  have h2 : stepFnIter 1
      (qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2)
      (.evalE (.var "$c1") (eqEnvC1 a) (eqResRhsK a)) ch
      = .ok (.retV rv (eqResRhsK a),
          qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2, ch) := by
    refine stepFnIter_one (stepFn_var (c := slCell rv) rfl ?_)
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE
        ((i : Nat) : Int) false ++ tail2) (.base ⟨a + 6⟩)
      = some (slCell rv)
    rw [lookup_append_right (qFront_miss (by omega))]
    exact hT6
  have h3 := qe_S13_raw
    (qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2) a rv ch
  have hlk3 : Heap.lookup
      ((qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2).heap)
      (.base ⟨a + 3⟩) = some (slCell (.slice ⟨none, 0, 0, 0⟩)) := by
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE
        ((i : Nat) : Int) false ++ tail2) (.base ⟨a + 3⟩)
      = some (slCell (.slice ⟨none, 0, 0, 0⟩))
    rw [lookup_append_right (qFront_miss (by omega))]
    exact hT3
  have hst3 : storeTarget
      (qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2)
      (.chain (.addr (.base ⟨a + 3⟩)) [] []) rv
      = .ok (qSt σ
          (Heap.set (qFront nv sv kv zeros8 zeros8 0 qv lE
            ((i : Nat) : Int) false ++ tail2) (.base ⟨a + 3⟩)
            ⟨some sliceU, rv⟩) na2) :=
    storeTarget_addr hlk3 (normVal_slice _ rv)
  rw [show Heap.set (qFront nv sv kv zeros8 zeros8 0 qv lE
        ((i : Nat) : Int) false ++ tail2) (.base ⟨a + 3⟩)
        ⟨some sliceU, rv⟩
      = qFront nv sv kv zeros8 zeros8 0 qv lE ((i : Nat) : Int) false
          ++ Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv) from by
    rw [set_append_right (qFront_miss (by omega))]] at hst3
  have h4 : stepFnIter 1
      (qStE σ nv sv kv qv lE ((i : Nat) : Int) false tail2 na2)
      (.next (.storeK [.chain (.addr (.base ⟨a + 3⟩)) [] []] [rv]
        (.seqn #[]) (eqEnvC1 a) (eqKret a))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (eqEnvC1 a) (eqKret a)),
          qStE σ nv sv kv qv lE ((i : Nat) : Int) false
            (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2, ch) :=
    stepFnIter_one (stepFn_store_step hst3)
  have h5 := qe_S14_raw (qStE σ nv sv kv qv lE ((i : Nat) : Int) false
    (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2) a ch
  have h15 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5
  -- loadMany (1) + S15 (13) + v read (1) + S16 (1) + enqueued store (1)
  have hload : loadMany
      (qStE σ nv sv kv qv lE ((i : Nat) : Int) false
        (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2)
      [.base ⟨a + 3⟩] = .ok [rv] := by
    refine loadMany_one (c := slCell rv) ?_
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE
        ((i : Nat) : Int) false ++ Heap.set tail2 (.base ⟨a + 3⟩)
          (slCell rv)) (.base ⟨a + 3⟩)
      = some (slCell rv)
    rw [lookup_append_right (qFront_miss (by omega))]
    exact Frame.Heap.lookup_set_self
  have h6 : stepFnIter 1
      (qStE σ nv sv kv qv lE ((i : Nat) : Int) false
        (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2)
      (.returning (qeFrameK a)) ch
      = .ok (.evalE (.ref "q") (qeEnvV a) (qeWbK a rv),
          qStE σ nv sv kv qv lE ((i : Nat) : Int) false
            (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2, ch) := by
    refine stepFnIter_one (stepFn_return_frame (vs := [rv]) hload)
  have h7 := qe_S15_raw σ nv sv kv qv rv lE ((i : Nat) : Int)
    (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2 a ch
  have h8 : stepFnIter 1
      (qStE σ nv sv kv rv lE ((i : Nat) : Int) false
        (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2)
      (.evalE (.var "v") (qeEnvV a) (qeStRhsK a ((i : Nat) : Int))) ch
      = .ok (.retV (.int w .uint64) (qeStRhsK a ((i : Nat) : Int)),
          qStE σ nv sv kv rv lE ((i : Nat) : Int) false
            (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2, ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell w) rfl ?_)
    show Heap.lookup (qFront nv sv kv zeros8 zeros8 0 rv lE
        ((i : Nat) : Int) false ++ Heap.set tail2 (.base ⟨a + 3⟩)
          (slCell rv)) (.base ⟨a⟩)
      = some (u64cell w)
    rw [lookup_append_right (qFront_miss (by omega)),
      Machine.Heap.lookup_set_ne (by
        simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
        omega)]
    exact hT0
  have h9 := qe_S16_raw (qStE σ nv sv kv rv lE ((i : Nat) : Int) false
    (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2) a ((i : Nat) : Int)
    (.int w .uint64) ch
  have hlk9 : Heap.lookup
      ((qStE σ nv sv kv rv lE ((i : Nat) : Int) false
        (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2).heap)
      (.base ⟨9⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lE.map (fun v => .int v .uint64)⟩⟩ := rfl
  have hstE : storeTarget
      (qStE σ nv sv kv rv lE ((i : Nat) : Int) false
        (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2)
      (.chain (.addr (.base ⟨9⟩)) [.int ((i : Nat) : Int) .uint64]
        [.index])
      (.int w .uint64)
      = .ok (qSt σ
          (Heap.set ((qStE σ nv sv kv rv lE ((i : Nat) : Int) false
            (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2).heap)
            (.base ⟨9⟩)
            ⟨some (.array 8 tU64),
             .array ⟨(lE.set i w).map (fun v => .int v .uint64)⟩⟩)
          na2) :=
    storeTarget_arrayLocal_u64 hlk9 (by omega) hlen hrE hwr
  rw [show Heap.set ((qStE σ nv sv kv rv lE ((i : Nat) : Int) false
        (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2).heap)
        (.base ⟨9⟩)
        ⟨some (.array 8 tU64),
         .array ⟨(lE.set i w).map (fun v => .int v .uint64)⟩⟩
      = qFront nv sv kv zeros8 zeros8 0 rv (lE.set i w)
          ((i : Nat) : Int) false
          ++ Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv) from rfl] at hstE
  have h10 : stepFnIter 1
      (qStE σ nv sv kv rv lE ((i : Nat) : Int) false
        (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2)
      (.next (.storeK
        [.chain (.addr (.base ⟨9⟩)) [.int ((i : Nat) : Int) .uint64]
          [.index]]
        [.int w .uint64] (.seqn #[]) (qeEnvV a) (qeEndTail a))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qeEnvV a) (qeEndTail a)),
          qStE σ nv sv kv rv (lE.set i w) ((i : Nat) : Int) false
            (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2, ch) :=
    stepFnIter_one (stepFn_store_step hstE)
  -- S17 (34)
  have h11 := qe_S17_raw σ nv sv kv rv (lE.set i w) ((i : Nat) : Int)
    (Heap.set tail2 (.base ⟨a + 3⟩) (slCell rv)) na2 a ch
  have h25 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h15 h6) h7) h8)
      h9) h10) h11
  rw [show 6 + 1 + 1 + 1 + 5 + 1 + 13 + 1 + 1 + 1 + 34 = 65 from by omega]
    at h25
  exact h25

/-- A full backing plus the appended element plus the fresh zero slack
IS the advanced backing at the spill capacity. -/
theorem qBack_spill_adv {C K seed : Nat} (hK : C + 1 ≤ K) :
    qBack C C seed ++ [(((seed + C) % 2 ^ 64 : Nat) : Int)]
      ++ List.replicate (K - (C + 1)) 0 = qBack K (C + 1) seed := by
  rw [qBack, qBack, Nat.sub_self, qFam_succ]
  simp [List.append_assoc]

/-- **One enqueue iteration, capacity- and address-generic** (the
corrected charter's shape): EXACTLY 130 steps on both the in-place and
the spill path; the spill consumes one capacity choice from the
envelope, the in-place path consumes none; the existential package
carries the (choice-dependent) backing address, capacity, dead tail and
remaining stream. -/
theorem qe_iter (σ : ExecState) (n seed k : Nat) (i : Nat) (B C : Nat)
    (tail : Heap) (na : Nat) (ch : Choices)
    (hfn : findFunctionIn? σ.functions ⟨"enqueue"⟩ = some enqueueFunc)
    (hm : σ.methods = #[])
    (hin : i < n) (hn8 : n ≤ 8)
    (hinv : qEnqInv seed i B C na tail) :
    ∃ (B' C' : Nat) (tail' : Heap) (na' : Nat) (ch' : Choices),
      stepFnIter 130
        (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
          (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int) false tail na)
        (.retV (.bool true) qeCmpK) ch
        = .ok (.retV (.bool (decide
              (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) qeCmpK,
            qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
              (qslV B' 0 (i + 1) C') (qPre (i + 1) seed)
              ((i + 1 : Nat) : Int) false tail' na', ch')
      ∧ na ≤ na' ∧ qEnqInv seed (i + 1) B' C' na' tail' := by
  obtain ⟨hiC, h12, hBna, htail, hsplit⟩ := hinv
  have hwr : (0 : Int) ≤ (((seed + i) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i) (y := 2 ^ 64) (by omega)
    omega
  have hwv : IntKind.normalize .uint64
      (((seed : Nat) : Int) + ((i : Nat) : Int))
      = (((seed + i) % 2 ^ 64 : Nat) : Int) := unorm_add_nat seed i
  -- The 64-step prefix
  have hpre := qe_pre σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((k : Nat) : Int) (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int)
    tail na ch (((seed + i) % 2 ^ 64 : Nat) : Int) hfn hm h12 htail hwr hwv
  -- Common abbreviations for the seven fresh cells
  have hTdead : DeadFrom
      (tail ++ [(.base ⟨na⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
        (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩, arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7) := by
    intro x hx
    rw [lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 6 ≠ x))]
    rfl
  have hHdead : DeadFrom
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
        zeros8 zeros8 0 (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int)
        false
      ++ (tail ++ [(.base ⟨na⟩,
          u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
        (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩, arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))])) (na + 7) :=
    qHeap_dead (by omega) hTdead
  have hlkbc : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
        zeros8 zeros8 0 (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int)
        false
      ++ (tail ++ [(.base ⟨na⟩,
          u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
        (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩, arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
      (.base ⟨na + 5⟩)
      = some ⟨some (.array 1 tU64),
          .array ⟨[(((seed + i) % 2 ^ 64 : Nat) : Int)].map
            (fun v => .int v .uint64)⟩⟩ := by
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 5)),
      lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 5))]
    simp [Heap.lookup]
  have hlktc : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
        zeros8 zeros8 0 (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int)
        false
      ++ (tail ++ [(.base ⟨na⟩,
          u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
        (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩, arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
      (.base ⟨na + 6⟩)
      = some ⟨some sliceU, .slice ⟨none, 0, 0, 0⟩⟩ := by
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (htail _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 6)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 6)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 6)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 6)),
      lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 6)),
      lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ na + 6))]
    simp [Heap.lookup]
  have hlkB : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
        zeros8 zeros8 0 (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int)
        false
      ++ (tail ++ [(.base ⟨na⟩,
          u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
        (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩, arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
      (.base ⟨B⟩)
      = some ⟨some (.array C tU64),
          .array ⟨(qBack C i seed).map (fun v => .int v .uint64)⟩⟩ := by
    rcases hsplit with ⟨hi0, hB7, hC0⟩ | ⟨hB12, hBtail⟩
    · subst hi0; subst hB7; subst hC0
      show Heap.lookup _ (.base ⟨7⟩) = _
      simp [qFront, Heap.lookup, qBack, qFam]
    · rw [lookup_append_right (qFront_miss hB12),
        lookup_append_left hBtail]
  have hrq : ∀ v ∈ qBack C i seed, 0 ≤ v ∧ v < 2 ^ 64 := qBack_range
  have hnorm2 : IntKind.normalize .uint64
      (IntKind.normalize .uint64 (((i : Nat) : Int) + 1))
      = ((i + 1 : Nat) : Int) := by
    rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
      unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64),
      unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64)]
  by_cases hcase : i + 1 ≤ C
  · -- IN-PLACE: the backing has room; B is tail-resident (C ≥ 1).
    have hB12 : 12 ≤ B ∧ Heap.lookup tail (.base ⟨B⟩)
        = some (arrCellU C (qBack C i seed)) := by
      rcases hsplit with ⟨-, -, hC0⟩ | h
      · omega
      · exact h
    have happly : applyStmtOp
        (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
          (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int) false
          (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
            (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7))
        ch (.appendSlice tU64) 1
        [.addr (.base ⟨na + 6⟩), qslV B 0 i C, qslV (na + 5) 0 1 1]
        = .ok (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int)
            ((k : Nat) : Int) (qslV B 0 i C) (qPre i seed)
            ((i : Nat) : Int) false
            (Heap.set tail (.base ⟨B⟩)
              (arrCellU C (qBack C (i + 1) seed))
            ++ [(.base ⟨na⟩,
                u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
              (.base ⟨na + 2⟩,
                u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩,
                arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
              (.base ⟨na + 6⟩, slCell (qslV B 0 (i + 1) C))]) (na + 7),
          ch) := by
      have h := qappend_inplace
        (σ := σ) (na := na + 7)
        (H := qFront ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k : Nat) : Int) zeros8 zeros8 0 (qslV B 0 i C) (qPre i seed)
          ((i : Nat) : Int) false
          ++ (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
            (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
        (B := B) (bc := na + 5) (tc := na + 6) (i := i) (C := C)
        (lq := qBack C i seed)
        (w := (((seed + i) % 2 ^ 64 : Nat) : Int))
        (old := .slice ⟨none, 0, 0, 0⟩) (ch := ch)
        hlkB hlkbc hlktc (by omega) (qBack_length hiC) hcase hrq hwr
      rw [qBack_set (by omega : i < C)] at h
      rw [show Heap.set (Heap.set (qFront ((n : Nat) : Int)
            ((seed : Nat) : Int) ((k : Nat) : Int) zeros8 zeros8 0
            (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int) false
          ++ (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
            (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
          (.base ⟨B⟩)
          ⟨some (.array C tU64),
           .array ⟨(qBack C (i + 1) seed).map (fun v => .int v .uint64)⟩⟩)
          (.base ⟨na + 6⟩) ⟨some sliceU, qslV B 0 (i + 1) C⟩
        = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
            zeros8 zeros8 0 (qslV B 0 i C) (qPre i seed)
            ((i : Nat) : Int) false
          ++ (Heap.set tail (.base ⟨B⟩)
              (arrCellU C (qBack C (i + 1) seed))
            ++ [(.base ⟨na⟩,
                u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
              (.base ⟨na + 2⟩,
                u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩,
                arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
              (.base ⟨na + 6⟩, slCell (qslV B 0 (i + 1) C))]) from by
          rw [set_append_right (qFront_miss (by omega)),
            set_append_left hB12.2,
            set_append_right (qFront_miss (by omega)),
            set_append_right (by
              rw [Machine.Heap.lookup_set_ne (by
                simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
                omega)]
              exact htail _ (by omega))]
          congr 2
          simp [Heap.set, base_beq_false (by omega : na ≠ na + 6),
            base_beq_false (by omega : na + 1 ≠ na + 6),
            base_beq_false (by omega : na + 2 ≠ na + 6),
            base_beq_false (by omega : na + 3 ≠ na + 6),
            base_beq_false (by omega : na + 4 ≠ na + 6),
            base_beq_false (by omega : na + 5 ≠ na + 6)]] at h
      exact h
    have happstep : stepFnIter 1
        (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
          (qslV B 0 i C) (qPre i seed) ((i : Nat) : Int) false
          (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
            (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7))
        (.retV (qslV (na + 5) 0 1 1) (eqAppK2 na (qslV B 0 i C))) ch
        = .ok (.next (eqKapp na),
            qStE σ ((n : Nat) : Int) ((seed : Nat) : Int)
              ((k : Nat) : Int) (qslV B 0 i C) (qPre i seed)
              ((i : Nat) : Int) false
              (Heap.set tail (.base ⟨B⟩)
                (arrCellU C (qBack C (i + 1) seed))
              ++ [(.base ⟨na⟩,
                  u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
                (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
                (.base ⟨na + 2⟩,
                  u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
                (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
                (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
                (.base ⟨na + 5⟩,
                  arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
                (.base ⟨na + 6⟩, slCell (qslV B 0 (i + 1) C))])
              (na + 7), ch) :=
      stepFnIter_one (stepFn_stmtOp_apply
        (op := .appendSlice tU64) (nt := 1)
        (done := [qslV B 0 i C, .addr (.base ⟨na + 6⟩)])
        (v := qslV (na + 5) 0 1 1) (env := eqEnvC1 na) (k := eqKapp na)
        happly)
    have hdead2 : ∀ x : Nat, na ≤ x →
        Heap.lookup (Heap.set tail (.base ⟨B⟩)
          (arrCellU C (qBack C (i + 1) seed))) (.base ⟨x⟩) = none := by
      intro x hx
      rw [Machine.Heap.lookup_set_ne (by
        simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
        omega)]
      exact htail _ hx
    have hpost := qe_post σ ((n : Nat) : Int) ((seed : Nat) : Int)
      ((k : Nat) : Int) (qslV B 0 i C) (qslV B 0 (i + 1) C)
      (qPre i seed) i
      (Heap.set tail (.base ⟨B⟩) (arrCellU C (qBack C (i + 1) seed))
        ++ [(.base ⟨na⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
          (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩,
            arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
          (.base ⟨na + 6⟩, slCell (qslV B 0 (i + 1) C))])
      (na + 7) na ch (((seed + i) % 2 ^ 64 : Nat) : Int) h12
      (by
        rw [lookup_append_right (hdead2 _ (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ na + 3)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 3)),
          lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 3))]
        simp [Heap.lookup])
      (by
        rw [lookup_append_right (hdead2 _ (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ na + 6))]
        simp [Heap.lookup])
      (by
        rw [lookup_append_right (hdead2 _ (by omega))]
        simp [Heap.lookup])
      (by omega) (qPre_length (by omega)) qPre_range hwr
    have hrun := stepFnIter_chain (stepFnIter_chain hpre happstep) hpost
    rw [show (64 : Nat) + 1 + 65 = 130 from by omega, hnorm2] at hrun
    rw [qPre_set (by omega : i < 8)] at hrun
    rw [show Heap.set
        (Heap.set tail (.base ⟨B⟩) (arrCellU C (qBack C (i + 1) seed))
          ++ [(.base ⟨na⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
            (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (qslV B 0 (i + 1) C))])
        (.base ⟨na + 3⟩) (slCell (qslV B 0 (i + 1) C))
      = Heap.set tail (.base ⟨B⟩) (arrCellU C (qBack C (i + 1) seed))
          ++ [(.base ⟨na⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 i C)),
            (.base ⟨na + 2⟩, u64cell (((seed + i) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (qslV B 0 (i + 1) C)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + i) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (qslV B 0 (i + 1) C))] from by
      rw [set_append_right (hdead2 _ (by omega))]
      simp [Heap.set, base_beq_false (by omega : na ≠ na + 3),
        base_beq_false (by omega : na + 1 ≠ na + 3),
        base_beq_false (by omega : na + 2 ≠ na + 3)]] at hrun
    refine ⟨B, C, _, na + 7, ch, hrun, by omega,
      by omega, by omega, by omega, ?_, .inr ⟨hB12.1, ?_⟩⟩
    · intro x hx
      rw [lookup_append_right (hdead2 _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 6 ≠ x))]
      rfl
    · rw [lookup_append_left]
      exact Frame.Heap.lookup_set_self
  · -- SPILL: the backing is full (`i = C`); one choice is consumed.
    obtain rfl : C = i := by omega
    have happly : applyStmtOp
        (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
          (qslV B 0 C C) (qPre C seed) ((C : Nat) : Int) false
          (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
            (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7))
        ch (.appendSlice tU64) 1
        [.addr (.base ⟨na + 6⟩), qslV B 0 C C, qslV (na + 5) 0 1 1]
        = .ok (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int)
            ((k : Nat) : Int) (qslV B 0 C C) (qPre C seed)
            ((C : Nat) : Int) false
            (tail ++ [(.base ⟨na⟩,
                u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
              (.base ⟨na + 2⟩,
                u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (.base ⟨na + 5⟩,
                arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
              (.base ⟨na + 6⟩, slCell (qslV (na + 7) 0 (C + 1)
                (qSpillCap C
                  (ch.consume (appendSpillWidth C (C + 1))).1))),
              (.base ⟨na + 7⟩, arrCellU
                (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)
                (qBack (qSpillCap C
                    (ch.consume (appendSpillWidth C (C + 1))).1)
                  (C + 1) seed))]) (na + 8),
          (ch.consume (appendSpillWidth C (C + 1))).2) := by
      have h := qappend_spill
        (σ := σ) (na := na + 7)
        (H := qFront ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k : Nat) : Int) zeros8 zeros8 0 (qslV B 0 C C) (qPre C seed)
          ((C : Nat) : Int) false
          ++ (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
            (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
        (B := B) (bc := na + 5) (tc := na + 6) (C := C)
        (lq := qBack C C seed)
        (w := (((seed + C) % 2 ^ 64 : Nat) : Int))
        (old := .slice ⟨none, 0, 0, 0⟩) (ch := ch)
        hlkB hlkbc hlktc hHdead (qBack_length (Nat.le_refl C)) hrq hwr
      rw [qBack_spill_adv (qSpillCap_ge C
        (ch.consume (appendSpillWidth C (C + 1))).1)] at h
      rw [show Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int)
            ((k : Nat) : Int) zeros8 zeros8 0 (qslV B 0 C C) (qPre C seed)
            ((C : Nat) : Int) false
          ++ (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
            (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]))
          (.base ⟨na + 6⟩)
          ⟨some sliceU, qslV (na + 7) 0 (C + 1)
            (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)⟩
          ++ [(.base ⟨na + 7⟩,
            ⟨some (.array (qSpillCap C
                (ch.consume (appendSpillWidth C (C + 1))).1) tU64),
             .array ⟨(qBack (qSpillCap C
                  (ch.consume (appendSpillWidth C (C + 1))).1)
                (C + 1) seed).map (fun v => .int v .uint64)⟩⟩)]
        = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
            zeros8 zeros8 0 (qslV B 0 C C) (qPre C seed)
            ((C : Nat) : Int) false
          ++ (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
            (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (qslV (na + 7) 0 (C + 1)
              (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1))),
            (.base ⟨na + 7⟩, arrCellU
              (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)
              (qBack (qSpillCap C
                  (ch.consume (appendSpillWidth C (C + 1))).1)
                (C + 1) seed))]) from by
          rw [set_append_right (qFront_miss (by omega)),
            set_append_right (htail _ (by omega))]
          rw [show Heap.set [(Loc.base ⟨na⟩,
              u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (Loc.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
            (Loc.base ⟨na + 2⟩,
              u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (Loc.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (Loc.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (Loc.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
            (Loc.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]
            (.base ⟨na + 6⟩)
            ⟨some sliceU, qslV (na + 7) 0 (C + 1)
              (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)⟩
            = [(Loc.base ⟨na⟩,
                u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
              (Loc.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
              (Loc.base ⟨na + 2⟩,
                u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
              (Loc.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (Loc.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
              (Loc.base ⟨na + 5⟩,
                arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
              (Loc.base ⟨na + 6⟩, slCell (qslV (na + 7) 0 (C + 1)
                (qSpillCap C
                  (ch.consume (appendSpillWidth C (C + 1))).1)))] from by
            simp [Heap.set, base_beq_false (by omega : na ≠ na + 6),
              base_beq_false (by omega : na + 1 ≠ na + 6),
              base_beq_false (by omega : na + 2 ≠ na + 6),
              base_beq_false (by omega : na + 3 ≠ na + 6),
              base_beq_false (by omega : na + 4 ≠ na + 6),
              base_beq_false (by omega : na + 5 ≠ na + 6)]]
          simp [List.append_assoc]] at h
      exact h
    have happstep : stepFnIter 1
        (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
          (qslV B 0 C C) (qPre C seed) ((C : Nat) : Int) false
          (tail ++ [(.base ⟨na⟩,
              u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
            (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
            (.base ⟨na + 5⟩,
              arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
            (.base ⟨na + 6⟩, slCell (.slice ⟨none, 0, 0, 0⟩))]) (na + 7))
        (.retV (qslV (na + 5) 0 1 1) (eqAppK2 na (qslV B 0 C C))) ch
        = .ok (.next (eqKapp na),
            qStE σ ((n : Nat) : Int) ((seed : Nat) : Int)
              ((k : Nat) : Int) (qslV B 0 C C) (qPre C seed)
              ((C : Nat) : Int) false
              (tail ++ [(.base ⟨na⟩,
                  u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
                (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
                (.base ⟨na + 2⟩,
                  u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
                (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
                (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
                (.base ⟨na + 5⟩,
                  arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
                (.base ⟨na + 6⟩, slCell (qslV (na + 7) 0 (C + 1)
                  (qSpillCap C
                    (ch.consume (appendSpillWidth C (C + 1))).1))),
                (.base ⟨na + 7⟩, arrCellU
                  (qSpillCap C
                    (ch.consume (appendSpillWidth C (C + 1))).1)
                  (qBack (qSpillCap C
                      (ch.consume (appendSpillWidth C (C + 1))).1)
                    (C + 1) seed))]) (na + 8),
            (ch.consume (appendSpillWidth C (C + 1))).2) :=
      stepFnIter_one (stepFn_stmtOp_apply
        (op := .appendSlice tU64) (nt := 1)
        (done := [qslV B 0 C C, .addr (.base ⟨na + 6⟩)])
        (v := qslV (na + 5) 0 1 1) (env := eqEnvC1 na) (k := eqKapp na)
        happly)
    have hpost := qe_post σ ((n : Nat) : Int) ((seed : Nat) : Int)
      ((k : Nat) : Int) (qslV B 0 C C)
      (qslV (na + 7) 0 (C + 1)
        (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1))
      (qPre C seed) C
      (tail ++ [(.base ⟨na⟩,
          u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
        (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
        (.base ⟨na + 5⟩,
          arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
        (.base ⟨na + 6⟩, slCell (qslV (na + 7) 0 (C + 1)
          (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1))),
        (.base ⟨na + 7⟩, arrCellU
          (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)
          (qBack (qSpillCap C
              (ch.consume (appendSpillWidth C (C + 1))).1)
            (C + 1) seed))])
      (na + 8) na (ch.consume (appendSpillWidth C (C + 1))).2
      (((seed + C) % 2 ^ 64 : Nat) : Int) h12
      (by
        rw [lookup_append_right (htail _ (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ na + 3)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 3)),
          lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 3))]
        simp [Heap.lookup])
      (by
        rw [lookup_append_right (htail _ (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 6)),
          lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ na + 6))]
        simp [Heap.lookup])
      (by
        rw [lookup_append_right (htail _ (by omega))]
        simp [Heap.lookup])
      (by omega) (qPre_length (by omega)) qPre_range hwr
    have hrun := stepFnIter_chain (stepFnIter_chain hpre happstep) hpost
    rw [show (64 : Nat) + 1 + 65 = 130 from by omega, hnorm2] at hrun
    rw [qPre_set (by omega : C < 8)] at hrun
    rw [show Heap.set
        (tail ++ [(.base ⟨na⟩,
            u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
          (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 3⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩,
            arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
          (.base ⟨na + 6⟩, slCell (qslV (na + 7) 0 (C + 1)
            (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1))),
          (.base ⟨na + 7⟩, arrCellU
            (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)
            (qBack (qSpillCap C
                (ch.consume (appendSpillWidth C (C + 1))).1)
              (C + 1) seed))])
        (.base ⟨na + 3⟩)
        (slCell (qslV (na + 7) 0 (C + 1)
          (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)))
      = tail ++ [(.base ⟨na⟩,
            u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B 0 C C)),
          (.base ⟨na + 2⟩, u64cell (((seed + C) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 3⟩, slCell (qslV (na + 7) 0 (C + 1)
            (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1))),
          (.base ⟨na + 4⟩, slCell (qslV (na + 5) 0 1 1)),
          (.base ⟨na + 5⟩,
            arrCellU 1 [(((seed + C) % 2 ^ 64 : Nat) : Int)]),
          (.base ⟨na + 6⟩, slCell (qslV (na + 7) 0 (C + 1)
            (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1))),
          (.base ⟨na + 7⟩, arrCellU
            (qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1)
            (qBack (qSpillCap C
                (ch.consume (appendSpillWidth C (C + 1))).1)
              (C + 1) seed))] from by
      rw [set_append_right (htail _ (by omega))]
      simp [Heap.set, base_beq_false (by omega : na ≠ na + 3),
        base_beq_false (by omega : na + 1 ≠ na + 3),
        base_beq_false (by omega : na + 2 ≠ na + 3)]] at hrun
    refine ⟨na + 7,
      qSpillCap C (ch.consume (appendSpillWidth C (C + 1))).1, _, na + 8,
      (ch.consume (appendSpillWidth C (C + 1))).2, hrun, by omega,
      ?_, by omega, by omega, ?_, .inr ⟨by omega, ?_⟩⟩
    · exact qSpillCap_ge C _
    · intro x hx
      rw [lookup_append_right (htail _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 6 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : na + 7 ≠ x))]
      rfl
    · rw [lookup_append_right (htail _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na ≠ na + 7)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 7)),
        lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 7)),
        lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ na + 7)),
        lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ na + 7)),
        lookup_cons_ne (base_beq_false (by omega : na + 5 ≠ na + 7)),
        lookup_cons_ne (base_beq_false (by omega : na + 6 ≠ na + 7))]
      simp [Heap.lookup]

/-! ## The dequeue-phase environments and continuations

Everything below `d`'s cell lives at SYMBOLIC addresses (`D` is the
`nextAddr` the enqueue phase exits with), so every splice/read/store at
these environments is a conditioned or kit-glued step. -/

def dScope (D : Nat) : Scope := ("d", .base ⟨D⟩) :: hScope
def dEnv (D : Nat) : LocalEnv := [dScope D, baseScope]
def dqScope (D : Nat) : Scope := ("dequeued", .base ⟨D + 1⟩) :: dScope D
def qdEnv (D : Nat) : LocalEnv :=
  [[("$forFirst", .base ⟨D + 3⟩)], [("i", .base ⟨D + 2⟩)], dqScope D,
   baseScope]
def qdEnv1 (D : Nat) : LocalEnv := [] :: qdEnv D
def qdEnv2 (D : Nat) : LocalEnv := [] :: qdEnv1 D
def qdEnvV (D a : Nat) : LocalEnv := [("v", .base ⟨a⟩)] :: qdEnv1 D

/-- The `dequeue` callee frame scope. -/
def dqcScope (a : Nat) : Scope :=
  [("$res1", .base ⟨a + 3⟩), ("$res0", .base ⟨a + 2⟩), ("q", .base ⟨a + 1⟩)]
def dqcEnv (a : Nat) : LocalEnv := [dqcScope a]
def dqcEnvV (a : Nat) : LocalEnv := [("v", .base ⟨a + 4⟩)] :: dqcEnv a

def qXtail (D : Nat) : Cont :=
  .seq [qT6, qT7, qT8, qT9, qT10] (dEnv D) qStop
def qXifK (D : Nat) : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "d") (.var "n")]]) (.seqn #[])
    (dEnv D) (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop)
def tailAfterDeq (D : Nat) : Cont :=
  .seq [qT9, qT10] [dqScope D, baseScope] qStop
def qdHeadTail (D : Nat) : Cont :=
  .seq [] (qdEnv D)
    (.seq [] [[("i", .base ⟨D + 2⟩)], dqScope D, baseScope]
      (tailAfterDeq D))
def qdHeadCfg (D : Nat) : Config :=
  .exec (.while (.boolLit true) qdBody) (qdEnv D) (qdHeadTail D)
def qdLoopK (D : Nat) : Cont :=
  .loop (.boolLit true) qdBody (qdEnv D) (qdHeadTail D)
def qdCmpK (D : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt (qdEnv1 D)
    (.seq [qdFill] (qdEnv1 D) (qdLoopK D))

def qdPlans : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "q"]), (.chain [], [.ref "v"])]
def qdAfterCallK (D a : Nat) : Cont :=
  .seq [qdStoreSeqn] (qdEnvV D a) (.seq [] (qdEnv1 D) (qdLoopK D))
def qdCallArgsK (D a : Nat) : Cont :=
  .callArgsK ⟨"dequeue"⟩ qdPlans [] [] (qdEnvV D a) (qdAfterCallK D a)
def qdFrameK (D a : Nat) : Cont :=
  .frame qdPlans (qdEnvV D a) [.base ⟨a + 2⟩, .base ⟨a + 3⟩] []
    (qdAfterCallK D a) false

/-- A declaration-free block pushes a fresh scope (no env `DecidableEq`
on this arm, so it holds at symbolic addresses). -/
theorem stepFn_block {σ : ExecState} {ss : Array Stmt} {env : LocalEnv}
    {k : Cont} {ch : Choices} :
    stepFn σ (.exec (.block #[] ss) env k) ch
      = .ok (.next (.seq ss.toList ([] :: env) k), σ, ch) := by
  simp only [stepFn]
  rfl

/-- Splice + pop in one: an `Expr`-free `seqn` under a same-env
sequence, landing on the first statement of the concatenation. -/
theorem stepFnIter_splice_pop {σ : ExecState} {ss : Array Stmt} {t : Stmt}
    {ts rest : List Stmt} {env : LocalEnv} {k : Cont} {ch : Choices}
    (hs : ss.toList ++ rest = t :: ts) :
    stepFnIter 2 σ (.exec (.seqn ss) env (.seq rest env k)) ch
      = .ok (.exec t env (.seq ts env k), σ, ch) := by
  have h1 := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := ss)
    (env := env) (rest := rest) (k := k) (ch := ch))
  rw [hs] at h1
  exact stepFnIter_chain h1 (stepFnIter_one stepFn_seq_pop)

/-- Store-drain glue: a drained store whose body is the empty `seqn`
under a same-env sequence — three steps to the next statement. -/
theorem stepFnIter_drain3 {σ : ExecState} {t : Stmt} {ts : List Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices} :
    stepFnIter 3 σ
      (.next (.storeK [] [] (.seqn #[]) env (.seq (t :: ts) env k))) ch
      = .ok (.exec t env (.seq ts env k), σ, ch) :=
  stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
    (stepFnIter_splice_pop (ss := #[]) rfl)

/-- Block push + pop in one: a declaration-free block with a nonempty
statement list. -/
theorem stepFnIter_block_pop {σ : ExecState} {ss : Array Stmt} {t : Stmt}
    {ts : List Stmt} {env : LocalEnv} {k : Cont} {ch : Choices}
    (hs : ss.toList = t :: ts) :
    stepFnIter 2 σ (.exec (.block #[] ss) env k) ch
      = .ok (.exec t ([] :: env) (.seq ts ([] :: env) k), σ, ch) := by
  have h1 := stepFnIter_one (stepFn_block (σ := σ) (ss := ss) (env := env)
    (k := k) (ch := ch))
  rw [hs] at h1
  exact stepFnIter_chain h1 (stepFnIter_one stepFn_seq_pop)

/-- Bool cells never renormalize (the normalizer's catch-all arm). -/
theorem normVal_bool (σ : ExecState) (b : Bool) :
    normalizeValueForTy σ .bool (.bool b) = .ok (.bool b) := by
  with_unfolding_all rfl

/-- The `dequeue` callee's two statement pieces. -/
def dqSeqnA : Stmt :=
  .seqn #[.initialization { id := "v", typ := tU64 },
          .assign (.var "v")
            (.indexGet (.var "q") (.intLit 0 .int))]
def dqSeqnB : Stmt :=
  .seqn #[.assign (.var "$res0")
            (.slice (.var "q") (.intLit 1 .int)
              (.length (.var "q") (some sliceU)) none),
          .assign (.var "$res1") (.var "v"),
          .returnStmt]

/-! ## The min-branch (`d := k; if n < k { d = n }`) and the dequeue
loop's declarations — from the enqueue exit test to the dequeue head.
The `if` costs 12 extra steps on the TRUE (`n < k`) branch; both
branches land `d = min k n`. -/

/-- Enqueue exit: test false → break drain → the `d` initialization.
9 steps (concrete environments). -/
theorem qx_S1_raw (σ : ExecState) (ch : Choices) :
    stepFnIter 9 σ (.retV (.bool false) qeCmpK) ch
      = .ok (.exec (.initialization { id := "d", typ := tU64 })
          [hScope, baseScope]
          (.seq [.assign (.var "d") (.var "k"), qT6, qT7, qT8, qT9, qT10]
            [hScope, baseScope] qStop), σ, ch) := by
  with_unfolding_all rfl

/-- `d := k` evaluation: 6 steps to the store point. -/
theorem qx_S2_raw (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na D : Nat) (ch : Choices) :
    stepFnIter 6 (qStE σ nv sv kv qv lE iv false tail na)
      (.next (.seq [.assign (.var "d") (.var "k"), qT6, qT7, qT8, qT9,
        qT10] (dEnv D) qStop)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨D⟩)) [] []]
            [.int kv .uint64] (.seqn #[]) (dEnv D) (qXtail D)),
          qStE σ nv sv kv qv lE iv false tail na, ch) := by
  with_unfolding_all rfl

/-- `n < k` test evaluation: 6 steps from the popped `qT6`. -/
theorem qx_S3_raw (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (iv : Int) (tail : Heap) (na D : Nat) (ch : Choices) :
    stepFnIter 6 (qStE σ nv sv kv qv lE iv false tail na)
      (.exec qT6 (dEnv D)
        (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop)) ch
      = .ok (.retV (.bool (decide (nv < kv))) (qXifK D),
          qStE σ nv sv kv qv lE iv false tail na, ch) := by
  with_unfolding_all rfl

/-- From the enqueue exit test (FALSE) to the dequeue loop's head:
61 steps when `k ≤ n` (the `if` takes its empty else), 73 when
`n < k` (the `d = n` overwrite runs). Both land `d = min k n` and the
four dequeue-loop cells at `D..D+3`. -/
theorem qx_toHead (σ : ExecState) (n seed' k : Nat) (sv : Int)
    (qv : GoValue) (lE : List Int) (iv : Int) (tail : Heap) (D : Nat)
    (ch : Choices)
    (h12 : 12 ≤ D) (htail : DeadFrom tail D)
    (hn8 : n ≤ 8) (hk : k < 2 ^ 64) :
    stepFnIter (if n < k then 73 else 61)
      (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        tail D)
      (.retV (.bool false) qeCmpK) ch
      = .ok (qdHeadCfg D,
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((min k n : Nat) : Int)),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0),
              (.base ⟨D + 3⟩, bcell true)]) (D + 4), ch) := by
  -- shared prefix: break drain + `d := k`
  have h1 := qx_S1_raw
    (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false tail D)
    ch
  have h2 : stepFnIter 1
      (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        tail D)
      (.exec (.initialization { id := "d", typ := tU64 })
        [hScope, baseScope]
        (.seq [.assign (.var "d") (.var "k"), qT6, qT7, qT8, qT9, qT10]
          [hScope, baseScope] qStop)) ch
      = .ok (.next (.seq [.assign (.var "d") (.var "k"), qT6, qT7, qT8,
            qT9, qT10] (dEnv D) qStop),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell 0)]) (D + 1), ch) := by
    have h := stepFnIter_one (stepFn_init_seq
      (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        tail D)
      (p := { id := "d", typ := tU64 })
      (rest := [.assign (.var "d") (.var "k"), qT6, qT7, qT8, qT9, qT10])
      (env := [hScope, baseScope]) (k := qStop) (ch := ch)
      (hdef := by with_unfolding_all rfl))
    rw [show LocalEnv.declare [hScope, baseScope] "d"
        (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false tail D).nextAddr⟩) = dEnv D from rfl] at h
    rw [show Heap.set (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv
        lE iv false tail D).heap
        (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false tail D).nextAddr⟩)
        ⟨some tU64, .int 0 .uint64⟩
      = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv
          lE iv false ++ (tail ++ [(.base ⟨D⟩, u64cell 0)]) from by
        rw [show (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false tail D).heap
          = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0
              qv lE iv false ++ tail from rfl,
          set_fresh ((qHeap_dead h12 htail) _ (Nat.le_refl _)),
          List.append_assoc]] at h
    exact h
  have h3 := qx_S2_raw σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
    (tail ++ [(.base ⟨D⟩, u64cell 0)]) (D + 1) D ch
  have hlkD : Heap.lookup
      ((qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell 0)]) (D + 1)).heap) (.base ⟨D⟩)
      = some (u64cell 0) := by
    show Heap.lookup (qFront ((n : Nat) : Int) sv ((k : Nat) : Int)
        zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨D⟩, u64cell 0)])) (.base ⟨D⟩)
      = some (u64cell 0)
    rw [lookup_append_right (qFront_miss h12),
      lookup_append_right (htail _ (Nat.le_refl _))]
    exact lookup_singleton_self
  have hstD : storeTarget
      (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell 0)]) (D + 1))
      (.chain (.addr (.base ⟨D⟩)) [] []) (.int ((k : Nat) : Int) .uint64)
      = .ok (qSt σ (Heap.set (qFront ((n : Nat) : Int) sv
          ((k : Nat) : Int) zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨D⟩, u64cell 0)])) (.base ⟨D⟩)
          ⟨some tU64, .int ((k : Nat) : Int) .uint64⟩) (D + 1)) :=
    storeTarget_addr hlkD (normVal_u64 _ (by omega) (by exact_mod_cast hk))
  rw [show Heap.set (qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8
      zeros8 0 qv lE iv false ++ (tail ++ [(.base ⟨D⟩, u64cell 0)]))
      (.base ⟨D⟩) ⟨some tU64, .int ((k : Nat) : Int) .uint64⟩
    = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv lE
        iv false ++ (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))])
    from by
      rw [set_append_right (qFront_miss h12),
        set_append_right (htail _ (Nat.le_refl _)), set_singleton_self]]
    at hstD
  have h4 : stepFnIter 1
      (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell 0)]) (D + 1))
      (.next (.storeK [.chain (.addr (.base ⟨D⟩)) [] []]
        [.int ((k : Nat) : Int) .uint64] (.seqn #[]) (dEnv D)
        (qXtail D))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (dEnv D) (qXtail D)),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
          ch) :=
    stepFnIter_one (stepFn_store_step hstD)
  have h5 : stepFnIter 3
      (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
      (.next (.storeK [] [] (.seqn #[]) (dEnv D) (qXtail D))) ch
      = .ok (.exec qT6 (dEnv D)
          (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop),
        qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
        ch) := by
    have ha := stepFnIter_one (stepFn_storeK_nil
      (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
      (body := .seqn #[]) (env := dEnv D) (k := qXtail D) (ch := ch))
    have hb : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.exec (.seqn #[]) (dEnv D) (qXtail D)) ch
        = .ok (.next (.seq [qT6, qT7, qT8, qT9, qT10] (dEnv D) qStop),
            qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
              (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
            ch) := by
      have := stepFnIter_one (stepFn_seqn_splice
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))])
          (D + 1))
        (ss := #[]) (env := dEnv D)
        (rest := [qT6, qT7, qT8, qT9, qT10]) (k := qStop) (ch := ch))
      simpa [qXtail] using this
    have hc := stepFnIter_one (stepFn_seq_pop
      (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
      (t := qT6) (rest := [qT7, qT8, qT9, qT10]) (env := dEnv D)
      (k := qStop) (ch := ch))
    exact stepFnIter_chain (stepFnIter_chain ha hb) hc
  have h6 := qx_S3_raw σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
    (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1) D ch
  have hcommon := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6
  -- the 30-step shared rest, from the `dequeued` initialization
  have hrest : ∀ (dv : Int),
      stepFnIter 30
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1))
        (.exec (.initialization { id := "dequeued", typ := .array 8 tU64 })
          (dEnv D) (.seq [qT8, qT9, qT10] (dEnv D) qStop)) ch
        = .ok (qdHeadCfg D,
            qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
              (tail ++ [(.base ⟨D⟩, u64cell dv),
                (.base ⟨D + 1⟩, arrCellU 8 zeros8),
                (.base ⟨D + 2⟩, u64cell 0),
                (.base ⟨D + 3⟩, bcell true)]) (D + 4), ch) := by
    intro dv
    have hd1 : DeadFrom (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1) :=
      htail.push
    have hd2 : DeadFrom (tail ++ [(.base ⟨D⟩, u64cell dv),
        (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2) :=
      htail.push2
    have hd3 : DeadFrom (tail ++ [(.base ⟨D⟩, u64cell dv),
        (.base ⟨D + 1⟩, arrCellU 8 zeros8),
        (.base ⟨D + 2⟩, u64cell 0)]) (D + 3) := by
      intro x hx
      rw [lookup_append_right (htail _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega : D ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ x)),
        lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ x))]
      rfl
    -- init dequeued (1)
    have g1 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1))
        (.exec (.initialization { id := "dequeued", typ := .array 8 tU64 })
          (dEnv D) (.seq [qT8, qT9, qT10] (dEnv D) qStop)) ch
        = .ok (.next (.seq [qT8, qT9, qT10] [dqScope D, baseScope] qStop),
            qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
              (tail ++ [(.base ⟨D⟩, u64cell dv),
                (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2), ch) := by
      have h := stepFnIter_one (stepFn_init_seq
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1))
        (p := { id := "dequeued", typ := .array 8 tU64 })
        (rest := [qT8, qT9, qT10]) (env := dEnv D) (k := qStop) (ch := ch)
        (hdef := show defaultValue _ (.array 8 tU64)
          = .ok (.array ⟨zeros8.map (fun v => .int v .uint64)⟩) from by
          with_unfolding_all rfl))
      rw [show LocalEnv.declare (dEnv D) "dequeued"
          (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1)).nextAddr⟩)
        = [dqScope D, baseScope] from rfl] at h
      rw [show Heap.set (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv
          lE iv false (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1)).heap
          (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1)).nextAddr⟩)
          ⟨some (.array 8 tU64),
           .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩
        = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv
            lE iv false
            ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) from by
          rw [show (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
              false (tail ++ [(.base ⟨D⟩, u64cell dv)]) (D + 1)).heap
            = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8
                0 qv lE iv false ++ (tail ++ [(.base ⟨D⟩, u64cell dv)])
              from rfl,
            set_fresh ((qHeap_dead (by omega) hd1) _ (Nat.le_refl _))]
          simp [List.append_assoc]] at h
      exact h
    -- pop qT8 (1) + block push/pop (2) + splice/pop (2) → init i
    have g2a := stepFnIter_one (stepFn_seq_pop
      (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell dv),
          (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2))
      (t := qT8) (rest := [qT9, qT10]) (env := [dqScope D, baseScope])
      (k := qStop) (ch := ch))
    have g2b : stepFnIter 2
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2))
        (.exec qT8 [dqScope D, baseScope]
          (.seq [qT9, qT10] [dqScope D, baseScope] qStop)) ch
        = .ok (.exec (.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)])
            ([] :: [dqScope D, baseScope])
            (.seq [.block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) qdBody]]
              ([] :: [dqScope D, baseScope]) (tailAfterDeq D)),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2), ch) := by
      have := stepFnIter_block_pop
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2))
        (ss := #[.seqn #[.initialization { id := "i", typ := tU64 },
            .assign (.var "i") (.intLit 0 .uint64)],
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) qdBody]])
        (env := [dqScope D, baseScope]) (k := tailAfterDeq D) (ch := ch)
        rfl
      simpa [qT8, tailAfterDeq] using this
    have g2c : stepFnIter 2
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2))
        (.exec (.seqn #[.initialization { id := "i", typ := tU64 },
            .assign (.var "i") (.intLit 0 .uint64)])
          ([] :: [dqScope D, baseScope])
          (.seq [.block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) qdBody]]
            ([] :: [dqScope D, baseScope]) (tailAfterDeq D))) ch
        = .ok (.exec (.initialization { id := "i", typ := tU64 })
            ([] :: [dqScope D, baseScope])
            (.seq [.assign (.var "i") (.intLit 0 .uint64),
              .block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) qdBody]]
              ([] :: [dqScope D, baseScope]) (tailAfterDeq D)),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2), ch) :=
      stepFnIter_splice_pop rfl
    -- init i (1)
    have g3 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2))
        (.exec (.initialization { id := "i", typ := tU64 })
          ([] :: [dqScope D, baseScope])
          (.seq [.assign (.var "i") (.intLit 0 .uint64),
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) qdBody]]
            ([] :: [dqScope D, baseScope]) (tailAfterDeq D))) ch
        = .ok (.next (.seq [.assign (.var "i") (.intLit 0 .uint64),
              .block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) qdBody]]
              ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
              (tailAfterDeq D)),
            qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
              (tail ++ [(.base ⟨D⟩, u64cell dv),
                (.base ⟨D + 1⟩, arrCellU 8 zeros8),
                (.base ⟨D + 2⟩, u64cell 0)]) (D + 3), ch) := by
      have h := stepFnIter_one (stepFn_init_seq
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2))
        (p := { id := "i", typ := tU64 })
        (rest := [.assign (.var "i") (.intLit 0 .uint64),
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) qdBody]])
        (env := [] :: [dqScope D, baseScope]) (k := tailAfterDeq D)
        (ch := ch) (hdef := by with_unfolding_all rfl))
      rw [show LocalEnv.declare ([] :: [dqScope D, baseScope]) "i"
          (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2)).nextAddr⟩)
        = [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope] from rfl] at h
      rw [show Heap.set (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv
          lE iv false (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2)).heap
          (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2)).nextAddr⟩)
          ⟨some tU64, .int 0 .uint64⟩
        = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv
            lE iv false
            ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0)]) from by
          rw [show (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
              false (tail ++ [(.base ⟨D⟩, u64cell dv),
                (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) (D + 2)).heap
            = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8
                0 qv lE iv false ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
                  (.base ⟨D + 1⟩, arrCellU 8 zeros8)]) from rfl,
            set_fresh ((qHeap_dead (by omega) hd2) _ (Nat.le_refl _))]
          simp [List.append_assoc]] at h
      exact h
    -- i := 0 (pop + 5 evals + rhs → storeK) (6)
    have g4 : stepFnIter 6
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3))
        (.next (.seq [.assign (.var "i") (.intLit 0 .uint64),
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) qdBody]]
          ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
          (tailAfterDeq D))) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨D + 2⟩)) [] []]
            [.int 0 .uint64] (.seqn #[])
            ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
            (.seq [.block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) qdBody]]
              ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
              (tailAfterDeq D))),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0)]) (D + 3), ch) := by
      with_unfolding_all rfl
    -- store i (1)
    have hlkI : Heap.lookup
        ((qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3)).heap) (.base ⟨D + 2⟩)
        = some (u64cell 0) := by
      show Heap.lookup (qFront ((n : Nat) : Int) sv ((k : Nat) : Int)
          zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)])) (.base ⟨D + 2⟩)
        = some (u64cell 0)
      rw [lookup_append_right (qFront_miss (by omega)),
        lookup_append_right (htail _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 2)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 2))]
      simp [Heap.lookup]
    have hstI : storeTarget
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3))
        (.chain (.addr (.base ⟨D + 2⟩)) [] []) (.int 0 .uint64)
        = .ok (qSt σ (Heap.set (qFront ((n : Nat) : Int) sv
            ((k : Nat) : Int) zeros8 zeros8 0 qv lE iv false
            ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0)])) (.base ⟨D + 2⟩)
            ⟨some tU64, .int 0 .uint64⟩) (D + 3)) :=
      storeTarget_addr hlkI (normVal_u64 _ (by omega) (by omega))
    rw [show Heap.set (qFront ((n : Nat) : Int) sv ((k : Nat) : Int)
        zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
          (.base ⟨D + 1⟩, arrCellU 8 zeros8),
          (.base ⟨D + 2⟩, u64cell 0)])) (.base ⟨D + 2⟩)
        ⟨some tU64, .int 0 .uint64⟩
      = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv
          lE iv false ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) from by
        rw [set_append_right (qFront_miss (by omega)),
          set_append_right (htail _ (by omega))]
        simp [Heap.set, base_beq_false (by omega : D ≠ D + 2),
          base_beq_false (by omega : D + 1 ≠ D + 2)]] at hstI
    have g5 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3))
        (.next (.storeK [.chain (.addr (.base ⟨D + 2⟩)) [] []]
          [.int 0 .uint64] (.seqn #[])
          ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
          (.seq [.block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) qdBody]]
            ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
            (tailAfterDeq D)))) ch
        = .ok (.next (.storeK [] [] (.seqn #[])
            ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
            (.seq [.block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) qdBody]]
              ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
              (tailAfterDeq D))),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0)]) (D + 3), ch) :=
      stepFnIter_one (stepFn_store_step hstI)
    -- drain (3) + block-ff push/pop (2) → init $forFirst
    have g6 := stepFnIter_drain3
      (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell dv),
          (.base ⟨D + 1⟩, arrCellU 8 zeros8),
          (.base ⟨D + 2⟩, u64cell 0)]) (D + 3))
      (t := .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) qdBody])
      (ts := []) (env := [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
      (k := tailAfterDeq D) (ch := ch)
    have g7 : stepFnIter 2
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3))
        (.exec (.block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) qdBody])
          ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
          (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
            (tailAfterDeq D))) ch
        = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
            ([] :: [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
            (.seq [.assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) qdBody]
              ([] :: [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
              (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
                (tailAfterDeq D))), 
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0)]) (D + 3), ch) :=
      stepFnIter_block_pop rfl
    -- init $forFirst (1)
    have g8 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3))
        (.exec (.initialization { id := "$forFirst", typ := .bool })
          ([] :: [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
          (.seq [.assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) qdBody]
            ([] :: [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
            (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
              (tailAfterDeq D)))) ch
        = .ok (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) qdBody] (qdEnv D)
              (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
                (tailAfterDeq D))),
            qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
              (tail ++ [(.base ⟨D⟩, u64cell dv),
                (.base ⟨D + 1⟩, arrCellU 8 zeros8),
                (.base ⟨D + 2⟩, u64cell 0),
                (.base ⟨D + 3⟩, bcell false)]) (D + 4), ch) := by
      have h := stepFnIter_one (stepFn_init_seq
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3))
        (p := { id := "$forFirst", typ := .bool })
        (rest := [.assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) qdBody])
        (env := [] :: [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
        (k := .seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
          (tailAfterDeq D))
        (ch := ch) (hdef := by with_unfolding_all rfl))
      rw [show LocalEnv.declare
          ([] :: [("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
          "$forFirst"
          (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0)]) (D + 3)).nextAddr⟩)
        = qdEnv D from rfl] at h
      rw [show Heap.set (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv
          lE iv false (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0)]) (D + 3)).heap
          (.base ⟨(qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0)]) (D + 3)).nextAddr⟩)
          ⟨some .bool, .bool false⟩
        = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv
            lE iv false
            ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0),
              (.base ⟨D + 3⟩, bcell false)]) from by
          rw [show (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
              false (tail ++ [(.base ⟨D⟩, u64cell dv),
                (.base ⟨D + 1⟩, arrCellU 8 zeros8),
                (.base ⟨D + 2⟩, u64cell 0)]) (D + 3)).heap
            = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8
                0 qv lE iv false ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
                  (.base ⟨D + 1⟩, arrCellU 8 zeros8),
                  (.base ⟨D + 2⟩, u64cell 0)]) from rfl,
            set_fresh ((qHeap_dead (by omega) hd3) _ (Nat.le_refl _))]
          simp [List.append_assoc]] at h
      exact h
    -- $forFirst := true (5 evals + rhs) (6)
    have g9 : stepFnIter 6
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell false)]) (D + 4))
        (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) qdBody] (qdEnv D)
          (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
            (tailAfterDeq D)))) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨D + 3⟩)) [] []]
            [.bool true] (.seqn #[]) (qdEnv D)
            (.seq [.while (.boolLit true) qdBody] (qdEnv D)
              (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
                (tailAfterDeq D)))),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0),
              (.base ⟨D + 3⟩, bcell false)]) (D + 4), ch) := by
      with_unfolding_all rfl
    -- store $forFirst (1)
    have hlkF : Heap.lookup
        ((qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell false)]) (D + 4)).heap) (.base ⟨D + 3⟩)
        = some (bcell false) := by
      show Heap.lookup (qFront ((n : Nat) : Int) sv ((k : Nat) : Int)
          zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell false)])) (.base ⟨D + 3⟩)
        = some (bcell false)
      rw [lookup_append_right (qFront_miss (by omega)),
        lookup_append_right (htail _ (by omega)),
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 3)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 3)),
        lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ D + 3))]
      simp [Heap.lookup]
    have hstF : storeTarget
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell false)]) (D + 4))
        (.chain (.addr (.base ⟨D + 3⟩)) [] []) (.bool true)
        = .ok (qSt σ (Heap.set (qFront ((n : Nat) : Int) sv
            ((k : Nat) : Int) zeros8 zeros8 0 qv lE iv false
            ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0),
              (.base ⟨D + 3⟩, bcell false)])) (.base ⟨D + 3⟩)
            ⟨some .bool, .bool true⟩) (D + 4)) :=
      storeTarget_addr hlkF (normVal_bool _ true)
    rw [show Heap.set (qFront ((n : Nat) : Int) sv ((k : Nat) : Int)
        zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
          (.base ⟨D + 1⟩, arrCellU 8 zeros8),
          (.base ⟨D + 2⟩, u64cell 0),
          (.base ⟨D + 3⟩, bcell false)])) (.base ⟨D + 3⟩)
        ⟨some .bool, .bool true⟩
      = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv
          lE iv false ++ (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell true)]) from by
        rw [set_append_right (qFront_miss (by omega)),
          set_append_right (htail _ (by omega))]
        simp [Heap.set, base_beq_false (by omega : D ≠ D + 3),
          base_beq_false (by omega : D + 1 ≠ D + 3),
          base_beq_false (by omega : D + 2 ≠ D + 3)]] at hstF
    have g10 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell false)]) (D + 4))
        (.next (.storeK [.chain (.addr (.base ⟨D + 3⟩)) [] []]
          [.bool true] (.seqn #[]) (qdEnv D)
          (.seq [.while (.boolLit true) qdBody] (qdEnv D)
            (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
              (tailAfterDeq D))))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (qdEnv D)
            (.seq [.while (.boolLit true) qdBody] (qdEnv D)
              (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
                (tailAfterDeq D)))),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0),
              (.base ⟨D + 3⟩, bcell true)]) (D + 4), ch) :=
      stepFnIter_one (stepFn_store_step hstF)
    -- drain (3) → the head
    have g11 : stepFnIter 3
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell true)]) (D + 4))
        (.next (.storeK [] [] (.seqn #[]) (qdEnv D)
          (.seq [.while (.boolLit true) qdBody] (qdEnv D)
            (.seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
              (tailAfterDeq D))))) ch
        = .ok (qdHeadCfg D,
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell dv),
              (.base ⟨D + 1⟩, arrCellU 8 zeros8),
              (.base ⟨D + 2⟩, u64cell 0),
              (.base ⟨D + 3⟩, bcell true)]) (D + 4), ch) := by
      have := stepFnIter_drain3
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell dv),
            (.base ⟨D + 1⟩, arrCellU 8 zeros8),
            (.base ⟨D + 2⟩, u64cell 0),
            (.base ⟨D + 3⟩, bcell true)]) (D + 4))
        (t := .while (.boolLit true) qdBody) (ts := []) (env := qdEnv D)
        (k := .seq [] ([("i", .base ⟨D + 2⟩)] :: [dqScope D, baseScope])
          (tailAfterDeq D)) (ch := ch)
      simpa [qdHeadCfg, qdHeadTail] using this
    have := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain g1 g2a)
            g2b) g2c) g3) g4) g5) g6) g7) g8) g9) g10) g11
    rw [show (1 : Nat) + 1 + 2 + 2 + 1 + 6 + 1 + 3 + 2 + 1 + 6 + 1 + 3
        = 30 from by omega] at this
    exact this
  by_cases hnk : n < k
  · -- TRUE: `d = n` overwrites (12 extra steps)
    rw [if_pos hnk]
    rw [show (decide (((n : Nat) : Int) < ((k : Nat) : Int))) = true from
      decide_eq_true (by exact_mod_cast hnk)] at hcommon
    have t1 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.retV (.bool true) (qXifK D)) ch
        = .ok (.exec (.block #[] #[.seqn #[.assign (.var "d") (.var "n")]])
            (dEnv D) (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
          ch) := by
      with_unfolding_all rfl
    have t2 := stepFnIter_block_pop
      (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
      (ss := #[.seqn #[.assign (.var "d") (.var "n")]])
      (env := dEnv D) (k := .seq [qT7, qT8, qT9, qT10] (dEnv D) qStop)
      (ch := ch) rfl
    have t3 := stepFnIter_splice_pop
      (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
        (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
      (ss := #[.assign (.var "d") (.var "n")]) (t := .assign (.var "d") (.var "n"))
      (ts := []) (rest := []) (env := [] :: dEnv D)
      (k := .seq [qT7, qT8, qT9, qT10] (dEnv D) qStop) (ch := ch) rfl
    have t4 : stepFnIter 5
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.exec (.assign (.var "d") (.var "n")) ([] :: dEnv D)
          (.seq [] ([] :: dEnv D)
            (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop))) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨D⟩)) [] []]
            [.int ((n : Nat) : Int) .uint64] (.seqn #[]) ([] :: dEnv D)
            (.seq [] ([] :: dEnv D)
              (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop))),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
          ch) := by
      with_unfolding_all rfl
    have hlkD2 : Heap.lookup
        ((qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))])
          (D + 1)).heap) (.base ⟨D⟩)
        = some (u64cell ((k : Nat) : Int)) := by
      show Heap.lookup (qFront ((n : Nat) : Int) sv ((k : Nat) : Int)
          zeros8 zeros8 0 qv lE iv false
          ++ (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]))
          (.base ⟨D⟩)
        = some (u64cell ((k : Nat) : Int))
      rw [lookup_append_right (qFront_miss h12),
        lookup_append_right (htail _ (Nat.le_refl _))]
      exact lookup_singleton_self
    have hstD2 : storeTarget
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.chain (.addr (.base ⟨D⟩)) [] [])
        (.int ((n : Nat) : Int) .uint64)
        = .ok (qSt σ (Heap.set (qFront ((n : Nat) : Int) sv
            ((k : Nat) : Int) zeros8 zeros8 0 qv lE iv false
            ++ (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]))
            (.base ⟨D⟩) ⟨some tU64, .int ((n : Nat) : Int) .uint64⟩)
          (D + 1)) :=
      storeTarget_addr hlkD2 (normVal_u64 _ (by omega) (by
        have : (n : Int) < 2 ^ 64 := by exact_mod_cast
          (by omega : n < 2 ^ 64)
        exact this))
    rw [show Heap.set (qFront ((n : Nat) : Int) sv ((k : Nat) : Int)
        zeros8 zeros8 0 qv lE iv false
        ++ (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]))
        (.base ⟨D⟩) ⟨some tU64, .int ((n : Nat) : Int) .uint64⟩
      = qFront ((n : Nat) : Int) sv ((k : Nat) : Int) zeros8 zeros8 0 qv
          lE iv false
          ++ (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))]) from by
        rw [set_append_right (qFront_miss h12),
          set_append_right (htail _ (Nat.le_refl _)), set_singleton_self]]
      at hstD2
    have t5 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.next (.storeK [.chain (.addr (.base ⟨D⟩)) [] []]
          [.int ((n : Nat) : Int) .uint64] (.seqn #[]) ([] :: dEnv D)
          (.seq [] ([] :: dEnv D)
            (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop)))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: dEnv D)
            (.seq [] ([] :: dEnv D)
              (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop))),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))]) (D + 1),
          ch) :=
      stepFnIter_one (stepFn_store_step hstD2)
    have t6 : stepFnIter 6
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))]) (D + 1))
        (.next (.storeK [] [] (.seqn #[]) ([] :: dEnv D)
          (.seq [] ([] :: dEnv D)
            (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop)))) ch
        = .ok (.exec (.initialization
              { id := "dequeued", typ := .array 8 tU64 }) (dEnv D)
            (.seq [qT8, qT9, qT10] (dEnv D) qStop),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))]) (D + 1),
          ch) := by
      have a1 := stepFnIter_one (stepFn_storeK_nil
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))])
          (D + 1))
        (body := .seqn #[]) (env := [] :: dEnv D)
        (k := .seq [] ([] :: dEnv D)
          (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop)) (ch := ch))
      have a2 := stepFnIter_one (stepFn_seqn_splice
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))])
          (D + 1))
        (ss := #[]) (env := [] :: dEnv D) (rest := [])
        (k := .seq [qT7, qT8, qT9, qT10] (dEnv D) qStop) (ch := ch))
      have a3 := stepFnIter_one (stepFn_seq_nil
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))])
          (D + 1))
        (env := [] :: dEnv D)
        (k := .seq [qT7, qT8, qT9, qT10] (dEnv D) qStop) (ch := ch))
      have a4 := stepFnIter_one (stepFn_seq_pop
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))])
          (D + 1))
        (t := qT7) (rest := [qT8, qT9, qT10]) (env := dEnv D)
        (k := qStop) (ch := ch))
      have a5 : stepFnIter 2
          (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))]) (D + 1))
          (.exec qT7 (dEnv D) (.seq [qT8, qT9, qT10] (dEnv D) qStop)) ch
          = .ok (.exec (.initialization
                { id := "dequeued", typ := .array 8 tU64 }) (dEnv D)
              (.seq [qT8, qT9, qT10] (dEnv D) qStop),
            qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
              (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))]) (D + 1),
            ch) := by
        have := stepFnIter_splice_pop
          (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
            false (tail ++ [(.base ⟨D⟩, u64cell ((n : Nat) : Int))])
            (D + 1))
          (ss := #[.initialization { id := "dequeued", typ := .array 8 tU64 }])
          (t := .initialization { id := "dequeued", typ := .array 8 tU64 })
          (ts := [qT8, qT9, qT10]) (rest := [qT8, qT9, qT10])
          (env := dEnv D) (k := qStop) (ch := ch) rfl
        simpa [qT7] using this
      exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain a1 a2) a3) a4) a5
    have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain hcommon t1) t2) t3) t4) t5) t6)
      (hrest ((n : Nat) : Int))
    rw [show (9 : Nat) + 1 + 6 + 1 + 3 + 6 + 1 + 2 + 2 + 5 + 1 + 6 + 30
        = 73 from by omega] at hall
    rw [show ((min k n : Nat) : Int) = ((n : Nat) : Int) from by
      rw [Nat.min_eq_right (by omega)]]
    exact hall
  · -- FALSE: empty else
    rw [if_neg hnk]
    rw [show (decide (((n : Nat) : Int) < ((k : Nat) : Int))) = false from
      decide_eq_false (by
        intro hc
        exact hnk (by exact_mod_cast hc))] at hcommon
    have f1 : stepFnIter 1
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.retV (.bool false) (qXifK D)) ch
        = .ok (.exec (.seqn #[]) (dEnv D)
            (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
          ch) := by
      with_unfolding_all rfl
    have f2 : stepFnIter 2
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.exec (.seqn #[]) (dEnv D)
          (.seq [qT7, qT8, qT9, qT10] (dEnv D) qStop)) ch
        = .ok (.exec qT7 (dEnv D)
            (.seq [qT8, qT9, qT10] (dEnv D) qStop),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
          ch) :=
      stepFnIter_splice_pop (ss := #[]) rfl
    have f3 : stepFnIter 2
        (qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
          (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1))
        (.exec qT7 (dEnv D) (.seq [qT8, qT9, qT10] (dEnv D) qStop)) ch
        = .ok (.exec (.initialization
              { id := "dequeued", typ := .array 8 tU64 }) (dEnv D)
            (.seq [qT8, qT9, qT10] (dEnv D) qStop),
          qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv false
            (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))]) (D + 1),
          ch) := by
      have := stepFnIter_splice_pop
        (σ := qStE σ ((n : Nat) : Int) sv ((k : Nat) : Int) qv lE iv
          false (tail ++ [(.base ⟨D⟩, u64cell ((k : Nat) : Int))])
          (D + 1))
        (ss := #[.initialization { id := "dequeued", typ := .array 8 tU64 }])
        (t := .initialization { id := "dequeued", typ := .array 8 tU64 })
        (ts := [qT8, qT9, qT10]) (rest := [qT8, qT9, qT10])
        (env := dEnv D) (k := qStop) (ch := ch) rfl
      simpa [qT7] using this
    have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hcommon f1) f2) f3) (hrest ((k : Nat) : Int))
    rw [show (9 : Nat) + 1 + 6 + 1 + 3 + 6 + 1 + 2 + 2 + 30 = 61 from by
      omega] at hall
    rw [show ((min k n : Nat) : Int) = ((k : Nat) : Int) from by
      rw [Nat.min_eq_left (by omega)]]
    exact hall

/-! ## The dequeue phase: head, iteration, loop.

The dequeue-loop cells sit at `D..D+3` inside the tail; the backing at
`B` is READ-ONLY here (`q[1:]` only advances the header), so the whole
phase is choice-free and the stream rides through unchanged. -/

/-- The four dequeue-loop cells. -/
def qdCells (D : Nat) (dv : Int) (lD : List Int) (jv : Int) (ff : Bool) :
    Heap :=
  [(.base ⟨D⟩, u64cell dv), (.base ⟨D + 1⟩, arrCellU 8 lD),
   (.base ⟨D + 2⟩, u64cell jv), (.base ⟨D + 3⟩, bcell ff)]

/-- The dequeue-phase state: front + read-only mid + the four cells +
the accumulated dead frames. -/
abbrev qStD (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (mid : Heap) (D : Nat) (dv : Int) (lD : List Int)
    (jv : Int) (ff : Bool) (rest : Heap) (na : Nat) : ExecState :=
  qStE σ nv sv kv qv lE nv false
    (mid ++ (qdCells D dv lD jv ff ++ rest)) na

/-- Lookup of one of the four cells (the mid part is dead past `D`). -/
theorem qdCells_lookup {nv sv kv : Int} {qv : GoValue} {lE : List Int}
    {mid : Heap} {D : Nat} {dv : Int} {lD : List Int} {jv : Int}
    {ff : Bool} {rest : Heap} {j : Nat} {c : HeapCell}
    (h12 : 12 ≤ D) (hmid : DeadFrom mid D)
    (hj : Heap.lookup (qdCells D dv lD jv ff) (.base ⟨D + j⟩) = some c) :
    Heap.lookup (qFront nv sv kv zeros8 zeros8 0 qv lE nv false
      ++ (mid ++ (qdCells D dv lD jv ff ++ rest))) (.base ⟨D + j⟩)
      = some c := by
  rw [lookup_append_right (qFront_miss (by omega)),
    lookup_append_right (hmid _ (by omega))]
  exact lookup_append_left hj

/-- Setting one of the four cells. -/
theorem qdCells_set {nv sv kv : Int} {qv : GoValue} {lE : List Int}
    {mid : Heap} {D : Nat} {dv : Int} {lD : List Int} {jv : Int}
    {ff : Bool} {rest cells' : Heap} {j : Nat} {c : HeapCell}
    (h12 : 12 ≤ D) (hmid : DeadFrom mid D)
    (hset : Heap.set (qdCells D dv lD jv ff) (.base ⟨D + j⟩) c = cells')
    (hj : ∃ c₀, Heap.lookup (qdCells D dv lD jv ff) (.base ⟨D + j⟩)
      = some c₀) :
    Heap.set (qFront nv sv kv zeros8 zeros8 0 qv lE nv false
      ++ (mid ++ (qdCells D dv lD jv ff ++ rest))) (.base ⟨D + j⟩) c
      = qFront nv sv kv zeros8 zeros8 0 qv lE nv false
          ++ (mid ++ (cells' ++ rest)) := by
  obtain ⟨c₀, hc₀⟩ := hj
  rw [set_append_right (qFront_miss (by omega)),
    set_append_right (hmid _ (by omega)), set_append_left hc₀, hset]

/-- The dequeue body's `$forFirst` dispatch spine. -/
def qdFfK (D : Nat) : Cont :=
  .ifK (.assign (.var "$forFirst") (.boolLit false))
    (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64)))
    (qdEnv1 D)
    (.seq [.seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[]) .breakStmt,
      qdFill] (qdEnv1 D) (qdLoopK D))

/-- The exit-test spine at the `i` read. -/
def qdTestK (D : Nat) : Cont :=
  .strictK .lessCmp [] [.var "d"] (qdEnv1 D) (qdCmpK D)

/-- The dequeue head: `$forFirst` true → the first exit test. 25
steps. -/
theorem qd_head (σ : ExecState) (nv sv kv : Int) (qv : GoValue)
    (lE : List Int) (mid : Heap) (D : Nat) (dv : Int) (lD : List Int)
    (rest : Heap) (na : Nat) (ch : Choices)
    (h12 : 12 ≤ D) (hmid : DeadFrom mid D) :
    stepFnIter 25
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (qdHeadCfg D) ch
      = .ok (.retV (.bool (decide ((0 : Int) < dv))) (qdCmpK D),
          qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) := by
  have hh1 : stepFnIter 3
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (qdHeadCfg D) ch
      = .ok (.exec qdBody (qdEnv D) (qdLoopK D),
          qStD σ nv sv kv qv lE mid D dv lD 0 true rest na, ch) := by
    with_unfolding_all rfl
  have hh2 : stepFnIter 2
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (.exec qdBody (qdEnv D) (qdLoopK D)) ch
      = .ok (.exec (.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))))
          (qdEnv1 D)
          (.seq [.seqn #[],
            .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
              .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D)),
        qStD σ nv sv kv qv lE mid D dv lD 0 true rest na, ch) := by
    have h := stepFnIter_block_pop
      (σ := qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (ss := #[.ifThenElse (.var "$forFirst")
          (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
        .seqn #[],
        .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
          .breakStmt, qdFill])
      (env := qdEnv D) (k := qdLoopK D) (ch := ch) rfl
    rw [show (qdBody : Stmt) = .block #[]
      #[.ifThenElse (.var "$forFirst")
          (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
        .seqn #[],
        .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
          .breakStmt, qdFill] from rfl]
    exact h
  have hh3 : stepFnIter 1
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (.exec (.ifThenElse (.var "$forFirst")
          (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))))
        (qdEnv1 D)
        (.seq [.seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
            .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D))) ch
      = .ok (.evalE (.var "$forFirst") (qdEnv1 D) (qdFfK D),
          qStD σ nv sv kv qv lE mid D dv lD 0 true rest na, ch) := by
    with_unfolding_all rfl
  have hh4 : stepFnIter 1
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (.evalE (.var "$forFirst") (qdEnv1 D) (qdFfK D)) ch
      = .ok (.retV (.bool true) (qdFfK D),
          qStD σ nv sv kv qv lE mid D dv lD 0 true rest na, ch) := by
    refine stepFnIter_one (stepFn_var (c := bcell true) rfl ?_)
    exact qdCells_lookup h12 hmid (by
      rw [qdCells,
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 3)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 3)),
        lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ D + 3))]
      simp [Heap.lookup])
  have hh5 : stepFnIter 6
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (.retV (.bool true) (qdFfK D)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨D + 3⟩)) [] []]
            [.bool false] (.seqn #[]) (qdEnv1 D)
            (.seq [.seqn #[],
              .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
                .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D))),
          qStD σ nv sv kv qv lE mid D dv lD 0 true rest na, ch) := by
    with_unfolding_all rfl
  have hstF : storeTarget
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (.chain (.addr (.base ⟨D + 3⟩)) [] []) (.bool false)
      = .ok (qSt σ (qFront nv sv kv zeros8 zeros8 0 qv lE nv false
          ++ (mid ++ (qdCells D dv lD 0 false ++ rest))) na) := by
    have hlk : Heap.lookup
        ((qStD σ nv sv kv qv lE mid D dv lD 0 true rest na).heap)
        (.base ⟨D + 3⟩) = some (bcell true) :=
      qdCells_lookup h12 hmid (by
        rw [qdCells,
          lookup_cons_ne (base_beq_false (by omega : D ≠ D + 3)),
          lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 3)),
          lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ D + 3))]
        simp [Heap.lookup])
    have h := storeTarget_addr
      (σ := qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      hlk (normVal_bool _ false)
    rw [show Heap.set
        ((qStD σ nv sv kv qv lE mid D dv lD 0 true rest na).heap)
        (.base ⟨D + 3⟩) ⟨some .bool, .bool false⟩
      = qFront nv sv kv zeros8 zeros8 0 qv lE nv false
          ++ (mid ++ (qdCells D dv lD 0 false ++ rest)) from by
      show Heap.set (qFront nv sv kv zeros8 zeros8 0 qv lE nv false
          ++ (mid ++ (qdCells D dv lD 0 true ++ rest))) (.base ⟨D + 3⟩)
          ⟨some .bool, .bool false⟩ = _
      refine qdCells_set h12 hmid ?_ ?_
      · rw [qdCells, qdCells]
        simp [Heap.set, base_beq_false (by omega : D ≠ D + 3),
          base_beq_false (by omega : D + 1 ≠ D + 3),
          base_beq_false (by omega : D + 2 ≠ D + 3)]
      · exact ⟨bcell true, by
          rw [qdCells,
            lookup_cons_ne (base_beq_false (by omega : D ≠ D + 3)),
            lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 3)),
            lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ D + 3))]
          simp [Heap.lookup]⟩] at h
    exact h
  have hh6 : stepFnIter 1
      (qStD σ nv sv kv qv lE mid D dv lD 0 true rest na)
      (.next (.storeK [.chain (.addr (.base ⟨D + 3⟩)) [] []]
        [.bool false] (.seqn #[]) (qdEnv1 D)
        (.seq [.seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
            .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qdEnv1 D)
          (.seq [.seqn #[],
            .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
              .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D))),
        qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) :=
    stepFnIter_one (stepFn_store_step hstF)
  have hh7 := stepFnIter_drain3
    (σ := qStD σ nv sv kv qv lE mid D dv lD 0 false rest na)
    (t := .seqn #[])
    (ts := [.ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
      .breakStmt, qdFill])
    (env := qdEnv1 D) (k := qdLoopK D) (ch := ch)
  have hh8 : stepFnIter 2
      (qStD σ nv sv kv qv lE mid D dv lD 0 false rest na)
      (.exec (.seqn #[]) (qdEnv1 D)
        (.seq [.ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
          .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D))) ch
      = .ok (.exec (.ifThenElse (.lessCmp (.var "i") (.var "d"))
            (.seqn #[]) .breakStmt) (qdEnv1 D)
          (.seq [qdFill] (qdEnv1 D) (qdLoopK D)),
        qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  have hh9 : stepFnIter 2
      (qStD σ nv sv kv qv lE mid D dv lD 0 false rest na)
      (.exec (.ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
        .breakStmt) (qdEnv1 D)
        (.seq [qdFill] (qdEnv1 D) (qdLoopK D))) ch
      = .ok (.evalE (.var "i") (qdEnv1 D) (qdTestK D),
          qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) := by
    with_unfolding_all rfl
  have hh10 : stepFnIter 1
      (qStD σ nv sv kv qv lE mid D dv lD 0 false rest na)
      (.evalE (.var "i") (qdEnv1 D) (qdTestK D)) ch
      = .ok (.retV (.int 0 .uint64) (qdTestK D),
          qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell 0) rfl ?_)
    exact qdCells_lookup h12 hmid (by
      rw [qdCells,
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 2)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 2))]
      simp [Heap.lookup])
  have hh11 : stepFnIter 1
      (qStD σ nv sv kv qv lE mid D dv lD 0 false rest na)
      (.retV (.int 0 .uint64) (qdTestK D)) ch
      = .ok (.evalE (.var "d") (qdEnv1 D)
          (.strictK .lessCmp [.int 0 .uint64] [] (qdEnv1 D) (qdCmpK D)),
        qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) := by
    with_unfolding_all rfl
  have hh12 : stepFnIter 1
      (qStD σ nv sv kv qv lE mid D dv lD 0 false rest na)
      (.evalE (.var "d") (qdEnv1 D)
        (.strictK .lessCmp [.int 0 .uint64] [] (qdEnv1 D) (qdCmpK D))) ch
      = .ok (.retV (.int dv .uint64)
          (.strictK .lessCmp [.int 0 .uint64] [] (qdEnv1 D) (qdCmpK D)),
        qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell dv) rfl ?_)
    have : Heap.lookup (qdCells D dv lD 0 false) (.base ⟨D + 0⟩)
        = some (u64cell dv) := by
      rw [qdCells]
      simp [Heap.lookup]
    have h := qdCells_lookup (nv := nv) (sv := sv) (kv := kv) (qv := qv)
      (lE := lE) (rest := rest) (j := 0) h12 hmid this
    simpa using h
  have hh13 : stepFnIter 1
      (qStD σ nv sv kv qv lE mid D dv lD 0 false rest na)
      (.retV (.int dv .uint64)
        (.strictK .lessCmp [.int 0 .uint64] [] (qdEnv1 D) (qdCmpK D))) ch
      = .ok (.retV (.bool (decide ((0 : Int) < dv))) (qdCmpK D),
          qStD σ nv sv kv qv lE mid D dv lD 0 false rest na, ch) := by
    with_unfolding_all rfl
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hh1 hh2)
          hh3) hh4) hh5) hh6) hh7) hh8) hh9) hh10) hh11) hh12) hh13
  rw [show (3 : Nat) + 2 + 1 + 1 + 6 + 1 + 3 + 2 + 2 + 1 + 1 + 1 + 1
      = 25 from by omega] at hall
  exact hall

/-- The `q[0]` read spine at the callee's `q` read. -/
def dqIdxK (D na : Nat) : Cont :=
  .strictK .indexGet [] [.intLit 0 .int] (dqcEnvV na)
    (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] [] (.seqn #[])
      (dqcEnvV na)
      (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na)))

/-- The re-slice spine at the callee's second `q` read (the slice
expression's base). -/
def dqSlK (D na : Nat) : Cont :=
  .strictK (.sliceExpr false) [] [.intLit 1 .int,
      .length (.var "q") (some sliceU)] (dqcEnvV na)
    (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] [] (.seqn #[])
      (dqcEnvV na)
      (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
        (dqcEnvV na) (qdFrameK D na)))

/-- The `len(q)` spine at the callee's third `q` read. -/
def dqLenK (D na : Nat) (qv : GoValue) : Cont :=
  .strictK (.lengthOf (some sliceU)) [] [] (dqcEnvV na)
    (.strictK (.sliceExpr false) [.int 1 .int, qv] [] (dqcEnvV na)
      (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
        (.seqn #[]) (dqcEnvV na)
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (dqcEnvV na) (qdFrameK D na))))

/-- The `dequeue` callee body, end to end: 49 steps from the body entry
to the frame return, generic in the heap through the lookup/store
facts. `w` is the dequeued value, `qv`/`qv'` the old and re-sliced
handles. -/
theorem qd_callee (σ : ExecState) (H : Heap) (D na : Nat)
    (B off len cap : Nat) (lq : List Int) (w : Int) (ch : Choices)
    (hlen1 : 1 ≤ len) (hcap : len ≤ cap)
    (hB : Heap.lookup H (.base ⟨B⟩)
      = some ⟨some (.array (lq.length) tU64),
          .array ⟨lq.map (fun v => .int v .uint64)⟩⟩)
    (hoff : off + len ≤ lq.length)
    (hgetw : lq.getD off 0 = w)
    (hq1 : Heap.lookup H (.base ⟨na + 1⟩)
      = some (slCell (qslV B off len cap)))
    (hr0 : Heap.lookup H (.base ⟨na + 2⟩)
      = some (slCell (.slice ⟨none, 0, 0, 0⟩)))
    (hr1 : Heap.lookup H (.base ⟨na + 3⟩) = some (u64cell 0))
    (hdead : DeadFrom H (na + 4))
    (hwr : 0 ≤ w ∧ w < 2 ^ 64) :
    stepFnIter 49 (qSt σ H (na + 4))
      (.exec dequeueFunc.body (dqcEnv na) (qdFrameK D na)) ch
      = .ok (.returning (qdFrameK D na),
          qSt σ (Heap.set (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
              (.base ⟨na + 2⟩)
              (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
            (.base ⟨na + 3⟩) (u64cell w))
          (na + 5), ch) := by
  -- body entry → init v (4)
  have p1 : stepFnIter 4 (qSt σ H (na + 4))
      (.exec dequeueFunc.body (dqcEnv na) (qdFrameK D na)) ch
      = .ok (.exec (.initialization { id := "v", typ := tU64 })
          ([] :: dqcEnv na)
          (.seq [.assign (.var "v")
              (.indexGet (.var "q") (.intLit 0 .int)), dqSeqnB]
            ([] :: dqcEnv na) (qdFrameK D na)),
        qSt σ H (na + 4), ch) := by
    have a1 : stepFnIter 2 (qSt σ H (na + 4))
        (.exec dequeueFunc.body (dqcEnv na) (qdFrameK D na)) ch
        = .ok (.exec dqSeqnA ([] :: dqcEnv na)
            (.seq [dqSeqnB] ([] :: dqcEnv na) (qdFrameK D na)),
          qSt σ H (na + 4), ch) := by
      have h := stepFnIter_block_pop (σ := qSt σ H (na + 4))
        (ss := #[dqSeqnA, dqSeqnB]) (env := dqcEnv na)
        (k := qdFrameK D na) (ch := ch) rfl
      rw [show (dequeueFunc.body : Stmt) = .block #[] #[dqSeqnA, dqSeqnB]
        from rfl]
      exact h
    have a2 : stepFnIter 2 (qSt σ H (na + 4))
        (.exec dqSeqnA ([] :: dqcEnv na)
          (.seq [dqSeqnB] ([] :: dqcEnv na) (qdFrameK D na))) ch
        = .ok (.exec (.initialization { id := "v", typ := tU64 })
            ([] :: dqcEnv na)
            (.seq [.assign (.var "v")
                (.indexGet (.var "q") (.intLit 0 .int)), dqSeqnB]
              ([] :: dqcEnv na) (qdFrameK D na)),
          qSt σ H (na + 4), ch) := by
      have h := stepFnIter_splice_pop (σ := qSt σ H (na + 4))
        (ss := #[.initialization { id := "v", typ := tU64 },
          .assign (.var "v") (.indexGet (.var "q") (.intLit 0 .int))])
        (t := .initialization { id := "v", typ := tU64 })
        (ts := [.assign (.var "v")
          (.indexGet (.var "q") (.intLit 0 .int)), dqSeqnB])
        (rest := [dqSeqnB]) (env := [] :: dqcEnv na)
        (k := qdFrameK D na) (ch := ch) rfl
      rw [show (dqSeqnA : Stmt)
        = .seqn #[.initialization { id := "v", typ := tU64 },
          .assign (.var "v") (.indexGet (.var "q") (.intLit 0 .int))]
        from rfl]
      exact h
    exact stepFnIter_chain a1 a2
  -- init v (1): the cell at na+4
  have p2 : stepFnIter 1 (qSt σ H (na + 4))
      (.exec (.initialization { id := "v", typ := tU64 })
        ([] :: dqcEnv na)
        (.seq [.assign (.var "v")
            (.indexGet (.var "q") (.intLit 0 .int)), dqSeqnB]
          ([] :: dqcEnv na) (qdFrameK D na))) ch
      = .ok (.next (.seq [.assign (.var "v")
            (.indexGet (.var "q") (.intLit 0 .int)), dqSeqnB]
          (dqcEnvV na) (qdFrameK D na)),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5), ch) := by
    have h := stepFnIter_one (stepFn_init_seq (σ := qSt σ H (na + 4))
      (p := { id := "v", typ := tU64 })
      (rest := [.assign (.var "v")
        (.indexGet (.var "q") (.intLit 0 .int)), dqSeqnB])
      (env := [] :: dqcEnv na) (k := qdFrameK D na) (ch := ch)
      (hdef := by with_unfolding_all rfl))
    rw [show LocalEnv.declare ([] :: dqcEnv na) "v"
        (.base ⟨(qSt σ H (na + 4)).nextAddr⟩) = dqcEnvV na from rfl] at h
    rw [show Heap.set (qSt σ H (na + 4)).heap
        (.base ⟨(qSt σ H (na + 4)).nextAddr⟩) ⟨some tU64, .int 0 .uint64⟩
      = H ++ [(.base ⟨na + 4⟩, u64cell 0)] from by
        show Heap.set H (.base ⟨na + 4⟩) _ = _
        exact set_fresh (hdead _ (Nat.le_refl _))] at h
    exact h
  -- v := q[0]: to the q read (5)
  have p3 : stepFnIter 5 (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)])
      (na + 5))
      (.next (.seq [.assign (.var "v")
          (.indexGet (.var "q") (.intLit 0 .int)), dqSeqnB]
        (dqcEnvV na) (qdFrameK D na))) ch
      = .ok (.evalE (.var "q") (dqcEnvV na) (dqIdxK D na),
          qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5), ch) := by
    with_unfolding_all rfl
  have hq1' : Heap.lookup (H ++ [(.base ⟨na + 4⟩, u64cell 0)])
      (.base ⟨na + 1⟩) = some (slCell (qslV B off len cap)) :=
    lookup_append_left hq1
  have p4 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5))
      (.evalE (.var "q") (dqcEnvV na) (dqIdxK D na)) ch
      = .ok (.retV (qslV B off len cap) (dqIdxK D na),
          qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := slCell (qslV B off len cap)) rfl ?_)
    exact hq1'
  have p5 : stepFnIter 2
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5))
      (.retV (qslV B off len cap) (dqIdxK D na)) ch
      = .ok (.retV (.int 0 .int)
          (.strictK .indexGet [qslV B off len cap] [] (dqcEnvV na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
              (.seqn #[]) (dqcEnvV na)
              (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na)))),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5), ch) := by
    with_unfolding_all rfl
  -- q[0] apply (1)
  have hgetq : (⟨lq.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[off + 0]? = some (.int w .uint64) := by
    rw [getElem?_mapU lq (off + 0) (by omega)]
    rw [show off + 0 = off from rfl, hgetw]
  have p6 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5))
      (.retV (.int 0 .int)
        (.strictK .indexGet [qslV B off len cap] [] (dqcEnvV na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
            (.seqn #[]) (dqcEnvV na)
            (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na))))) ch
      = .ok (.retV (.int w .uint64)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
            (.seqn #[]) (dqcEnvV na)
            (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na))),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5), ch) := by
    refine stepFnIter_one (stepFn_strict_apply
      (op := .indexGet) (done := [qslV B off len cap])
      (v := .int 0 .int) (out := .int w .uint64)
      (env := dqcEnvV na)
      (k := .rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
        (.seqn #[]) (dqcEnvV na)
        (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na))) ?_)
    exact applyStrictOp_indexGet_slice (ik := .int) (i := 0)
      (off := off) (len := len) (cap := cap) (a := ⟨B⟩)
      (vs := ⟨lq.map (fun v => .int v .uint64)⟩)
      (lookup_append_left hB) hcap (by omega) hgetq
  -- rhs delivered → store v (2)
  have p7 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5))
      (.retV (.int w .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 4⟩)) [] []] [] []
          (.seqn #[]) (dqcEnvV na)
          (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 4⟩)) [] []]
            [.int w .uint64] (.seqn #[]) (dqcEnvV na)
            (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na))),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5), ch) := by
    with_unfolding_all rfl
  have hstv : storeTarget
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5))
      (.chain (.addr (.base ⟨na + 4⟩)) [] []) (.int w .uint64)
      = .ok (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5)) := by
    have hlk : Heap.lookup
        ((qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5)).heap)
        (.base ⟨na + 4⟩) = some (u64cell 0) := by
      show Heap.lookup (H ++ [(.base ⟨na + 4⟩, u64cell 0)])
        (.base ⟨na + 4⟩) = some (u64cell 0)
      rw [lookup_append_right (hdead _ (Nat.le_refl _))]
      exact lookup_singleton_self
    have h := storeTarget_addr
      (σ := qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5))
      hlk (normVal_u64 _ hwr.1 hwr.2)
    rw [show Heap.set
        ((qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5)).heap)
        (.base ⟨na + 4⟩) ⟨some tU64, .int w .uint64⟩
      = H ++ [(.base ⟨na + 4⟩, u64cell w)] from by
        show Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell 0)])
          (.base ⟨na + 4⟩) _ = _
        rw [set_append_right (hdead _ (Nat.le_refl _)),
          set_singleton_self]] at h
    exact h
  have p8 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell 0)]) (na + 5))
      (.next (.storeK [.chain (.addr (.base ⟨na + 4⟩)) [] []]
        [.int w .uint64] (.seqn #[]) (dqcEnvV na)
        (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (dqcEnvV na)
          (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na))),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) :=
    stepFnIter_one (stepFn_store_step hstv)
  -- drain to `$res0 = q[1:len(q)]` (5), then to the q read (4)
  have p9 : stepFnIter 3
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.next (.storeK [] [] (.seqn #[]) (dqcEnvV na)
        (.seq [dqSeqnB] (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.exec dqSeqnB (dqcEnvV na)
          (.seq [] (dqcEnvV na) (qdFrameK D na)),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) :=
    stepFnIter_drain3 (t := dqSeqnB) (ts := [])
  have p10 : stepFnIter 2
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.exec dqSeqnB (dqcEnvV na)
        (.seq [] (dqcEnvV na) (qdFrameK D na))) ch
      = .ok (.exec (.assign (.var "$res0")
            (.slice (.var "q") (.intLit 1 .int)
              (.length (.var "q") (some sliceU)) none)) (dqcEnvV na)
          (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
            (dqcEnvV na) (qdFrameK D na)),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    have h := stepFnIter_splice_pop
      (σ := qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (ss := #[.assign (.var "$res0")
          (.slice (.var "q") (.intLit 1 .int)
            (.length (.var "q") (some sliceU)) none),
        .assign (.var "$res1") (.var "v"), .returnStmt])
      (t := .assign (.var "$res0")
        (.slice (.var "q") (.intLit 1 .int)
          (.length (.var "q") (some sliceU)) none))
      (ts := [.assign (.var "$res1") (.var "v"), .returnStmt])
      (rest := []) (env := dqcEnvV na) (k := qdFrameK D na) (ch := ch)
      rfl
    rw [show (dqSeqnB : Stmt) = .seqn #[.assign (.var "$res0")
        (.slice (.var "q") (.intLit 1 .int)
          (.length (.var "q") (some sliceU)) none),
      .assign (.var "$res1") (.var "v"), .returnStmt] from rfl]
    exact h
  have p11 : stepFnIter 4
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.exec (.assign (.var "$res0")
          (.slice (.var "q") (.intLit 1 .int)
            (.length (.var "q") (some sliceU)) none)) (dqcEnvV na)
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (dqcEnvV na) (qdFrameK D na))) ch
      = .ok (.evalE (.var "q") (dqcEnvV na) (dqSlK D na),
          qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    with_unfolding_all rfl
  have hq1w : Heap.lookup (H ++ [(.base ⟨na + 4⟩, u64cell w)])
      (.base ⟨na + 1⟩) = some (slCell (qslV B off len cap)) :=
    lookup_append_left hq1
  have p12 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.evalE (.var "q") (dqcEnvV na) (dqSlK D na)) ch
      = .ok (.retV (qslV B off len cap) (dqSlK D na),
          qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := slCell (qslV B off len cap)) rfl ?_)
    exact hq1w
  have p13 : stepFnIter 4
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.retV (qslV B off len cap) (dqSlK D na)) ch
      = .ok (.evalE (.var "q") (dqcEnvV na)
          (dqLenK D na (qslV B off len cap)),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    with_unfolding_all rfl
  have p14 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.evalE (.var "q") (dqcEnvV na)
        (dqLenK D na (qslV B off len cap))) ch
      = .ok (.retV (qslV B off len cap)
          (dqLenK D na (qslV B off len cap)),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := slCell (qslV B off len cap)) rfl ?_)
    exact hq1w
  have p15 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.retV (qslV B off len cap)
        (dqLenK D na (qslV B off len cap))) ch
      = .ok (.retV (.int (len : Nat) .int)
          (.strictK (.sliceExpr false)
            [.int 1 .int, qslV B off len cap] [] (dqcEnvV na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
              (.seqn #[]) (dqcEnvV na)
              (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
                (dqcEnvV na) (qdFrameK D na)))),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    refine stepFnIter_one (stepFn_strict_apply
      (op := .lengthOf (some sliceU)) (done := [])
      (v := qslV B off len cap) (out := .int (len : Nat) .int) ?_)
    exact applyStrictOp_len_slice hcap
  have p16 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.retV (.int (len : Nat) .int)
        (.strictK (.sliceExpr false)
          [.int 1 .int, qslV B off len cap] [] (dqcEnvV na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
            (.seqn #[]) (dqcEnvV na)
            (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
              (dqcEnvV na) (qdFrameK D na))))) ch
      = .ok (.retV (.slice ⟨some (.base ⟨B⟩), off + 1, len - 1, cap - 1⟩)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
            (.seqn #[]) (dqcEnvV na)
            (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
              (dqcEnvV na) (qdFrameK D na))),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    refine stepFnIter_one (stepFn_strict_apply
      (op := .sliceExpr false) (done := [.int 1 .int, qslV B off len cap])
      (v := .int (len : Nat) .int)
      (out := .slice ⟨some (.base ⟨B⟩), off + 1, len - 1, cap - 1⟩) ?_)
    exact applyStrictOp_sliceExpr_slice hlen1 hcap
  have p17 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.retV (.slice ⟨some (.base ⟨B⟩), off + 1, len - 1, cap - 1⟩)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
          (.seqn #[]) (dqcEnvV na)
          (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
            (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 2⟩)) [] []]
          [.slice ⟨some (.base ⟨B⟩), off + 1, len - 1, cap - 1⟩]
          (.seqn #[]) (dqcEnvV na)
          (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
            (dqcEnvV na) (qdFrameK D na))),
        qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5), ch) := by
    with_unfolding_all rfl
  have hstr0 : storeTarget
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.chain (.addr (.base ⟨na + 2⟩)) [] [])
      (.slice ⟨some (.base ⟨B⟩), off + 1, len - 1, cap - 1⟩)
      = .ok (qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
          (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5)) := by
    exact storeTarget_addr (lookup_append_left hr0)
      (normVal_slice _ _)
  have p18 : stepFnIter 1
      (qSt σ (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (na + 5))
      (.next (.storeK [.chain (.addr (.base ⟨na + 2⟩)) [] []]
        [.slice ⟨some (.base ⟨B⟩), off + 1, len - 1, cap - 1⟩]
        (.seqn #[]) (dqcEnvV na)
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (dqcEnvV na)
          (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
            (dqcEnvV na) (qdFrameK D na))),
        qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
          (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5),
        ch) :=
    stepFnIter_one (stepFn_store_step hstr0)
  -- `$res1 = v` (3 + read + rhs + store)
  have p19 : stepFnIter 6
      (qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5))
      (.next (.storeK [] [] (.seqn #[]) (dqcEnvV na)
        (.seq [.assign (.var "$res1") (.var "v"), .returnStmt]
          (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.evalE (.var "v") (dqcEnvV na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
            (.seqn #[]) (dqcEnvV na)
            (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na))),
        qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
          (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5),
        ch) := by
    have a1 := stepFnIter_drain3
      (σ := qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5))
      (t := .assign (.var "$res1") (.var "v")) (ts := [.returnStmt])
      (env := dqcEnvV na) (k := qdFrameK D na) (ch := ch)
    have a2 : stepFnIter 3
        (qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
          (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5))
        (.exec (.assign (.var "$res1") (.var "v")) (dqcEnvV na)
          (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na))) ch
        = .ok (.evalE (.var "v") (dqcEnvV na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
              (.seqn #[]) (dqcEnvV na)
              (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na))),
          qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
            (.base ⟨na + 2⟩)
            (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5),
          ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain a1 a2
  have p20 : stepFnIter 1
      (qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5))
      (.evalE (.var "v") (dqcEnvV na)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
          (.seqn #[]) (dqcEnvV na)
          (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.retV (.int w .uint64)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
            (.seqn #[]) (dqcEnvV na)
            (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na))),
        qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
          (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5),
        ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell w) rfl ?_)
    show Heap.lookup (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (.base ⟨na + 4⟩)
      = some (u64cell w)
    rw [Machine.Heap.lookup_set_ne (by
        simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
        omega),
      lookup_append_right (hdead _ (Nat.le_refl _))]
    exact lookup_singleton_self
  have p21 : stepFnIter 1
      (qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5))
      (.retV (.int w .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨na + 3⟩)) [] []] [] []
          (.seqn #[]) (dqcEnvV na)
          (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 3⟩)) [] []]
          [.int w .uint64] (.seqn #[]) (dqcEnvV na)
          (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na))),
        qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
          (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5),
        ch) := by
    with_unfolding_all rfl
  have hstr1 : storeTarget
      (qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5))
      (.chain (.addr (.base ⟨na + 3⟩)) [] []) (.int w .uint64)
      = .ok (qSt σ (Heap.set (Heap.set
          (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
          (.base ⟨na + 3⟩) (u64cell w)) (na + 5)) := by
    refine storeTarget_addr (old := .int 0 .uint64) ?_
      (normVal_u64 _ hwr.1 hwr.2)
    show Heap.lookup (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (.base ⟨na + 3⟩)
      = some (u64cell 0)
    rw [Machine.Heap.lookup_set_ne (by
        simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
        omega)]
    exact lookup_append_left hr1
  have p22 : stepFnIter 1
      (qSt σ (Heap.set (H ++ [(.base ⟨na + 4⟩, u64cell w)])
        (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1)))) (na + 5))
      (.next (.storeK [.chain (.addr (.base ⟨na + 3⟩)) [] []]
        [.int w .uint64] (.seqn #[]) (dqcEnvV na)
        (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (dqcEnvV na)
          (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na))),
        qSt σ (Heap.set (Heap.set
          (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
          (.base ⟨na + 3⟩) (u64cell w)) (na + 5), ch) :=
    stepFnIter_one (stepFn_store_step hstr1)
  have p23 : stepFnIter 5
      (qSt σ (Heap.set (Heap.set
        (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
        (.base ⟨na + 3⟩) (u64cell w)) (na + 5))
      (.next (.storeK [] [] (.seqn #[]) (dqcEnvV na)
        (.seq [.returnStmt] (dqcEnvV na) (qdFrameK D na)))) ch
      = .ok (.returning (qdFrameK D na),
          qSt σ (Heap.set (Heap.set
            (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (.base ⟨na + 2⟩)
            (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
            (.base ⟨na + 3⟩) (u64cell w)) (na + 5), ch) := by
    have a1 := stepFnIter_drain3
      (σ := qSt σ (Heap.set (Heap.set
        (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (.base ⟨na + 2⟩)
        (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
        (.base ⟨na + 3⟩) (u64cell w)) (na + 5))
      (t := .returnStmt) (ts := []) (env := dqcEnvV na)
      (k := qdFrameK D na) (ch := ch)
    have a2 : stepFnIter 2
        (qSt σ (Heap.set (Heap.set
          (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (.base ⟨na + 2⟩)
          (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
          (.base ⟨na + 3⟩) (u64cell w)) (na + 5))
        (.exec .returnStmt (dqcEnvV na)
          (.seq [] (dqcEnvV na) (qdFrameK D na))) ch
        = .ok (.returning (qdFrameK D na),
            qSt σ (Heap.set (Heap.set
              (H ++ [(.base ⟨na + 4⟩, u64cell w)]) (.base ⟨na + 2⟩)
              (slCell (qslV B (off + 1) (len - 1) (cap - 1))))
              (.base ⟨na + 3⟩) (u64cell w)) (na + 5), ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain a1 a2
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                (stepFnIter_chain p1 p2) p3) p4) p5) p6) p7) p8) p9)
                  p10) p11) p12) p13) p14) p15) p16) p17) p18) p19)
                    p20) p21) p22) p23
  rw [show (4 : Nat) + 1 + 5 + 1 + 2 + 1 + 1 + 1 + 3 + 2 + 4 + 1 + 4 + 1
      + 1 + 1 + 1 + 1 + 6 + 1 + 1 + 1 + 5 = 49 from by omega] at hall
  exact hall

/-- **The enqueue loop**: exactly `130·(n−j)` steps at EVERY choice
stream, existentially packaging the (choice-dependent) backing address,
capacity, dead tail and remaining stream. -/
theorem qe_loop (σ : ExecState) (n seed k : Nat)
    (hfn : findFunctionIn? σ.functions ⟨"enqueue"⟩ = some enqueueFunc)
    (hm : σ.methods = #[]) (hn8 : n ≤ 8) :
    ∀ j, j ≤ n → ∀ (B C : Nat) (tail : Heap) (na : Nat) (ch : Choices),
    qEnqInv seed j B C na tail →
    ∃ (B' C' : Nat) (tail' : Heap) (na' : Nat) (ch' : Choices),
      stepFnIter (130 * (n - j))
        (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
          (qslV B 0 j C) (qPre j seed) ((j : Nat) : Int) false tail na)
        (.retV (.bool (decide (((j : Nat) : Int) < ((n : Nat) : Int))))
          qeCmpK) ch
        = .ok (.retV (.bool (decide
              (((n : Nat) : Int) < ((n : Nat) : Int)))) qeCmpK,
            qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
              (qslV B' 0 n C') (qPre n seed) ((n : Nat) : Int) false
              tail' na', ch')
      ∧ na ≤ na' ∧ qEnqInv seed n B' C' na' tail' := by
  suffices key : ∀ μ j, μ = n - j → j ≤ n →
      ∀ (B C : Nat) (tail : Heap) (na : Nat) (ch : Choices),
      qEnqInv seed j B C na tail →
      ∃ (B' C' : Nat) (tail' : Heap) (na' : Nat) (ch' : Choices),
        stepFnIter (130 * (n - j))
          (qStE σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
            (qslV B 0 j C) (qPre j seed) ((j : Nat) : Int) false tail na)
          (.retV (.bool (decide (((j : Nat) : Int) < ((n : Nat) : Int))))
            qeCmpK) ch
          = .ok (.retV (.bool (decide
                (((n : Nat) : Int) < ((n : Nat) : Int)))) qeCmpK,
              qStE σ ((n : Nat) : Int) ((seed : Nat) : Int)
                ((k : Nat) : Int) (qslV B' 0 n C') (qPre n seed)
                ((n : Nat) : Int) false tail' na', ch')
        ∧ na ≤ na' ∧ qEnqInv seed n B' C' na' tail' by
    intro j hj
    exact key (n - j) j rfl hj
  intro μ
  induction μ with
  | zero =>
      intro j hμ hj B C tail na ch hinv
      have heq : j = n := by omega
      subst heq
      rw [Nat.sub_self, Nat.mul_zero]
      exact ⟨B, C, tail, na, ch, rfl, Nat.le_refl _, hinv⟩
  | succ μ' ih =>
      intro j hμ hj B C tail na ch hinv
      have hlt : j < n := by omega
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨B1, C1, tail1, na1, ch1, hstep, hna1, hinv1⟩ :=
        qe_iter σ n seed k j B C tail na ch hfn hm hlt hn8 hinv
      obtain ⟨B', C', tail', na', ch', hrest, hna', hinv'⟩ :=
        ih (j + 1) (by omega) (by omega) B1 C1 tail1 na1 ch1 hinv1
      rw [show (decide (((j + 1 : Nat) : Int) < ((n : Nat) : Int)))
          = (decide (((j + 1 : Nat) : Int) < ((n : Nat) : Int)))
        from rfl] at hrest
      have hchain := stepFnIter_chain hstep hrest
      rw [show (130 : Nat) + 130 * (n - (j + 1)) = 130 * (n - j) from by
        have : n - j = (n - (j + 1)) + 1 := by omega
        rw [this, Nat.mul_succ]
        omega] at hchain
      exact ⟨B', C', tail', na', ch', hchain, by omega, hinv'⟩

/-! ## The dequeue write-back and store-block continuations -/

/-- The write-back spine after the `dequeue` frame return, at the
`.ref q` resolution (`qv2` is the loaded re-sliced handle, `w` the
loaded dequeued value). -/
def qdWbK1 (D a : Nat) (qv2 : GoValue) (w : Int) : Cont :=
  .tgtOpK (.chain []) [] [] [] [(.chain [], [.ref "v"])] .vals []
    [qv2, .int w .uint64] (.seqn #[]) (qdEnvV D a) (qdAfterCallK D a)

/-- The `dequeued[i]` store's end tail. -/
def qdEndTail (D a : Nat) : Cont :=
  .seq [] (qdEnvV D a) (.seq [] (qdEnv1 D) (qdLoopK D))

/-- The `dequeued[i] = v` target spine at the `i` read. -/
def qdStIdxK (D a : Nat) : Cont :=
  .tgtOpK (.chain [.index]) [.addr (.base ⟨D + 1⟩)] [] [] [] .vals
    [.var "v"] [] (.seqn #[]) (qdEnvV D a) (qdEndTail D a)

/-- The `dequeued[i] = v` rhs spine at the `v` read. -/
def qdStRhsK (D a : Nat) (jv : Int) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨D + 1⟩)) [.int jv .uint64] [.index]]
    [] [] (.seqn #[]) (qdEnvV D a) (qdEndTail D a)

/-- The loop tail after the increment's store drains. -/
def qdIncTail (D : Nat) : Cont :=
  .seq [.seqn #[],
    .ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[]) .breakStmt,
    qdFill] (qdEnv1 D) (qdLoopK D)

/-- The `i = i + 1` rhs spine. -/
def qdIncRhsK (D : Nat) : Cont :=
  .rhsK .vals [.chain (.addr (.base ⟨D + 2⟩)) [] []] [] [] (.seqn #[])
    (qdEnv1 D) (qdIncTail D)

/-! ## The dequeue-iteration raw segments (state-generic where the
heap is silent; the conditioned steps between them are glued in
`qd_iter`) -/

/-- Qd-call: the popped call seqn → the `q` argument read. 4 steps,
state-generic. -/
theorem qd_call_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.seq [qdCallSeqn, qdStoreSeqn] (qdEnvV D a)
        (.seq [] (qdEnv1 D) (qdLoopK D)))) ch
      = .ok (.evalE (.var "q") (qdEnvV D a) (qdCallArgsK D a), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.seq [qdCallSeqn, qdStoreSeqn] (qdEnvV D a)
        (.seq [] (qdEnv1 D) (qdLoopK D)))) ch
      = .ok (.exec qdCallSeqn (qdEnvV D a) (qdAfterCallK D a), σ, ch) :=
    stepFnIter_one stepFn_seq_pop
  have s2 : stepFnIter 2 σ
      (.exec qdCallSeqn (qdEnvV D a) (qdAfterCallK D a)) ch
      = .ok (.exec (.call #[.var "q", .var "v"] ⟨"dequeue"⟩ #[.var "q"])
          (qdEnvV D a) (qdAfterCallK D a), σ, ch) := by
    have h := stepFnIter_splice_pop (σ := σ)
      (ss := #[.call #[.var "q", .var "v"] ⟨"dequeue"⟩ #[.var "q"]])
      (t := .call #[.var "q", .var "v"] ⟨"dequeue"⟩ #[.var "q"])
      (ts := [qdStoreSeqn]) (rest := [qdStoreSeqn]) (env := qdEnvV D a)
      (k := .seq [] (qdEnv1 D) (qdLoopK D)) (ch := ch) rfl
    rw [show (qdCallSeqn : Stmt)
      = .seqn #[.call #[.var "q", .var "v"] ⟨"dequeue"⟩ #[.var "q"]]
      from rfl]
    exact h
  have s3 : stepFnIter 1 σ
      (.exec (.call #[.var "q", .var "v"] ⟨"dequeue"⟩ #[.var "q"])
        (qdEnvV D a) (qdAfterCallK D a)) ch
      = .ok (.evalE (.var "q") (qdEnvV D a) (qdCallArgsK D a), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain s1 s2) s3

/-- Qd-wb2: the write-back target chain (both `.ref` resolutions) after
the `q` target's `.ref q` read is dispatched. 4 steps, state-generic,
ending at the two-target store point. -/
theorem qd_wb2_raw (σ : ExecState) (D a : Nat) (qv2 : GoValue) (w : Int)
    (ch : Choices) :
    stepFnIter 4 σ (.evalE (.ref "q") (qdEnvV D a) (qdWbK1 D a qv2 w)) ch
      = .ok (.next (.storeK
            [.chain (.addr (.base ⟨8⟩)) [] [],
             .chain (.addr (.base ⟨a⟩)) [] []]
            [qv2, .int w .uint64] (.seqn #[]) (qdEnvV D a)
            (qdAfterCallK D a)), σ, ch) := by
  with_unfolding_all rfl

/-- Qd-b1: the drained write-back store → the `dequeued[i]` target's
`i` read. 8 steps, state-generic. -/
theorem qd_b1_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 8 σ
      (.next (.storeK [] [] (.seqn #[]) (qdEnvV D a)
        (qdAfterCallK D a))) ch
      = .ok (.evalE (.var "i") (qdEnvV D a) (qdStIdxK D a), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (qdEnvV D a)
        (qdAfterCallK D a))) ch
      = .ok (.exec (.seqn #[]) (qdEnvV D a) (qdAfterCallK D a), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 2 σ
      (.exec (.seqn #[]) (qdEnvV D a) (qdAfterCallK D a)) ch
      = .ok (.exec qdStoreSeqn (qdEnvV D a)
          (.seq [] (qdEnvV D a) (.seq [] (qdEnv1 D) (qdLoopK D))),
        σ, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  have s3 : stepFnIter 2 σ
      (.exec qdStoreSeqn (qdEnvV D a)
        (.seq [] (qdEnvV D a) (.seq [] (qdEnv1 D) (qdLoopK D)))) ch
      = .ok (.exec (.assign
            (.addr (.indexAddr (.ref "dequeued") (.var "i"))) (.var "v"))
          (qdEnvV D a)
          (.seq [] (qdEnvV D a) (.seq [] (qdEnv1 D) (qdLoopK D))),
        σ, ch) := by
    have h := stepFnIter_splice_pop (σ := σ)
      (ss := #[.assign (.addr (.indexAddr (.ref "dequeued") (.var "i")))
        (.var "v")])
      (t := .assign (.addr (.indexAddr (.ref "dequeued") (.var "i")))
        (.var "v"))
      (ts := []) (rest := []) (env := qdEnvV D a)
      (k := .seq [] (qdEnv1 D) (qdLoopK D)) (ch := ch) rfl
    rw [show (qdStoreSeqn : Stmt)
      = .seqn #[.assign (.addr (.indexAddr (.ref "dequeued") (.var "i")))
          (.var "v")] from rfl]
    exact h
  have s4 : stepFnIter 3 σ
      (.exec (.assign
          (.addr (.indexAddr (.ref "dequeued") (.var "i"))) (.var "v"))
        (qdEnvV D a)
        (.seq [] (qdEnvV D a) (.seq [] (qdEnv1 D) (qdLoopK D)))) ch
      = .ok (.evalE (.var "i") (qdEnvV D a) (qdStIdxK D a), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3) s4

/-- Qd-b3: the index value delivered → the rhs `v` read. 1 step. -/
theorem qd_b3_raw (σ : ExecState) (D a : Nat) (jv : Int) (ch : Choices) :
    stepFnIter 1 σ (.retV (.int jv .uint64) (qdStIdxK D a)) ch
      = .ok (.evalE (.var "v") (qdEnvV D a) (qdStRhsK D a jv), σ, ch) := by
  with_unfolding_all rfl

/-- Qd-b5: the rhs value delivered → the `dequeued[i]` store point. 1
step. -/
theorem qd_b5_raw (σ : ExecState) (D a : Nat) (jv w : Int) (ch : Choices) :
    stepFnIter 1 σ (.retV (.int w .uint64) (qdStRhsK D a jv)) ch
      = .ok (.next (.storeK
            [.chain (.addr (.base ⟨D + 1⟩)) [.int jv .uint64] [.index]]
            [.int w .uint64] (.seqn #[]) (qdEnvV D a)
            (qdEndTail D a)), σ, ch) := by
  with_unfolding_all rfl

/-- Qd-t1: the `dequeued[i]` store drained → the loop cont. 4 steps. -/
theorem qd_t1_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.storeK [] [] (.seqn #[]) (qdEnvV D a) (qdEndTail D a))) ch
      = .ok (.next (qdLoopK D), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (qdEnvV D a) (qdEndTail D a))) ch
      = .ok (.exec (.seqn #[]) (qdEnvV D a) (qdEndTail D a), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 1 σ
      (.exec (.seqn #[]) (qdEnvV D a) (qdEndTail D a)) ch
      = .ok (.next (.seq [] (qdEnvV D a)
          (.seq [] (qdEnv1 D) (qdLoopK D))), σ, ch) := by
    have h := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := #[])
      (env := qdEnvV D a) (rest := [])
      (k := .seq [] (qdEnv1 D) (qdLoopK D)) (ch := ch))
    simpa [qdEndTail] using h
  have s3 : stepFnIter 1 σ
      (.next (.seq [] (qdEnvV D a) (.seq [] (qdEnv1 D) (qdLoopK D)))) ch
      = .ok (.next (.seq [] (qdEnv1 D) (qdLoopK D)), σ, ch) :=
    stepFnIter_one stepFn_seq_nil
  have s4 : stepFnIter 1 σ
      (.next (.seq [] (qdEnv1 D) (qdLoopK D))) ch
      = .ok (.next (qdLoopK D), σ, ch) :=
    stepFnIter_one stepFn_seq_nil
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3) s4

/-- Qd-t2: the loop cont → the `$forFirst` read. 7 steps. -/
theorem qd_t2_raw (σ : ExecState) (D : Nat) (ch : Choices) :
    stepFnIter 7 σ (.next (qdLoopK D)) ch
      = .ok (.evalE (.var "$forFirst") (qdEnv1 D) (qdFfK D), σ, ch) := by
  with_unfolding_all rfl

/-- Qd-t3: `$forFirst` false → the increment's `i` read. 5 steps. -/
theorem qd_t3_raw (σ : ExecState) (D : Nat) (ch : Choices) :
    stepFnIter 5 σ (.retV (.bool false) (qdFfK D)) ch
      = .ok (.evalE (.var "i") (qdEnv1 D)
          (.strictK .add [] [.intLit 1 .uint64] (qdEnv1 D)
            (qdIncRhsK D)), σ, ch) := by
  with_unfolding_all rfl

/-- Qd-t4: the `i` value delivered → the incremented store point (the
add's normalization spelled symbolically). 4 steps. -/
theorem qd_t4_raw (σ : ExecState) (D : Nat) (jv : Int) (ch : Choices) :
    stepFnIter 4 σ (.retV (.int jv .uint64)
      (.strictK .add [] [.intLit 1 .uint64] (qdEnv1 D) (qdIncRhsK D))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨D + 2⟩)) [] []]
            [.int (IntKind.normalize .uint64 (jv + 1)) .uint64]
            (.seqn #[]) (qdEnv1 D) (qdIncTail D)), σ, ch) := by
  with_unfolding_all rfl

/-- Qd-t5: the increment store drained → the exit test's `i` read. 7
steps. -/
theorem qd_t5_raw (σ : ExecState) (D : Nat) (ch : Choices) :
    stepFnIter 7 σ
      (.next (.storeK [] [] (.seqn #[]) (qdEnv1 D) (qdIncTail D))) ch
      = .ok (.evalE (.var "i") (qdEnv1 D) (qdTestK D), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (qdEnv1 D) (qdIncTail D))) ch
      = .ok (.exec (.seqn #[]) (qdEnv1 D) (qdIncTail D), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 2 σ
      (.exec (.seqn #[]) (qdEnv1 D) (qdIncTail D)) ch
      = .ok (.exec (.seqn #[]) (qdEnv1 D)
          (.seq [.ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
            .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D)), σ, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  have s3 : stepFnIter 2 σ
      (.exec (.seqn #[]) (qdEnv1 D)
        (.seq [.ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
          .breakStmt, qdFill] (qdEnv1 D) (qdLoopK D))) ch
      = .ok (.exec (.ifThenElse (.lessCmp (.var "i") (.var "d"))
            (.seqn #[]) .breakStmt) (qdEnv1 D)
          (.seq [qdFill] (qdEnv1 D) (qdLoopK D)), σ, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  have s4 : stepFnIter 2 σ
      (.exec (.ifThenElse (.lessCmp (.var "i") (.var "d")) (.seqn #[])
        .breakStmt) (qdEnv1 D)
        (.seq [qdFill] (qdEnv1 D) (qdLoopK D))) ch
      = .ok (.evalE (.var "i") (qdEnv1 D) (qdTestK D), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3) s4

/-- Qd-t6: the test's `i` value delivered → the `d` read. 1 step. -/
theorem qd_t6_raw (σ : ExecState) (D : Nat) (iv : Int) (ch : Choices) :
    stepFnIter 1 σ (.retV (.int iv .uint64) (qdTestK D)) ch
      = .ok (.evalE (.var "d") (qdEnv1 D)
          (.strictK .lessCmp [.int iv .uint64] [] (qdEnv1 D)
            (qdCmpK D)), σ, ch) := by
  with_unfolding_all rfl

/-- Qd-t7: the `d` value delivered → the comparison's delivery. 1
step. -/
theorem qd_t7_raw (σ : ExecState) (D : Nat) (iv dv : Int) (ch : Choices) :
    stepFnIter 1 σ (.retV (.int dv .uint64)
      (.strictK .lessCmp [.int iv .uint64] [] (qdEnv1 D) (qdCmpK D))) ch
      = .ok (.retV (.bool (decide (iv < dv))) (qdCmpK D), σ, ch) := by
  with_unfolding_all rfl

/-- One dequeue iteration: EXACTLY 117 steps — the `q[0]` read off the
untouched backing at the moving offset, the `q[1:]` re-slice, the two
result stores, the write-backs, the `dequeued[i]` store, and the
incremented dispatch. Choice-free. -/
theorem qd_iter (σ : ExecState) (n seed k' : Nat) (j m : Nat)
    (B C : Nat) (mid : Heap) (D : Nat) (rest : Heap) (na : Nat)
    (ch : Choices)
    (hfn : findFunctionIn? σ.functions ⟨"dequeue"⟩ = some dequeueFunc)
    (hm : σ.methods = #[])
    (hjm : j < m) (hmn : m ≤ n) (hn8 : n ≤ 8) (hnC : n ≤ C)
    (h12 : 12 ≤ D) (hDna : D + 4 ≤ na) (hB12 : 12 ≤ B)
    (hmid : DeadFrom mid D)
    (hB : Heap.lookup mid (.base ⟨B⟩)
      = some (arrCellU C (qBack C n seed)))
    (hrest : DeadFrom rest na) :
    stepFnIter 117
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D
        ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest na)
      (.retV (.bool true) (qdCmpK D)) ch
      = .ok (.retV (.bool (decide
            (((j + 1 : Nat) : Int) < ((m : Nat) : Int)))) (qdCmpK D),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
            ((k' : Nat) : Int)
            (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
            mid D ((m : Nat) : Int) (qPre (j + 1) seed)
            ((j + 1 : Nat) : Int) false
            (rest ++ [(.base ⟨na⟩,
                u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
              (.base ⟨na + 2⟩,
                slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
              (.base ⟨na + 3⟩,
                u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
              (.base ⟨na + 4⟩,
                u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])
            (na + 5), ch) := by
  have hwj : (0 : Int) ≤ (((seed + j) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + j) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + j) (y := 2 ^ 64) (by omega)
    omega
  -- i1 (7): test true → the harness `v` initialization
  have i1 : stepFnIter 7
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false rest na)
      (.retV (.bool true) (qdCmpK D)) ch
      = .ok (.exec (.initialization { id := "v", typ := tU64 })
          (qdEnv2 D)
          (.seq [qdCallSeqn, qdStoreSeqn] (qdEnv2 D)
            (.seq [] (qdEnv1 D) (qdLoopK D))),
        qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
          (qPre j seed) ((j : Nat) : Int) false rest na, ch) := by
    have a1 : stepFnIter 1
        (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          (qslV B j (n - j) (C - j)) (qPre n seed) mid D
          ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest na)
        (.retV (.bool true) (qdCmpK D)) ch
        = .ok (.exec (.seqn #[]) (qdEnv1 D)
            (.seq [qdFill] (qdEnv1 D) (qdLoopK D)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            (qslV B j (n - j) (C - j)) (qPre n seed) mid D
            ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
            na, ch) := by
      with_unfolding_all rfl
    have a2 : stepFnIter 2
        (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          (qslV B j (n - j) (C - j)) (qPre n seed) mid D
          ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest na)
        (.exec (.seqn #[]) (qdEnv1 D)
          (.seq [qdFill] (qdEnv1 D) (qdLoopK D))) ch
        = .ok (.exec qdFill (qdEnv1 D)
            (.seq [] (qdEnv1 D) (qdLoopK D)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            (qslV B j (n - j) (C - j)) (qPre n seed) mid D
            ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
            na, ch) :=
      stepFnIter_splice_pop (ss := #[]) rfl
    have a3 : stepFnIter 2
        (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          (qslV B j (n - j) (C - j)) (qPre n seed) mid D
          ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest na)
        (.exec qdFill (qdEnv1 D) (.seq [] (qdEnv1 D) (qdLoopK D))) ch
        = .ok (.exec qdVSeqn (qdEnv2 D)
            (.seq [qdCallSeqn, qdStoreSeqn] (qdEnv2 D)
              (.seq [] (qdEnv1 D) (qdLoopK D))),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            (qslV B j (n - j) (C - j)) (qPre n seed) mid D
            ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
            na, ch) := by
      have h := stepFnIter_block_pop
        (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed) mid
          D ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
          na)
        (ss := #[qdVSeqn, qdCallSeqn, qdStoreSeqn]) (env := qdEnv1 D)
        (k := .seq [] (qdEnv1 D) (qdLoopK D)) (ch := ch) rfl
      rw [show (qdFill : Stmt)
        = .block #[] #[qdVSeqn, qdCallSeqn, qdStoreSeqn] from rfl]
      exact h
    have a4 : stepFnIter 2
        (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          (qslV B j (n - j) (C - j)) (qPre n seed) mid D
          ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest na)
        (.exec qdVSeqn (qdEnv2 D)
          (.seq [qdCallSeqn, qdStoreSeqn] (qdEnv2 D)
            (.seq [] (qdEnv1 D) (qdLoopK D)))) ch
        = .ok (.exec (.initialization { id := "v", typ := tU64 })
            (qdEnv2 D)
            (.seq [qdCallSeqn, qdStoreSeqn] (qdEnv2 D)
              (.seq [] (qdEnv1 D) (qdLoopK D))),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            (qslV B j (n - j) (C - j)) (qPre n seed) mid D
            ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
            na, ch) := by
      have h := stepFnIter_splice_pop
        (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed) mid
          D ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
          na)
        (ss := #[.initialization { id := "v", typ := tU64 }])
        (t := .initialization { id := "v", typ := tU64 })
        (ts := [qdCallSeqn, qdStoreSeqn])
        (rest := [qdCallSeqn, qdStoreSeqn]) (env := qdEnv2 D)
        (k := .seq [] (qdEnv1 D) (qdLoopK D)) (ch := ch) rfl
      rw [show (qdVSeqn : Stmt)
        = .seqn #[.initialization { id := "v", typ := tU64 }] from rfl]
      exact h
    have h := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain a1 a2)
      a3) a4
    rw [show (1 : Nat) + 2 + 2 + 2 = 7 from by omega] at h
    exact h
  -- deadness of the full dequeue heap at `na`
  have hCellsDead : DeadFrom
      (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
        ((j : Nat) : Int) false ++ rest)) na := by
    intro x hx
    rw [lookup_append_right (hmid _ (by omega)), qdCells]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega : D ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 3 ≠ x))]
    exact hrest _ hx
  -- alloc harness v (1)
  have i2 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false rest na)
      (.exec (.initialization { id := "v", typ := tU64 }) (qdEnv2 D)
        (.seq [qdCallSeqn, qdStoreSeqn] (qdEnv2 D)
          (.seq [] (qdEnv1 D) (qdLoopK D)))) ch
      = .ok (.next (.seq [qdCallSeqn, qdStoreSeqn] (qdEnvV D na)
            (.seq [] (qdEnv1 D) (qdLoopK D))),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            (qslV B j (n - j) (C - j)) (qPre n seed) mid D
            ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false
            (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch) := by
    have h := stepFnIter_one (stepFn_init_seq
      (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
        ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed) mid D
        ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest na)
      (p := { id := "v", typ := tU64 })
      (rest := [qdCallSeqn, qdStoreSeqn]) (env := qdEnv2 D)
      (k := .seq [] (qdEnv1 D) (qdLoopK D)) (ch := ch)
      (hdef := by with_unfolding_all rfl))
    rw [show LocalEnv.declare (qdEnv2 D) "v"
        (.base ⟨(qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed) mid
          D ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
          na).nextAddr⟩) = qdEnvV D na from rfl] at h
    rw [show Heap.set (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
        ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed) mid D
        ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
        na).heap
        (.base ⟨(qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed) mid
          D ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false rest
          na).nextAddr⟩)
        ⟨some tU64, .int 0 .uint64⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
          ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
            ((j : Nat) : Int) false
            ++ (rest ++ [(.base ⟨na⟩, u64cell 0)]))) from by
        rw [show (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
            ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed)
            mid D ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false
            rest na).heap
          = qFront ((n : Nat) : Int) ((seed : Nat) : Int)
              ((k' : Nat) : Int) zeros8 zeros8 0
              (qslV B j (n - j) (C - j)) (qPre n seed) ((n : Nat) : Int)
              false
              ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
                ((j : Nat) : Int) false ++ rest)) from rfl,
          set_fresh ((qHeap_dead (by omega) hCellsDead) _
            (Nat.le_refl _))]
        simp [List.append_assoc]] at h
    exact h
  -- generic deadness of the mid + cells + tail package
  have hMidCells : ∀ (dv' : Int) (lD' : List Int) (jv' : Int) (ff' : Bool)
      (rest' : Heap) (na' : Nat), D + 4 ≤ na' → DeadFrom rest' na' →
      DeadFrom (mid ++ (qdCells D dv' lD' jv' ff' ++ rest')) na' := by
    intro dv' lD' jv' ff' rest' na' hna' hr' x hx
    rw [lookup_append_right (hmid _ (by omega)), qdCells]
    simp only [List.cons_append, List.nil_append]
    rw [lookup_cons_ne (base_beq_false (by omega : D ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 3 ≠ x))]
    exact hr' _ hx
  have hqdMiss : ∀ (dv' : Int) (lD' : List Int) (jv' : Int) (ff' : Bool)
      (x : Nat), D + 4 ≤ x →
      Heap.lookup (qdCells D dv' lD' jv' ff') (.base ⟨x⟩) = none := by
    intro dv' lD' jv' ff' x hx
    rw [qdCells,
      lookup_cons_ne (base_beq_false (by omega : D ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : D + 3 ≠ x))]
    rfl
  -- g3: the popped call seqn → the `q` read (4)
  have g3 := qd_call_raw
    (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
      (qPre j seed) ((j : Nat) : Int) false
      (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1)) D na ch
  -- g4: the `q` argument read (1)
  have g4 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
      (.evalE (.var "q") (qdEnvV D na) (qdCallArgsK D na)) ch
      = .ok (.retV (qslV B j (n - j) (C - j)) (qdCallArgsK D na),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            (qslV B j (n - j) (C - j)) (qPre n seed) mid D
            ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false
            (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch) :=
    stepFnIter_one (stepFn_var
      (c := slCell (qslV B j (n - j) (C - j))) rfl rfl)
  -- g5: the frame entry (1)
  have hd1 : DeadFrom (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1) :=
    hrest.push
  have hEnter := qdeq_enterFrame (σ := σ)
    (H := qFront ((n : Nat) : Int) ((seed : Nat) : Int)
        ((k' : Nat) : Int) zeros8 zeros8 0 (qslV B j (n - j) (C - j))
        (qPre n seed) ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
        ((j : Nat) : Int) false ++ (rest ++ [(.base ⟨na⟩, u64cell 0)]))))
    (na := na + 1) (qv := qslV B j (n - j) (C - j)) hfn hm
    (qHeap_dead (by omega)
      (hMidCells _ _ _ _ _ _ (by omega) hd1))
  rw [show na + 1 + 1 = na + 2 from rfl,
    show na + 1 + 2 = na + 3 from rfl] at hEnter
  have g5 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
      (.retV (qslV B j (n - j) (C - j)) (qdCallArgsK D na)) ch
      = .ok (.exec dequeueFunc.body (dqcEnv na) (qdFrameK D na),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            (qslV B j (n - j) (C - j)) (qPre n seed) mid D
            ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int) false
            (rest ++ [(.base ⟨na⟩, u64cell 0),
              (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
              (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
              (.base ⟨na + 3⟩, u64cell 0)]) (na + 4), ch) := by
    have h := stepFnIter_one (stepFn_call_enter (vals := [])
      (v := qslV B j (n - j) (C - j)) (plans := qdPlans)
      (env := qdEnvV D na) (k := qdAfterCallK D na)
      (ch := ch) hEnter)
    rw [show ((qFront ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) zeros8 zeros8 0 (qslV B j (n - j) (C - j))
          (qPre n seed) ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0)]))))
        ++ [(.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 3⟩, u64cell 0)] : Heap)
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
          ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
            (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 3⟩, u64cell 0)]))) from by
      simp [List.append_assoc]] at h
    exact h
  -- g6: the whole callee (49)
  have hrest2d : DeadFrom (rest ++ [(.base ⟨na⟩, u64cell 0),
      (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
      (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
      (.base ⟨na + 3⟩, u64cell 0)]) (na + 4) := by
    intro x hx
    rw [lookup_append_right (hrest _ (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
      lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x))]
    rfl
  have hBfull : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
        ((j : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
          (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
          (.base ⟨na + 3⟩, u64cell 0)])))) (.base ⟨B⟩)
      = some ⟨some (.array ((qBack C n seed).length) tU64),
          .array ⟨(qBack C n seed).map (fun v => .int v .uint64)⟩⟩ := by
    have hBcell : (arrCellU C (qBack C n seed) : HeapCell)
        = ⟨some (.array ((qBack C n seed).length) tU64),
            .array ⟨(qBack C n seed).map (fun v => .int v .uint64)⟩⟩ := by
      rw [arrCellU, qBack_length hnC]
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_left hB, hBcell]
  have hlkRest : ∀ (x : Nat) (c : HeapCell), na ≤ x →
      Heap.lookup [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 3⟩, u64cell 0)] (.base ⟨x⟩) = some c →
      Heap.lookup
        (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
          ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
            (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 3⟩, u64cell 0)])))) (.base ⟨x⟩) = some c := by
    intro x c hx hlit
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (hmid _ (by omega)),
      lookup_append_right (hqdMiss _ _ _ _ _ (by omega)),
      lookup_append_right (hrest _ (by omega))]
    exact hlit
  have hq1full : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 3⟩, u64cell 0)])))) (.base ⟨na + 1⟩)
      = some (slCell (qslV B j (n - j) (C - j))) :=
    hlkRest _ _ (by omega) (by
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
      simp [Heap.lookup])
  have hr0full : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 3⟩, u64cell 0)])))) (.base ⟨na + 2⟩)
      = some (slCell (.slice ⟨none, 0, 0, 0⟩)) :=
    hlkRest _ _ (by omega) (by
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
      simp [Heap.lookup])
  have hr1full : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 3⟩, u64cell 0)])))) (.base ⟨na + 3⟩)
      = some (u64cell 0) :=
    hlkRest _ _ (by omega) (by
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 3)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 3)),
        lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 3))]
      simp [Heap.lookup])
  have hdeadfull : DeadFrom
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 3⟩, u64cell 0)])))) (na + 4) :=
    qHeap_dead (by omega) (hMidCells _ _ _ _ _ _ (by omega) hrest2d)
  have hlen1j : 1 ≤ n - j := by omega
  have hcapj : n - j ≤ C - j := by omega
  have hoffj : j + (n - j) ≤ (qBack C n seed).length := by
    rw [qBack_length hnC]; omega
  have hgetwj : (qBack C n seed).getD j 0
      = (((seed + j) % 2 ^ 64 : Nat) : Int) := qBack_getD (by omega)
  have hcallee := qd_callee σ
    (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
        (.base ⟨na + 3⟩, u64cell 0)]))))
    D na B j (n - j) (C - j) (qBack C n seed)
    (((seed + j) % 2 ^ 64 : Nat) : Int) ch
    hlen1j hcapj hBfull hoffj hgetwj hq1full hr0full hr1full hdeadfull hwj
  rw [show (n - j) - 1 = n - (j + 1) from by omega,
    show (C - j) - 1 = C - (j + 1) from by omega] at hcallee
  -- normalize the callee's result heap into the qStD shape
  have hheap3 : Heap.set (Heap.set
      ((qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
          ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
            (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 3⟩, u64cell 0)]))))
        ++ [(.base ⟨na + 4⟩,
            u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])
      (.base ⟨na + 2⟩)
      (slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))))
      (.base ⟨na + 3⟩)
      (u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
          ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
            (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩,
              slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
            (.base ⟨na + 3⟩,
              u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 4⟩,
              u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))) := by
    rw [show ((qFront ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) zeros8 zeros8 0 (qslV B j (n - j) (C - j))
          (qPre n seed) ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
            (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 3⟩, u64cell 0)]))))
        ++ [(.base ⟨na + 4⟩,
            u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))] : Heap)
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
          ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
            (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩, slCell (.slice ⟨none, 0, 0, 0⟩)),
            (.base ⟨na + 3⟩, u64cell 0),
            (.base ⟨na + 4⟩,
              u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))) from by
      simp [List.append_assoc]]
    rw [set_append_right (qFront_miss (by omega)),
      set_append_right (hmid _ (by omega)),
      set_append_right (hqdMiss _ _ _ _ _ (by omega)),
      set_append_right (hrest _ (by omega))]
    rw [set_append_right (qFront_miss (by omega)),
      set_append_right (hmid _ (by omega)),
      set_append_right (hqdMiss _ _ _ _ _ (by omega)),
      set_append_right (hrest _ (by omega))]
    congr 1
    congr 1
    congr 1
    congr 1
    simp [Heap.set,
      base_beq_false (by omega : na ≠ na + 2),
      base_beq_false (by omega : na + 1 ≠ na + 2),
      base_beq_false (by omega : na ≠ na + 3),
      base_beq_false (by omega : na + 1 ≠ na + 3),
      base_beq_false (by omega : na + 2 ≠ na + 3)]
  rw [hheap3] at hcallee
  -- generic lookup/set carriers through the fixed front + mid + cells
  have hlkG : ∀ (qv' : GoValue) (lD' : List Int) (jv' : Int) (ff' : Bool)
      (T : Heap) (x : Nat) (c : HeapCell), na ≤ x →
      Heap.lookup T (.base ⟨x⟩) = some c →
      Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) zeros8 zeros8 0 qv' (qPre n seed)
          ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) lD' jv' ff'
          ++ (rest ++ T)))) (.base ⟨x⟩) = some c := by
    intro qv' lD' jv' ff' T x c hx hlit
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (hmid _ (by omega)),
      lookup_append_right (hqdMiss _ _ _ _ _ (by omega)),
      lookup_append_right (hrest _ (by omega))]
    exact hlit
  have hsetG : ∀ (qv' : GoValue) (lD' : List Int) (jv' : Int) (ff' : Bool)
      (T T' : Heap) (x : Nat) (c : HeapCell), na ≤ x →
      Heap.set T (.base ⟨x⟩) c = T' →
      Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k' : Nat) : Int) zeros8 zeros8 0 qv' (qPre n seed)
          ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) lD' jv' ff'
          ++ (rest ++ T)))) (.base ⟨x⟩) c
        = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
            zeros8 zeros8 0 qv' (qPre n seed) ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) lD' jv' ff'
            ++ (rest ++ T'))) := by
    intro qv' lD' jv' ff' T T' x c hx hset
    rw [set_append_right (qFront_miss (by omega)),
      set_append_right (hmid _ (by omega)),
      set_append_right (hqdMiss _ _ _ _ _ (by omega)),
      set_append_right (hrest _ (by omega)), hset]
  -- g7: the frame return + result loads (1)
  have hload : loadMany
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      [.base ⟨na + 2⟩, .base ⟨na + 3⟩]
      = .ok [qslV B (j + 1) (n - (j + 1)) (C - (j + 1)), .int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64] := by
    refine loadMany_two (c := slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))) (d := u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)) ?_ ?_
    · show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
      ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨na + 2⟩) = _
      refine hlkG _ _ _ _ _ _ _ (by omega) ?_
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
      simp [Heap.lookup]
    · show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B j (n - j) (C - j)) (qPre n seed)
      ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨na + 3⟩) = _
      refine hlkG _ _ _ _ _ _ _ (by omega) ?_
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 3)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 3)),
        lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ na + 3))]
      simp [Heap.lookup]
  have g7 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.returning (qdFrameK D na)) ch
      = .ok (.evalE (.ref "q") (qdEnvV D na) (qdWbK1 D na (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (((seed + j) % 2 ^ 64 : Nat) : Int)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) :=
    stepFnIter_one (stepFn_return_frame hload)
  -- g8: the two target resolutions (4)
  have g8 := qd_wb2_raw
    (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D na (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (((seed + j) % 2 ^ 64 : Nat) : Int) ch
  -- g9: the `q` write-back store through the concrete front cell (1)
  have hstq : storeTarget
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.chain (.addr (.base ⟨8⟩)) [] []) (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
            ((j : Nat) : Int) false
            ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (na + 5)) := by
    have h := storeTarget_addr
      (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (a := ⟨8⟩) (ty := sliceU) (old := qslV B j (n - j) (C - j)) (v := qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))
      rfl (normVal_slice _ _)
    rw [show Heap.set
        ((qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) : ExecState).heap
        (.base ⟨8⟩) ⟨some sliceU, qslV B (j + 1) (n - (j + 1)) (C - (j + 1))⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
            ((j : Nat) : Int) false
            ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))) from rfl] at h
    exact h
  have g9 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.next (.storeK
        [.chain (.addr (.base ⟨8⟩)) [] [],
         .chain (.addr (.base ⟨na⟩)) [] []]
        [qslV B (j + 1) (n - (j + 1)) (C - (j + 1)), .int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64] (.seqn #[]) (qdEnvV D na)
        (qdAfterCallK D na))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64] (.seqn #[]) (qdEnvV D na)
            (qdAfterCallK D na)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) :=
    stepFnIter_one (stepFn_store_step hstq)
  -- g10: the `v` write-back store at the symbolic cell (1)
  have hstv : storeTarget
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.chain (.addr (.base ⟨na⟩)) [] []) (.int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64)
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
            ((j : Nat) : Int) false
            ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (na + 5)) := by
    have hlk : Heap.lookup
        ((qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) : ExecState).heap
        (.base ⟨na⟩) = some (u64cell 0) := by
      show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨na⟩) = _
      refine hlkG _ _ _ _ _ _ _ (by omega) ?_
      simp [Heap.lookup]
    have h := storeTarget_addr hlk (normVal_u64 _ hwj.1 hwj.2)
    rw [show Heap.set
        ((qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) : ExecState).heap
        (.base ⟨na⟩) ⟨some tU64, .int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
            ((j : Nat) : Int) false
            ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))) from by
      show Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨na⟩) _ = _
      refine hsetG _ _ _ _ _ _ _ _ (by omega) ?_
      simp [Heap.set]] at h
    exact h
  have g10 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell 0),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64] (.seqn #[]) (qdEnvV D na)
        (qdAfterCallK D na))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qdEnvV D na)
            (qdAfterCallK D na)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) :=
    stepFnIter_one (stepFn_store_step hstv)
  -- g11..g15: the `dequeued[i]` store block's reads (8 + 1 + 1 + 1 + 1)
  have g11 := qd_b1_raw
    (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D na ch
  have g12 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.evalE (.var "i") (qdEnvV D na) (qdStIdxK D na)) ch
      = .ok (.retV (.int ((j : Nat) : Int) .uint64) (qdStIdxK D na),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell ((j : Nat) : Int))
      rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
        ((j : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D + 2⟩) = _
    exact qdCells_lookup h12 hmid (by
      rw [qdCells,
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 2)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 2))]
      simp [Heap.lookup])
  have g13 := qd_b3_raw
    (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D na ((j : Nat) : Int) ch
  have g14 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.evalE (.var "v") (qdEnvV D na)
        (qdStRhsK D na ((j : Nat) : Int))) ch
      = .ok (.retV (.int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64)
            (qdStRhsK D na ((j : Nat) : Int)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)) rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
        ((j : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨na⟩) = _
    refine hlkG _ _ _ _ _ _ _ (by omega) ?_
    simp [Heap.lookup]
  have g15 := qd_b5_raw
    (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D na ((j : Nat) : Int) (((seed + j) % 2 ^ 64 : Nat) : Int) ch
  -- g16: the `dequeued[i]` store itself (1)
  have hilen : j < (qPre j seed).length := by
    rw [qPre_length (by omega)]; omega
  have hlen8 : (qPre j seed).length = 8 := qPre_length (by omega)
  have hrangej : ∀ v ∈ qPre j seed, 0 ≤ v ∧ v < 2 ^ 64 := qPre_range
  have hlkdq : Heap.lookup
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D + 1⟩)
      = some (arrCellU 8 (qPre j seed)) :=
    qdCells_lookup h12 hmid (by
      rw [qdCells,
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 1))]
      simp [Heap.lookup])
  have keyStore : ∀ (H : Heap),
      Heap.lookup H (.base ⟨D + 1⟩)
        = some (arrCellU 8 (qPre j seed)) →
      storeTarget (qSt σ H (na + 5))
          (.chain (.addr (.base ⟨D + 1⟩))
            [.int ((j : Nat) : Int) .uint64] [.index])
          (.int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64)
        = .ok (qSt σ (Heap.set H (.base ⟨D + 1⟩)
            (arrCellU 8 ((qPre j seed).set j (((seed + j) % 2 ^ 64 : Nat) : Int)))) (na + 5)) := by
    intro H h
    exact storeTarget_arrayLocal_u64 (σ := qSt σ H (na + 5))
      (a := ⟨D + 1⟩) (N := 8) (i := j) (ik := .uint64)
      (l := qPre j seed) (w := (((seed + j) % 2 ^ 64 : Nat) : Int)) h hilen hlen8 hrangej hwj
  have hstdq := keyStore
    (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))))
    hlkdq
  rw [qPre_set (by omega : j < 8)] at hstdq
  rw [show Heap.set
      (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre j seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))))
      (.base ⟨D + 1⟩) (arrCellU 8 (qPre (j + 1) seed))
    = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
    ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
      ((j : Nat) : Int) false
      ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))) from by
    refine qdCells_set (j := 1) h12 hmid ?_ ?_
    · rw [qdCells, qdCells]
      simp [Heap.set, base_beq_false (by omega : D ≠ D + 1)]
    · exact ⟨arrCellU 8 (qPre j seed), by
        rw [qdCells,
          lookup_cons_ne (base_beq_false (by omega : D ≠ D + 1))]
        simp [Heap.lookup]⟩] at hstdq
  have g16 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre j seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.next (.storeK
        [.chain (.addr (.base ⟨D + 1⟩))
          [.int ((j : Nat) : Int) .uint64] [.index]]
        [.int (((seed + j) % 2 ^ 64 : Nat) : Int) .uint64] (.seqn #[]) (qdEnvV D na)
        (qdEndTail D na))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qdEnvV D na)
            (qdEndTail D na)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) :=
    stepFnIter_one (stepFn_store_step hstdq)
  -- g17..g28: the 34-step loop tail
  have g17 := qd_t1_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D na ch
  have g18 := qd_t2_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D ch
  have g19 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.evalE (.var "$forFirst") (qdEnv1 D) (qdFfK D)) ch
      = .ok (.retV (.bool false) (qdFfK D),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) := by
    refine stepFnIter_one (stepFn_var (c := bcell false) rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
        ((j : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D + 3⟩) = _
    exact qdCells_lookup h12 hmid (by
      rw [qdCells,
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 3)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 3)),
        lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ D + 3))]
      simp [Heap.lookup])
  have g20 := qd_t3_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D ch
  have g21 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.evalE (.var "i") (qdEnv1 D)
        (.strictK .add [] [.intLit 1 .uint64] (qdEnv1 D)
          (qdIncRhsK D))) ch
      = .ok (.retV (.int ((j : Nat) : Int) .uint64)
            (.strictK .add [] [.intLit 1 .uint64] (qdEnv1 D)
              (qdIncRhsK D)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell ((j : Nat) : Int))
      rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
        ((j : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D + 2⟩) = _
    exact qdCells_lookup h12 hmid (by
      rw [qdCells,
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 2)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 2))]
      simp [Heap.lookup])
  have g22 := qd_t4_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D ((j : Nat) : Int) ch
  have hnj : IntKind.normalize .uint64 (((j : Nat) : Int) + 1)
      = ((j + 1 : Nat) : Int) := by
    rw [show (((j : Nat) : Int) + 1) = ((j + 1 : Nat) : Int) from by
      omega]
    exact unorm_nat_of_lt (by omega)
  rw [hnj] at g22
  -- g23: the `i` increment store (1)
  have hsti : storeTarget
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.chain (.addr (.base ⟨D + 2⟩)) [] [])
      (.int ((j + 1 : Nat) : Int) .uint64)
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
            ((j + 1 : Nat) : Int) false
            ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (na + 5)) := by
    have hlk : Heap.lookup
        ((qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) : ExecState).heap
        (.base ⟨D + 2⟩) = some (u64cell ((j : Nat) : Int)) := by
      show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D + 2⟩) = _
      exact qdCells_lookup h12 hmid (by
        rw [qdCells,
          lookup_cons_ne (base_beq_false (by omega : D ≠ D + 2)),
          lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 2))]
        simp [Heap.lookup])
    have hnp1 : (0 : Int) ≤ ((j + 1 : Nat) : Int) := by omega
    have hnp2 : ((j + 1 : Nat) : Int) < 2 ^ 64 := by
      exact_mod_cast (show j + 1 < 2 ^ 64 by omega)
    have h := storeTarget_addr hlk
      (normVal_u64 (w := ((j + 1 : Nat) : Int)) _ hnp1 hnp2)
    rw [show Heap.set
        ((qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) : ExecState).heap
        (.base ⟨D + 2⟩) ⟨some tU64, .int ((j + 1 : Nat) : Int) .uint64⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
          ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
            ((j + 1 : Nat) : Int) false
            ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]))) from by
      show Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
        ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
          ((j : Nat) : Int) false
          ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D + 2⟩) _ = _
      refine qdCells_set (j := 2) h12 hmid ?_ ?_
      · rw [qdCells, qdCells]
        simp [Heap.set, base_beq_false (by omega : D ≠ D + 2),
          base_beq_false (by omega : D + 1 ≠ D + 2)]
      · exact ⟨u64cell ((j : Nat) : Int), by
          rw [qdCells,
            lookup_cons_ne (base_beq_false (by omega : D ≠ D + 2)),
            lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 2))]
          simp [Heap.lookup]⟩] at h
    exact h
  have g23 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j : Nat) : Int) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.next (.storeK [.chain (.addr (.base ⟨D + 2⟩)) [] []]
        [.int ((j + 1 : Nat) : Int) .uint64] (.seqn #[]) (qdEnv1 D)
        (qdIncTail D))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qdEnv1 D)
            (qdIncTail D)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) :=
    stepFnIter_one (stepFn_store_step hsti)
  have g24 := qd_t5_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D ch
  have g25 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.evalE (.var "i") (qdEnv1 D) (qdTestK D)) ch
      = .ok (.retV (.int ((j + 1 : Nat) : Int) .uint64) (qdTestK D),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := u64cell ((j + 1 : Nat) : Int)) rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
        ((j + 1 : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D + 2⟩) = _
    exact qdCells_lookup h12 hmid (by
      rw [qdCells,
        lookup_cons_ne (base_beq_false (by omega : D ≠ D + 2)),
        lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ D + 2))]
      simp [Heap.lookup])
  have g26 := qd_t6_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D ((j + 1 : Nat) : Int) ch
  have g27 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5))
      (.evalE (.var "d") (qdEnv1 D)
        (.strictK .lessCmp [.int ((j + 1 : Nat) : Int) .uint64] []
          (qdEnv1 D) (qdCmpK D))) ch
      = .ok (.retV (.int ((m : Nat) : Int) .uint64)
            (.strictK .lessCmp [.int ((j + 1 : Nat) : Int) .uint64] []
              (qdEnv1 D) (qdCmpK D)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := u64cell ((m : Nat) : Int)) rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
      zeros8 zeros8 0 (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed)
      ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre (j + 1) seed)
        ((j + 1 : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])))) (.base ⟨D⟩) = _
    have hin : Heap.lookup (qdCells D ((m : Nat) : Int)
        (qPre (j + 1) seed) ((j + 1 : Nat) : Int) false)
        (.base ⟨D + 0⟩) = some (u64cell ((m : Nat) : Int)) := by
      rw [qdCells]
      simp [Heap.lookup]
    have h := qdCells_lookup (nv := ((n : Nat) : Int))
      (sv := ((seed : Nat) : Int)) (kv := ((k' : Nat) : Int))
      (qv := qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (lE := qPre n seed)
      (rest := rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])
      (j := 0) h12 hmid hin
    simpa using h
  have g28 := qd_t7_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B (j + 1) (n - (j + 1)) (C - (j + 1))) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre (j + 1) seed) (((j + 1 : Nat) : Int)) false
        (rest ++ [(.base ⟨na⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
        (.base ⟨na + 2⟩, slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
        (.base ⟨na + 3⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
        (.base ⟨na + 4⟩, u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5)) D ((j + 1 : Nat) : Int)
    ((m : Nat) : Int) ch
  -- the chain
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                  (stepFnIter_chain (stepFnIter_chain
                    (stepFnIter_chain i1 i2) g3) g4) g5) hcallee) g7)
                  g8) g9) g10) g11) g12) g13) g14) g15) g16) g17) g18)
                  g19) g20) g21) g22) g23) g24) g25) g26) g27) g28
  rw [show (7 : Nat) + 1 + 4 + 1 + 1 + 49 + 1 + 4 + 1 + 1 + 8 + 1 + 1
      + 1 + 1 + 1 + 4 + 7 + 1 + 5 + 1 + 4 + 1 + 7 + 1 + 1 + 1 + 1
      = 117 from by omega] at hall
  exact hall

/-- **The dequeue loop**: `117·(m−j)` steps from the exit test at `j`
to the exit test at `m` — choice-free, by induction over the counted
iterations. The five per-iteration cells accumulate existentially in
`rest'`; the backing in `mid` is read, never written. -/
theorem qd_loop (σ : ExecState) (n seed k' m : Nat) (B C : Nat)
    (mid : Heap) (D : Nat)
    (hfn : findFunctionIn? σ.functions ⟨"dequeue"⟩ = some dequeueFunc)
    (hm : σ.methods = #[])
    (hmn : m ≤ n) (hn8 : n ≤ 8) (hnC : n ≤ C) (h12 : 12 ≤ D)
    (hB12 : 12 ≤ B) (hmid : DeadFrom mid D)
    (hB : Heap.lookup mid (.base ⟨B⟩)
      = some (arrCellU C (qBack C n seed))) :
    ∀ j, j ≤ m → ∀ (rest : Heap) (na : Nat) (ch : Choices),
    D + 4 ≤ na → DeadFrom rest na →
    ∃ (rest' : Heap) (na' : Nat),
      stepFnIter (117 * (m - j))
        (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
          (qslV B j (n - j) (C - j)) (qPre n seed) mid D ((m : Nat) : Int)
          (qPre j seed) ((j : Nat) : Int) false rest na)
        (.retV (.bool (decide (((j : Nat) : Int) < ((m : Nat) : Int))))
          (qdCmpK D)) ch
        = .ok (.retV (.bool (decide
              (((m : Nat) : Int) < ((m : Nat) : Int)))) (qdCmpK D),
            qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
              ((k' : Nat) : Int) (qslV B m (n - m) (C - m)) (qPre n seed)
              mid D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int)
              false rest' na', ch)
      ∧ na ≤ na' ∧ D + 4 ≤ na' ∧ DeadFrom rest' na' := by
  suffices key : ∀ μ j, μ = m - j → j ≤ m →
      ∀ (rest : Heap) (na : Nat) (ch : Choices),
      D + 4 ≤ na → DeadFrom rest na →
      ∃ (rest' : Heap) (na' : Nat),
        stepFnIter (117 * (m - j))
          (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
            ((k' : Nat) : Int) (qslV B j (n - j) (C - j)) (qPre n seed)
            mid D ((m : Nat) : Int) (qPre j seed) ((j : Nat) : Int)
            false rest na)
          (.retV (.bool (decide (((j : Nat) : Int) < ((m : Nat) : Int))))
            (qdCmpK D)) ch
          = .ok (.retV (.bool (decide
                (((m : Nat) : Int) < ((m : Nat) : Int)))) (qdCmpK D),
              qStD σ ((n : Nat) : Int) ((seed : Nat) : Int)
                ((k' : Nat) : Int) (qslV B m (n - m) (C - m))
                (qPre n seed) mid D ((m : Nat) : Int) (qPre m seed)
                ((m : Nat) : Int) false rest' na', ch)
        ∧ na ≤ na' ∧ D + 4 ≤ na' ∧ DeadFrom rest' na' by
    intro j hj
    exact key (m - j) j rfl hj
  intro μ
  induction μ with
  | zero =>
      intro j hμ hj rest na ch hDna hrest
      have heq : j = m := by omega
      subst heq
      rw [Nat.sub_self, Nat.mul_zero]
      exact ⟨rest, na, rfl, Nat.le_refl _, hDna, hrest⟩
  | succ μ' ih =>
      intro j hμ hj rest na ch hDna hrest
      have hlt : j < m := by omega
      rw [show (decide (((j : Nat) : Int) < ((m : Nat) : Int))) = true
        from decide_eq_true (by exact_mod_cast hlt)]
      have hstep := qd_iter σ n seed k' j m B C mid D rest na ch hfn hm
        hlt hmn hn8 hnC h12 hDna hB12 hmid hB hrest
      have hrest5 : DeadFrom (rest ++ [(.base ⟨na⟩,
          u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
          (.base ⟨na + 2⟩,
            slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
          (.base ⟨na + 3⟩,
            u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
          (.base ⟨na + 4⟩,
            u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))]) (na + 5) := by
        intro x hx
        rw [lookup_append_right (hrest _ (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na + 4 ≠ x))]
        rfl
      obtain ⟨rest', na', hrestrun, hle', hD4', hdead'⟩ :=
        ih (j + 1) (by omega) (by omega)
          (rest ++ [(.base ⟨na⟩,
            u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 1⟩, slCell (qslV B j (n - j) (C - j))),
            (.base ⟨na + 2⟩,
              slCell (qslV B (j + 1) (n - (j + 1)) (C - (j + 1)))),
            (.base ⟨na + 3⟩,
              u64cell (((seed + j) % 2 ^ 64 : Nat) : Int)),
            (.base ⟨na + 4⟩,
              u64cell (((seed + j) % 2 ^ 64 : Nat) : Int))])
          (na + 5) ch (by omega) hrest5
      have hchain := stepFnIter_chain hstep hrestrun
      rw [show (117 : Nat) + 117 * (m - (j + 1)) = 117 * (m - j) from by
        have : m - j = (m - (j + 1)) + 1 := by omega
        rw [this, Nat.mul_succ]
        omega] at hchain
      exact ⟨rest', na', hchain, by omega, by omega, hdead'⟩

/-! ## The exit-epilogue continuations and helpers -/

/-- The epilogue env after `$c8` is declared at `a`. -/
def qxEnvC8 (D a : Nat) : LocalEnv :=
  [("$c8", .base ⟨a⟩) :: dqScope D, baseScope]

/-- The `qsize` callee frame env (params at `a+1`, `a+2`). -/
def qszEnv (a : Nat) : LocalEnv :=
  [[("$res0", .base ⟨a + 2⟩), ("q", .base ⟨a + 1⟩)]]

/-- The caller continuation after the `qsize` call. -/
def qxK10 (D a : Nat) : Cont := .seq [qT10] (qxEnvC8 D a) qStop

/-- The `qsize` call's frame continuation. -/
def qxFrameK (D a : Nat) : Cont :=
  .frame [(.chain [], [.ref "$c8"])] (qxEnvC8 D a) [.base ⟨a + 2⟩] []
    (qxK10 D a) false

/-- The four dequeue-loop cells miss every address from `D + 4` up. -/
theorem qdCells_miss {D : Nat} {dv : Int} {lD : List Int} {jv : Int}
    {ff : Bool} {x : Nat} (hx : D + 4 ≤ x) :
    Heap.lookup (qdCells D dv lD jv ff) (.base ⟨x⟩) = none := by
  rw [qdCells,
    lookup_cons_ne (base_beq_false (by omega : D ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : D + 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : D + 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : D + 3 ≠ x))]
  rfl

/-- Deadness of the mid + cells + tail package above the allocation
front. -/
theorem qdTail_dead {mid : Heap} {D : Nat} {dv : Int} {lD : List Int}
    {jv : Int} {ff : Bool} {rest : Heap} {na : Nat}
    (hmid : DeadFrom mid D) (hna : D + 4 ≤ na)
    (hrest : DeadFrom rest na) :
    DeadFrom (mid ++ (qdCells D dv lD jv ff ++ rest)) na := by
  intro x hx
  rw [lookup_append_right (hmid _ (by omega)),
    lookup_append_right (qdCells_miss (by omega))]
  exact hrest _ hx

/-! ## The epilogue raw segments -/

/-- Ex-e1: exit test false → the break unwind → `qT9`. 7 steps. -/
theorem qx2_e1_raw (σ : ExecState) (D : Nat) (ch : Choices) :
    stepFnIter 7 σ (.retV (.bool false) (qdCmpK D)) ch
      = .ok (.exec qT9 [dqScope D, baseScope]
          (.seq [qT10] [dqScope D, baseScope] qStop), σ, ch) := by
  with_unfolding_all rfl

/-- Ex-e4: the popped `$c8` call → the `q` argument read. 2 steps. -/
theorem qx2_e4_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 2 σ
      (.next (.seq [.call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"], qT10]
        (qxEnvC8 D a) qStop)) ch
      = .ok (.evalE (.var "q") (qxEnvC8 D a)
          (.callArgsK ⟨"qsize"⟩ [(.chain [], [.ref "$c8"])] [] []
            (qxEnvC8 D a) (qxK10 D a)), σ, ch) := by
  with_unfolding_all rfl

/-- Ex-e9: the callee's assign dispatched → its `q` read. 5 steps. -/
theorem qx2_e9_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.exec (.assign (.var "$res0")
          (.convert tU64 (.length (.var "q") (some sliceU))))
        ([] :: qszEnv a)
        (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a))) ch
      = .ok (.evalE (.var "q") ([] :: qszEnv a)
          (.strictK (.lengthOf (some sliceU)) [] [] ([] :: qszEnv a)
            (.strictK (.convert tU64) [] [] ([] :: qszEnv a)
              (.rhsK .vals [.chain (.addr (.base ⟨a + 2⟩)) [] []] [] []
                (.seqn #[]) ([] :: qszEnv a)
                (.seq [.returnStmt] ([] :: qszEnv a)
                  (qxFrameK D a))))), σ, ch) := by
  with_unfolding_all rfl

/-- Ex-e12: the length delivered → the converted store point. 2
steps. -/
theorem qx2_e12_raw (σ : ExecState) (D a : Nat) (L : Int) (ch : Choices) :
    stepFnIter 2 σ
      (.retV (.int L .int)
        (.strictK (.convert tU64) [] [] ([] :: qszEnv a)
          (.rhsK .vals [.chain (.addr (.base ⟨a + 2⟩)) [] []] [] []
            (.seqn #[]) ([] :: qszEnv a)
            (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 2⟩)) [] []]
            [.int (IntKind.normalize .uint64 L) .uint64] (.seqn #[])
            ([] :: qszEnv a)
            (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a))),
          σ, ch) := by
  with_unfolding_all rfl

/-- Ex-e14: the `$res0` store drained → the frame return. 5 steps. -/
theorem qx2_e14_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.next (.storeK [] [] (.seqn #[]) ([] :: qszEnv a)
        (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a)))) ch
      = .ok (.returning (qxFrameK D a), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) ([] :: qszEnv a)
        (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a)))) ch
      = .ok (.exec (.seqn #[]) ([] :: qszEnv a)
          (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a)), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 1 σ
      (.exec (.seqn #[]) ([] :: qszEnv a)
        (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a))) ch
      = .ok (.next (.seq [.returnStmt] ([] :: qszEnv a)
          (qxFrameK D a)), σ, ch) := by
    have h := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := #[])
      (env := [] :: qszEnv a) (rest := [.returnStmt])
      (k := qxFrameK D a) (ch := ch))
    simpa using h
  have s3 : stepFnIter 3 σ
      (.next (.seq [.returnStmt] ([] :: qszEnv a) (qxFrameK D a))) ch
      = .ok (.returning (qxFrameK D a), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain s1 s2) s3

/-- Ex-e16: the write-back target `.ref $c8` resolved → the store
point. 2 steps. -/
theorem qx2_e16_raw (σ : ExecState) (D a : Nat) (v : GoValue)
    (ch : Choices) :
    stepFnIter 2 σ
      (.evalE (.ref "$c8") (qxEnvC8 D a)
        (.tgtOpK (.chain []) [] [] [] [] .vals [] [v] (.seqn #[])
          (qxEnvC8 D a) (qxK10 D a))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a⟩)) [] []] [v]
            (.seqn #[]) (qxEnvC8 D a) (qxK10 D a)), σ, ch) := by
  with_unfolding_all rfl

/-- Ex-e18: the `$c8` write-back drained → the `$res0 = enqueued`
dispatch. 5 steps. -/
theorem qx2_e18_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 5 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a) (qxK10 D a))) ch
      = .ok (.exec (.assign (.var "$res0") (.var "enqueued"))
          (qxEnvC8 D a)
          (.seq [.assign (.var "$res1") (.var "dequeued"),
            .assign (.var "$res2") (.var "$c8"), .returnStmt]
            (qxEnvC8 D a) qStop), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a) (qxK10 D a))) ch
      = .ok (.exec (.seqn #[]) (qxEnvC8 D a) (qxK10 D a), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 1 σ
      (.exec (.seqn #[]) (qxEnvC8 D a) (qxK10 D a)) ch
      = .ok (.next (.seq [qT10] (qxEnvC8 D a) qStop), σ, ch) := by
    have h := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := #[])
      (env := qxEnvC8 D a) (rest := [qT10]) (k := qStop) (ch := ch))
    simpa [qxK10] using h
  have s3 : stepFnIter 1 σ
      (.next (.seq [qT10] (qxEnvC8 D a) qStop)) ch
      = .ok (.exec qT10 (qxEnvC8 D a)
          (.seq [] (qxEnvC8 D a) qStop), σ, ch) :=
    stepFnIter_one stepFn_seq_pop
  have s4 : stepFnIter 2 σ
      (.exec qT10 (qxEnvC8 D a) (.seq [] (qxEnvC8 D a) qStop)) ch
      = .ok (.exec (.assign (.var "$res0") (.var "enqueued"))
          (qxEnvC8 D a)
          (.seq [.assign (.var "$res1") (.var "dequeued"),
            .assign (.var "$res2") (.var "$c8"), .returnStmt]
            (qxEnvC8 D a) qStop), σ, ch) := by
    have h := stepFnIter_splice_pop (σ := σ)
      (ss := #[.assign (.var "$res0") (.var "enqueued"),
        .assign (.var "$res1") (.var "dequeued"),
        .assign (.var "$res2") (.var "$c8"), .returnStmt])
      (t := .assign (.var "$res0") (.var "enqueued"))
      (ts := [.assign (.var "$res1") (.var "dequeued"),
        .assign (.var "$res2") (.var "$c8"), .returnStmt])
      (rest := []) (env := qxEnvC8 D a) (k := qStop) (ch := ch) rfl
    rw [show (qT10 : Stmt)
      = .seqn #[.assign (.var "$res0") (.var "enqueued"),
          .assign (.var "$res1") (.var "dequeued"),
          .assign (.var "$res2") (.var "$c8"), .returnStmt] from rfl]
    exact h
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain s1 s2) s3) s4

/-- Ex-e19: the `$res0 = enqueued` dispatch → the `enqueued` read. 3
steps. -/
theorem qx2_e19_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 3 σ
      (.exec (.assign (.var "$res0") (.var "enqueued")) (qxEnvC8 D a)
        (.seq [.assign (.var "$res1") (.var "dequeued"),
          .assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop)) ch
      = .ok (.evalE (.var "enqueued") (qxEnvC8 D a)
          (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
            (.seqn #[]) (qxEnvC8 D a)
            (.seq [.assign (.var "$res1") (.var "dequeued"),
              .assign (.var "$res2") (.var "$c8"), .returnStmt]
              (qxEnvC8 D a) qStop)), σ, ch) := by
  with_unfolding_all rfl

/-- Ex-e21: a delivered rhs value at a plain-address store spine → the
store point. 1 step. -/
theorem qx2_e21_raw (σ : ExecState) (v : GoValue) (b : Nat)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFnIter 1 σ
      (.retV v (.rhsK .vals [.chain (.addr (.base ⟨b⟩)) [] []] [] []
        (.seqn #[]) env k)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨b⟩)) [] []] [v]
            (.seqn #[]) env k), σ, ch) := by
  with_unfolding_all rfl

/-- Ex-e23: the `$res0` store drained → the `dequeued` read. 6
steps. -/
theorem qx2_e23_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 6 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a)
        (.seq [.assign (.var "$res1") (.var "dequeued"),
          .assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop))) ch
      = .ok (.evalE (.var "dequeued") (qxEnvC8 D a)
          (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
            (.seqn #[]) (qxEnvC8 D a)
            (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
              (qxEnvC8 D a) qStop)), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a)
        (.seq [.assign (.var "$res1") (.var "dequeued"),
          .assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop))) ch
      = .ok (.exec (.seqn #[]) (qxEnvC8 D a)
          (.seq [.assign (.var "$res1") (.var "dequeued"),
            .assign (.var "$res2") (.var "$c8"), .returnStmt]
            (qxEnvC8 D a) qStop), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 2 σ
      (.exec (.seqn #[]) (qxEnvC8 D a)
        (.seq [.assign (.var "$res1") (.var "dequeued"),
          .assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop)) ch
      = .ok (.exec (.assign (.var "$res1") (.var "dequeued"))
          (qxEnvC8 D a)
          (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
            (qxEnvC8 D a) qStop), σ, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  have s3 : stepFnIter 3 σ
      (.exec (.assign (.var "$res1") (.var "dequeued")) (qxEnvC8 D a)
        (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop)) ch
      = .ok (.evalE (.var "dequeued") (qxEnvC8 D a)
          (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
            (.seqn #[]) (qxEnvC8 D a)
            (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
              (qxEnvC8 D a) qStop)), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain s1 s2) s3

/-- Ex-e27: the `$res1` store drained → the `$c8` read. 6 steps. -/
theorem qx2_e27_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 6 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a)
        (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop))) ch
      = .ok (.evalE (.var "$c8") (qxEnvC8 D a)
          (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
            (.seqn #[]) (qxEnvC8 D a)
            (.seq [.returnStmt] (qxEnvC8 D a) qStop)), σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a)
        (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop))) ch
      = .ok (.exec (.seqn #[]) (qxEnvC8 D a)
          (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
            (qxEnvC8 D a) qStop), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 2 σ
      (.exec (.seqn #[]) (qxEnvC8 D a)
        (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D a) qStop)) ch
      = .ok (.exec (.assign (.var "$res2") (.var "$c8")) (qxEnvC8 D a)
          (.seq [.returnStmt] (qxEnvC8 D a) qStop), σ, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  have s3 : stepFnIter 3 σ
      (.exec (.assign (.var "$res2") (.var "$c8")) (qxEnvC8 D a)
        (.seq [.returnStmt] (qxEnvC8 D a) qStop)) ch
      = .ok (.evalE (.var "$c8") (qxEnvC8 D a)
          (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
            (.seqn #[]) (qxEnvC8 D a)
            (.seq [.returnStmt] (qxEnvC8 D a) qStop)), σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain s1 s2) s3

/-- Ex-e31: the `$res2` store drained → the entry frame's terminal. 6
steps. -/
theorem qx2_e31_raw (σ : ExecState) (D a : Nat) (ch : Choices) :
    stepFnIter 6 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a)
        (.seq [.returnStmt] (qxEnvC8 D a) qStop))) ch
      = .ok (.next .stop, σ, ch) := by
  have s1 : stepFnIter 1 σ
      (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D a)
        (.seq [.returnStmt] (qxEnvC8 D a) qStop))) ch
      = .ok (.exec (.seqn #[]) (qxEnvC8 D a)
          (.seq [.returnStmt] (qxEnvC8 D a) qStop), σ, ch) :=
    stepFnIter_one stepFn_storeK_nil
  have s2 : stepFnIter 1 σ
      (.exec (.seqn #[]) (qxEnvC8 D a)
        (.seq [.returnStmt] (qxEnvC8 D a) qStop)) ch
      = .ok (.next (.seq [.returnStmt] (qxEnvC8 D a) qStop), σ, ch) := by
    have h := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := #[])
      (env := qxEnvC8 D a) (rest := [.returnStmt]) (k := qStop)
      (ch := ch))
    simpa using h
  have s3 : stepFnIter 4 σ
      (.next (.seq [.returnStmt] (qxEnvC8 D a) qStop)) ch
      = .ok (.next .stop, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain s1 s2) s3

/-- **The 72-step exit epilogue**: the dequeue loop's false exit test →
the break unwind → `$c8 := qsize(q)` → the three result stores → the
entry frame's terminal `.next .stop`. -/
theorem q_exit (σ : ExecState) (n seed k' m : Nat) (B C : Nat)
    (mid : Heap) (D : Nat) (rest : Heap) (na : Nat) (ch : Choices)
    (hfn : findFunctionIn? σ.functions ⟨"qsize"⟩ = some qsizeFunc)
    (hm : σ.methods = #[])
    (hmn : m ≤ n) (hn8 : n ≤ 8) (hnC : n ≤ C) (h12 : 12 ≤ D)
    (hDna : D + 4 ≤ na) (hmid : DeadFrom mid D)
    (hrest : DeadFrom rest na) :
    stepFnIter 72
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na))
      (.retV (.bool false) (qdCmpK D)) ch
      = .ok (.next .stop,
          qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (((n - m : Nat) : Int)) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3), ch) := by
  -- carriers through the front + mid + cells prefix, generic in the
  -- front's result slots and the tail literal
  have hlkT : ∀ (r0 r1 : List Int) (r2 : Int) (T : Heap) (x : Nat)
      (c : HeapCell), na ≤ x →
      Heap.lookup T (.base ⟨x⟩) = some c →
      Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (r0) (r1) (r2) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ T)))) (.base ⟨x⟩) = some c := by
    intro r0 r1 r2 T x c hx hlit
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (hmid _ (by omega)),
      lookup_append_right (qdCells_miss (by omega)),
      lookup_append_right (hrest _ (by omega))]
    exact hlit
  have hsetT : ∀ (r0 r1 : List Int) (r2 : Int) (T T' : Heap) (x : Nat)
      (c : HeapCell), na ≤ x →
      Heap.set T (.base ⟨x⟩) c = T' →
      Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (r0) (r1) (r2) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ T)))) (.base ⟨x⟩) c
        = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (r0) (r1) (r2) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ T'))) := by
    intro r0 r1 r2 T T' x c hx hset
    rw [set_append_right (qFront_miss (by omega)),
      set_append_right (hmid _ (by omega)),
      set_append_right (qdCells_miss (by omega)),
      set_append_right (hrest _ (by omega)), hset]
  -- e1: the break unwind (7)
  have e1 := qx2_e1_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na)) D ch
  -- e2: qT9's splice (2)
  have e2 : stepFnIter 2
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na))
      (.exec qT9 [dqScope D, baseScope]
        (.seq [qT10] [dqScope D, baseScope] qStop)) ch
      = .ok (.exec (.initialization { id := "$c8", typ := tU64 })
          [dqScope D, baseScope]
          (.seq [.call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"], qT10]
            [dqScope D, baseScope] qStop),
        qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na), ch) := by
    have h := stepFnIter_splice_pop
      (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na))
      (ss := #[.initialization { id := "$c8", typ := tU64 },
        .call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"]])
      (t := .initialization { id := "$c8", typ := tU64 })
      (ts := [.call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"], qT10])
      (rest := [qT10]) (env := [dqScope D, baseScope]) (k := qStop)
      (ch := ch) rfl
    rw [show (qT9 : Stmt)
      = .seqn #[.initialization { id := "$c8", typ := tU64 },
          .call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"]] from rfl]
    exact h
  -- e3: the `$c8` allocation (1)
  have e3 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na))
      (.exec (.initialization { id := "$c8", typ := tU64 })
        [dqScope D, baseScope]
        (.seq [.call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"], qT10]
          [dqScope D, baseScope] qStop)) ch
      = .ok (.next (.seq [.call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"], qT10]
            (qxEnvC8 D na) qStop),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch) := by
    have h := stepFnIter_one (stepFn_init_seq
      (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na))
      (p := { id := "$c8", typ := tU64 })
      (rest := [.call #[.var "$c8"] ⟨"qsize"⟩ #[.var "q"], qT10])
      (env := [dqScope D, baseScope]) (k := qStop) (ch := ch)
      (hdef := by with_unfolding_all rfl))
    rw [show LocalEnv.declare [dqScope D, baseScope] "$c8"
        (.base ⟨(qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na)).nextAddr⟩) = qxEnvC8 D na from rfl] at h
    rw [show Heap.set (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na)).heap
        (.base ⟨(qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false rest (na)).nextAddr⟩) ⟨some tU64, .int 0 .uint64⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0)]))) from by
      show Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ rest)))
        (.base ⟨na⟩) _ = _
      rw [set_fresh ((qHeap_dead (by omega)
        (qdTail_dead hmid (by omega) hrest)) _ (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  -- e4: the call dispatch → the `q` read (2)
  have e4 := qx2_e4_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1)) D na ch
  -- e5: the `q` argument read (1)
  have e5 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
      (.evalE (.var "q") (qxEnvC8 D na)
        (.callArgsK ⟨"qsize"⟩ [(.chain [], [.ref "$c8"])] [] []
          (qxEnvC8 D na) (qxK10 D na))) ch
      = .ok (.retV (qslV B m (n - m) (C - m))
            (.callArgsK ⟨"qsize"⟩ [(.chain [], [.ref "$c8"])] [] []
              (qxEnvC8 D na) (qxK10 D na)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch) :=
    stepFnIter_one (stepFn_var (c := slCell (qslV B m (n - m) (C - m))) rfl rfl)
  -- e6: the `qsize` frame entry (1)
  have hEnt := qsize_enterFrame (σ := σ)
    (H := qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0)]))))
    (na := na + 1) (qv := qslV B m (n - m) (C - m)) hfn hm
    (qHeap_dead (by omega) (qdTail_dead hmid (by omega) (by
      intro x hx
      rw [lookup_append_right (hrest _ (by omega))]
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
      rfl)))
  rw [show na + 1 + 1 = na + 2 from rfl] at hEnt
  have e6 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
      (.retV (qslV B m (n - m) (C - m))
        (.callArgsK ⟨"qsize"⟩ [(.chain [], [.ref "$c8"])] [] []
          (qxEnvC8 D na) (qxK10 D na))) ch
      = .ok (.exec qsizeFunc.body (qszEnv na) (qxFrameK D na),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3), ch) := by
    have h := stepFnIter_one (stepFn_call_enter (vals := [])
      (v := qslV B m (n - m) (C - m)) (plans := [(.chain [], [.ref "$c8"])])
      (env := qxEnvC8 D na) (k := qxK10 D na) (ch := ch) hEnt)
    rw [show ((qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0)]))))
        ++ [(.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
            (.base ⟨na + 2⟩, u64cell 0)] : Heap)
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]))) from by
      simp [List.append_assoc]] at h
    exact h
  -- e7 + e8: the callee body entry (2 + 2)
  have e7 : stepFnIter 2
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3))
      (.exec qsizeFunc.body (qszEnv na) (qxFrameK D na)) ch
      = .ok (.exec (.seqn #[.assign (.var "$res0")
            (.convert tU64 (.length (.var "q") (some sliceU))),
            .returnStmt]) ([] :: qszEnv na)
          (.seq [] ([] :: qszEnv na) (qxFrameK D na)),
        qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3), ch) := by
    have h := stepFnIter_block_pop
      (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3))
      (ss := #[.seqn #[.assign (.var "$res0")
          (.convert tU64 (.length (.var "q") (some sliceU))),
          .returnStmt]])
      (env := qszEnv na) (k := qxFrameK D na) (ch := ch) rfl
    rw [show (qsizeFunc.body : Stmt)
      = .block #[] #[.seqn #[.assign (.var "$res0")
          (.convert tU64 (.length (.var "q") (some sliceU))),
          .returnStmt]] from rfl]
    exact h
  have e8 : stepFnIter 2
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3))
      (.exec (.seqn #[.assign (.var "$res0")
          (.convert tU64 (.length (.var "q") (some sliceU))),
          .returnStmt]) ([] :: qszEnv na)
        (.seq [] ([] :: qszEnv na) (qxFrameK D na))) ch
      = .ok (.exec (.assign (.var "$res0")
            (.convert tU64 (.length (.var "q") (some sliceU))))
          ([] :: qszEnv na)
          (.seq [.returnStmt] ([] :: qszEnv na) (qxFrameK D na)),
        qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3), ch) :=
    stepFnIter_splice_pop (ss := #[.assign (.var "$res0")
      (.convert tU64 (.length (.var "q") (some sliceU))), .returnStmt])
      rfl
  -- e9: to the callee's `q` read (5)
  have e9 := qx2_e9_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3)) D na ch
  -- e10: the callee's `q` read (1)
  have e10 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3))
      (.evalE (.var "q") ([] :: qszEnv na)
        (.strictK (.lengthOf (some sliceU)) [] [] ([] :: qszEnv na)
          (.strictK (.convert tU64) [] [] ([] :: qszEnv na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
              (.seqn #[]) ([] :: qszEnv na)
              (.seq [.returnStmt] ([] :: qszEnv na)
                (qxFrameK D na)))))) ch
      = .ok (.retV (qslV B m (n - m) (C - m))
            (.strictK (.lengthOf (some sliceU)) [] [] ([] :: qszEnv na)
              (.strictK (.convert tU64) [] [] ([] :: qszEnv na)
                (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
                  (.seqn #[]) ([] :: qszEnv na)
                  (.seq [.returnStmt] ([] :: qszEnv na)
                    (qxFrameK D na))))),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3), ch) := by
    refine stepFnIter_one (stepFn_var (c := slCell (qslV B m (n - m) (C - m))) rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]))))
      (.base ⟨na + 1⟩) = _
    refine hlkT _ _ _ _ _ _ (by omega) ?_
    rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    simp [Heap.lookup]
  -- e11: the length apply (1)
  have e11 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3))
      (.retV (qslV B m (n - m) (C - m))
        (.strictK (.lengthOf (some sliceU)) [] [] ([] :: qszEnv na)
          (.strictK (.convert tU64) [] [] ([] :: qszEnv na)
            (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
              (.seqn #[]) ([] :: qszEnv na)
              (.seq [.returnStmt] ([] :: qszEnv na)
                (qxFrameK D na)))))) ch
      = .ok (.retV (.int ((n - m : Nat) : Int) .int)
            (.strictK (.convert tU64) [] [] ([] :: qszEnv na)
              (.rhsK .vals [.chain (.addr (.base ⟨na + 2⟩)) [] []] [] []
                (.seqn #[]) ([] :: qszEnv na)
                (.seq [.returnStmt] ([] :: qszEnv na)
                  (qxFrameK D na)))),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3), ch) :=
    stepFnIter_one (stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (by omega : n - m ≤ C - m)))
  -- e12: the convert (2), then resolve the normalization
  have e12 := qx2_e12_raw
    (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3)) D na ((n - m : Nat) : Int) ch
  rw [unorm_nat_of_lt (by omega : n - m < 2 ^ 64)] at e12
  -- e13: the `$res0` store at `na + 2` (1)
  have hst13 : storeTarget
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3))
      (.chain (.addr (.base ⟨na + 2⟩)) [] [])
      (.int ((n - m : Nat) : Int) .uint64)
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) := by
    have hlk : Heap.lookup (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3)).heap
        (.base ⟨na + 2⟩) = some (u64cell 0) := by
      show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]))))
        (.base ⟨na + 2⟩) = _
      refine hlkT _ _ _ _ _ _ (by omega) ?_
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
        lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
      simp [Heap.lookup]
    have h := storeTarget_addr hlk
      (normVal_u64 (w := ((n - m : Nat) : Int)) _ (by omega)
        (by exact_mod_cast (show n - m < 2 ^ 64 by omega)))
    rw [show Heap.set (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3)).heap
        (.base ⟨na + 2⟩) ⟨some tU64, .int ((n - m : Nat) : Int) .uint64⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))) from by
      show Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]))))
        (.base ⟨na + 2⟩) _ = _
      refine hsetT _ _ _ _ _ _ _ (by omega) ?_
      simp [Heap.set, base_beq_false (by omega : na ≠ na + 2),
        base_beq_false (by omega : na + 1 ≠ na + 2)]] at h
    exact h
  have e13 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell 0)]) (na + 3))
      (.next (.storeK [.chain (.addr (.base ⟨na + 2⟩)) [] []]
        [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) ([] :: qszEnv na)
        (.seq [.returnStmt] ([] :: qszEnv na) (qxFrameK D na)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) ([] :: qszEnv na)
            (.seq [.returnStmt] ([] :: qszEnv na) (qxFrameK D na))),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3), ch) :=
    stepFnIter_one (stepFn_store_step hst13)
  -- e14: the callee return (5)
  have e14 := qx2_e14_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)) D na ch
  -- e15: the frame return + `$c8` write-back target (1)
  have hload15 : loadMany (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)) [.base ⟨na + 2⟩]
      = .ok [.int ((n - m : Nat) : Int) .uint64] := by
    refine loadMany_one (c := u64cell ((n - m : Nat) : Int)) ?_
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))))
      (.base ⟨na + 2⟩) = _
    refine hlkT _ _ _ _ _ _ (by omega) ?_
    rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
      lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
    simp [Heap.lookup]
  have e15 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
      (.returning (qxFrameK D na)) ch
      = .ok (.evalE (.ref "$c8") (qxEnvC8 D na)
          (.tgtOpK (.chain []) [] [] [] [] .vals []
            [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) (qxEnvC8 D na)
            (qxK10 D na)),
        qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3), ch) :=
    stepFnIter_one (stepFn_return_frame hload15)
  -- e16: the `$c8` target resolution (2)
  have e16 := qx2_e16_raw
    (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)) D na (.int ((n - m : Nat) : Int) .uint64) ch
  -- e17: the `$c8` store at `na` (1)
  have hst17 : storeTarget
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
      (.chain (.addr (.base ⟨na⟩)) [] []) (.int ((n - m : Nat) : Int) .uint64)
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) := by
    have hlk : Heap.lookup (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)).heap
        (.base ⟨na⟩) = some (u64cell 0) := by
      show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))))
        (.base ⟨na⟩) = _
      refine hlkT _ _ _ _ _ _ (by omega) ?_
      simp [Heap.lookup]
    have h := storeTarget_addr hlk
      (normVal_u64 (w := ((n - m : Nat) : Int)) _ (by omega)
        (by exact_mod_cast (show n - m < 2 ^ 64 by omega)))
    rw [show Heap.set (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)).heap
        (.base ⟨na⟩) ⟨some tU64, .int ((n - m : Nat) : Int) .uint64⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))) from by
      show Heap.set (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (zeros8) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))))
        (.base ⟨na⟩) _ = _
      refine hsetT _ _ _ _ _ _ _ (by omega) ?_
      simp [Heap.set]] at h
    exact h
  have e17 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell 0),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) (qxEnvC8 D na)
        (qxK10 D na))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D na)
            (qxK10 D na)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3), ch) :=
    stepFnIter_one (stepFn_store_step hst17)
  -- e18 + e19: to the `enqueued` read (5 + 3)
  have e18 := qx2_e18_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)) D na ch
  have e19 := qx2_e19_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)) D na ch
  -- e20: the `enqueued` read off the concrete front (1)
  have e20 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
      (.evalE (.var "enqueued") (qxEnvC8 D na)
        (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
          (.seqn #[]) (qxEnvC8 D na)
          (.seq [.assign (.var "$res1") (.var "dequeued"),
            .assign (.var "$res2") (.var "$c8"), .returnStmt]
            (qxEnvC8 D na) qStop))) ch
      = .ok (.retV (.array ⟨(qPre n seed).map (fun v => .int v .uint64)⟩)
            (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
              (.seqn #[]) (qxEnvC8 D na)
              (.seq [.assign (.var "$res1") (.var "dequeued"),
                .assign (.var "$res2") (.var "$c8"), .returnStmt]
                (qxEnvC8 D na) qStop)),
          qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3), ch) :=
    stepFnIter_one (stepFn_var (c := arrCellU 8 (qPre n seed)) rfl rfl)
  -- e21: to the store point (1)
  have e21 := qx2_e21_raw (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
    (.array ⟨(qPre n seed).map (fun v => .int v .uint64)⟩) 3
    (qxEnvC8 D na)
    (.seq [.assign (.var "$res1") (.var "dequeued"),
      .assign (.var "$res2") (.var "$c8"), .returnStmt]
      (qxEnvC8 D na) qStop) ch
  -- e22: the `$res0` result store (1)
  have hst22 : storeTarget
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
      (.chain (.addr (.base ⟨3⟩)) [] [])
      (.array ⟨(qPre n seed).map (fun v => .int v .uint64)⟩)
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) := by
    have h := storeTarget_addr
      (σ := qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
      (a := ⟨3⟩) (ty := .array 8 tU64)
      (old := .array ⟨zeros8.map (fun v => .int v .uint64)⟩)
      rfl
      (normalizeValueForTy_arr_u64 (N := 8) (lp := qPre n seed)
        (qPre_length hn8) qPre_range)
    rw [show Heap.set (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3)).heap
        (.base ⟨3⟩) ⟨some (.array 8 tU64),
          .array ⟨(qPre n seed).map (fun v => .int v .uint64)⟩⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))) from rfl] at h
    exact h
  have e22 : stepFnIter 1
      (qStD σ ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qslV B m (n - m) (C - m)) (qPre n seed) mid D ((m : Nat) : Int)
        (qPre m seed) ((m : Nat) : Int) false (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]) (na + 3))
      (.next (.storeK [.chain (.addr (.base ⟨3⟩)) [] []]
        [.array ⟨(qPre n seed).map (fun v => .int v .uint64)⟩]
        (.seqn #[]) (qxEnvC8 D na)
        (.seq [.assign (.var "$res1") (.var "dequeued"),
          .assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D na) qStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D na)
            (.seq [.assign (.var "$res1") (.var "dequeued"),
              .assign (.var "$res2") (.var "$c8"), .returnStmt]
              (qxEnvC8 D na) qStop)),
          qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3), ch) :=
    stepFnIter_one (stepFn_store_step hst22)
  -- e23: to the `dequeued` read (6)
  have e23 := qx2_e23_raw
    (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) D na ch
  -- e24: the `dequeued` read at `D + 1` (1)
  have e24 : stepFnIter 1
      (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (.evalE (.var "dequeued") (qxEnvC8 D na)
        (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
          (.seqn #[]) (qxEnvC8 D na)
          (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
            (qxEnvC8 D na) qStop))) ch
      = .ok (.retV (.array ⟨(qPre m seed).map (fun v => .int v .uint64)⟩)
            (.rhsK .vals [.chain (.addr (.base ⟨4⟩)) [] []] [] []
              (.seqn #[]) (qxEnvC8 D na)
              (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
                (qxEnvC8 D na) qStop)),
          qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3), ch) := by
    refine stepFnIter_one
      (stepFn_var (c := arrCellU 8 (qPre m seed)) rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))))
      (.base ⟨D + 1⟩) = _
    rw [lookup_append_right (qFront_miss (by omega)),
      lookup_append_right (hmid _ (by omega))]
    refine lookup_append_left ?_
    rw [qdCells,
      lookup_cons_ne (base_beq_false (by omega : D ≠ D + 1))]
    simp [Heap.lookup]
  -- e25: to the store point (1)
  have e25 := qx2_e21_raw
    (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
    (.array ⟨(qPre m seed).map (fun v => .int v .uint64)⟩) 4
    (qxEnvC8 D na)
    (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
      (qxEnvC8 D na) qStop) ch
  -- e26: the `$res1` result store (1)
  have hst26 : storeTarget
      (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (.chain (.addr (.base ⟨4⟩)) [] [])
      (.array ⟨(qPre m seed).map (fun v => .int v .uint64)⟩)
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) := by
    have h := storeTarget_addr
      (σ := qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (a := ⟨4⟩) (ty := .array 8 tU64)
      (old := .array ⟨zeros8.map (fun v => .int v .uint64)⟩)
      rfl
      (normalizeValueForTy_arr_u64 (N := 8) (lp := qPre m seed)
        (qPre_length (by omega)) qPre_range)
    rw [show Heap.set
        (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)).heap
        (.base ⟨4⟩) ⟨some (.array 8 tU64),
          .array ⟨(qPre m seed).map (fun v => .int v .uint64)⟩⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))) from rfl] at h
    exact h
  have e26 : stepFnIter 1
      (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (zeros8) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (.next (.storeK [.chain (.addr (.base ⟨4⟩)) [] []]
        [.array ⟨(qPre m seed).map (fun v => .int v .uint64)⟩]
        (.seqn #[]) (qxEnvC8 D na)
        (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
          (qxEnvC8 D na) qStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D na)
            (.seq [.assign (.var "$res2") (.var "$c8"), .returnStmt]
              (qxEnvC8 D na) qStop)),
          qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3), ch) :=
    stepFnIter_one (stepFn_store_step hst26)
  -- e27: to the `$c8` read (6)
  have e27 := qx2_e27_raw
    (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) D na ch
  -- e28: the `$c8` read at `na` (1)
  have e28 : stepFnIter 1
      (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (.evalE (.var "$c8") (qxEnvC8 D na)
        (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
          (.seqn #[]) (qxEnvC8 D na)
          (.seq [.returnStmt] (qxEnvC8 D na) qStop))) ch
      = .ok (.retV (.int ((n - m : Nat) : Int) .uint64)
            (.rhsK .vals [.chain (.addr (.base ⟨5⟩)) [] []] [] []
              (.seqn #[]) (qxEnvC8 D na)
              (.seq [.returnStmt] (qxEnvC8 D na) qStop)),
          qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3), ch) := by
    refine stepFnIter_one (stepFn_var (c := u64cell ((n - m : Nat) : Int)) rfl ?_)
    show Heap.lookup (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))))
      (.base ⟨na⟩) = _
    refine hlkT _ _ _ _ _ _ (by omega) ?_
    simp [Heap.lookup]
  -- e29: to the store point (1)
  have e29 := qx2_e21_raw
    (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
    (.int ((n - m : Nat) : Int) .uint64) 5 (qxEnvC8 D na)
    (.seq [.returnStmt] (qxEnvC8 D na) qStop) ch
  -- e30: the `$res2` result store (1)
  have hst30 : storeTarget
      (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (.chain (.addr (.base ⟨5⟩)) [] []) (.int ((n - m : Nat) : Int) .uint64)
      = .ok (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (((n - m : Nat) : Int)) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) := by
    have h := storeTarget_addr
      (σ := qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (a := ⟨5⟩) (ty := tU64) (old := .int 0 .uint64)
      rfl
      (normVal_u64 (w := ((n - m : Nat) : Int)) _ (by omega)
        (by exact_mod_cast (show n - m < 2 ^ 64 by omega)))
    rw [show Heap.set
        (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)).heap
        (.base ⟨5⟩) ⟨some tU64, .int ((n - m : Nat) : Int) .uint64⟩
      = qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (((n - m : Nat) : Int)) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))]))) from rfl] at h
    exact h
  have e30 : stepFnIter 1
      (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (0) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3))
      (.next (.storeK [.chain (.addr (.base ⟨5⟩)) [] []]
        [.int ((n - m : Nat) : Int) .uint64] (.seqn #[]) (qxEnvC8 D na)
        (.seq [.returnStmt] (qxEnvC8 D na) qStop))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (qxEnvC8 D na)
            (.seq [.returnStmt] (qxEnvC8 D na) qStop)),
          qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (((n - m : Nat) : Int)) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3), ch) :=
    stepFnIter_one (stepFn_store_step hst30)
  -- e31: the terminal (6)
  have e31 := qx2_e31_raw
    (qSt σ (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k' : Nat) : Int)
        (qPre n seed) (qPre m seed) (((n - m : Nat) : Int)) (qslV B m (n - m) (C - m)) (qPre n seed)
        ((n : Nat) : Int) false
      ++ (mid ++ (qdCells D ((m : Nat) : Int) (qPre m seed) ((m : Nat) : Int) false
        ++ (rest ++ [(.base ⟨na⟩, u64cell ((n - m : Nat) : Int)),
          (.base ⟨na + 1⟩, slCell (qslV B m (n - m) (C - m))),
          (.base ⟨na + 2⟩, u64cell ((n - m : Nat) : Int))])))) (na + 3)) D na ch
  -- the chain
  have hall := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
              (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                  (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
                    (stepFnIter_chain (stepFnIter_chain
                      (stepFnIter_chain e1 e2) e3) e4) e5) e6) e7) e8)
                    e9) e10) e11) e12) e13) e14) e15) e16) e17) e18)
                    e19) e20) e21) e22) e23) e24) e25) e26) e27) e28)
                    e29) e30) e31
  rw [show (7 : Nat) + 2 + 1 + 2 + 1 + 1 + 2 + 2 + 5 + 1 + 1 + 2 + 1
      + 5 + 1 + 2 + 1 + 5 + 3 + 1 + 1 + 1 + 6 + 1 + 1 + 1 + 6 + 1 + 1
      + 1 + 6 = 72 from by omega] at hall
  exact hall

/-! ## The pinned program, the entry equation, and the run -/

/-- The pinned program as an empty-heap state (mirror `stProg`). -/
def qProg : ExecState :=
  { types := queueLowered.typeDefs.toList,
    functions := queueLowered.funcs,
    methods := queueLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq qH_entry_eq queueLowered queueHarnessRFunc qHSeed qHC0
  qProg

/-- The final-state readback: the three result cells, generic over the
tail (mirror `st_readback`). -/
theorem q_readback (σ : ExecState) (nv sv kv r2 : Int)
    (r0 r1 : List Int) (qv : GoValue) (lE : List Int) (iv : Int)
    (ff : Bool) (Tf : Heap) (naf : Nat) :
    loadMany (qSt σ (qFront nv sv kv r0 r1 r2 qv lE iv ff ++ Tf) naf)
      [.base ⟨3⟩, .base ⟨4⟩, .base ⟨5⟩]
      = .ok [.array ⟨r0.map (fun v => .int v .uint64)⟩,
             .array ⟨r1.map (fun v => .int v .uint64)⟩,
             .int r2 .uint64] := by
  with_unfolding_all rfl

/-- **The harness run**: exactly
`242 + 130·n + 117·min(k,n) + 12·[n < k]` steps from the machine
entry's post-prelude seed to the driver terminal, at EVERY choice
stream — the count is choice-invariant even though the heap layout is
not (the existential backing address/capacity, final tail, allocation
front and leftover stream carry the choice-dependence). -/
theorem q_run (n seed k : Nat) (hcap : n ≤ 8) (_hseed : seed < 2 ^ 64)
    (hk : k < 2 ^ 64) (ch : Choices) :
    ∃ (Bf Cf naf : Nat) (Tf : Heap) (ch' : Choices),
      stepFnIter (242 + 130 * n + 117 * min k n
          + (if n < k then 12 else 0))
        (qSt qProg (qHeap0 ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)) 6)
        (.exec queueHarnessRFunc.body [baseScope] qStop) ch
      = .ok (.next .stop,
          qSt qProg
            (qFront ((n : Nat) : Int) ((seed : Nat) : Int) ((k : Nat) : Int)
              (qPre n seed) (qPre (min k n) seed)
              ((n - min k n : Nat) : Int)
              (qslV Bf (min k n) (n - min k n) (Cf - min k n))
              (qPre n seed) ((n : Nat) : Int) false ++ Tf) naf,
          ch') := by
  have hfnE : findFunctionIn? qProg.functions ⟨"enqueue"⟩
      = some enqueueFunc := enqueue_pin
  have hfnD : findFunctionIn? qProg.functions ⟨"dequeue"⟩
      = some dequeueFunc := dequeue_pin
  have hfnQ : findFunctionIn? qProg.functions ⟨"qsize"⟩
      = some qsizeFunc := qsize_pin
  have hmets : qProg.methods = #[] := rfl
  -- the 59-step entry and the 25-step first loop head
  have hE0 := qe_E0_raw qProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((k : Nat) : Int) ch
  have hA0 := qe_A0_raw qProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((k : Nat) : Int) (qslV 7 0 0 0) zeros8 0 [] 12 ch
  have hEA := stepFnIter_chain hE0 hA0
  rw [show ((0 : Int)) = ((0 : Nat) : Int) from rfl,
    show (zeros8 : List Int) = qPre 0 seed from (qPre_zero seed).symm]
    at hEA
  -- the enqueue loop from the freshly established invariant
  obtain ⟨B', C', tail', na', ch1, hloop, hna12', hinv'⟩ :=
    qe_loop qProg n seed k hfnE hmets hcap 0 (Nat.zero_le n) 7 0 [] 12
      ch ⟨Nat.zero_le _, by omega, by omega, (fun x _ => rfl),
        Or.inl ⟨rfl, rfl, rfl⟩⟩
  rw [show n - 0 = n from by omega] at hloop
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hloop
  have hEAL := stepFnIter_chain hEA hloop
  obtain ⟨hnC', h12na', hB'na', htail', hsplit⟩ := hinv'
  -- the min branch and the dequeue-loop declarations
  have hX := qx_toHead qProg n seed k ((seed : Nat) : Int)
    (qslV B' 0 n C') (qPre n seed) ((n : Nat) : Int) tail' na' ch1
    h12na' htail' hcap hk
  have hEALX := stepFnIter_chain hEAL hX
  -- bridge the four fresh cells into the `qStD` shape
  rw [show (tail' ++ [(.base ⟨na'⟩,
        u64cell ((min k n : Nat) : Int)),
      (.base ⟨na' + 1⟩, arrCellU 8 zeros8),
      (.base ⟨na' + 2⟩, u64cell 0),
      (.base ⟨na' + 3⟩, bcell true)] : Heap)
    = tail' ++ (qdCells na' ((min k n : Nat) : Int) zeros8 0 true
        ++ []) from by
    simp [qdCells]] at hEALX
  -- the dequeue head
  have hHead := qd_head qProg ((n : Nat) : Int) ((seed : Nat) : Int)
    ((k : Nat) : Int) (qslV B' 0 n C') (qPre n seed) tail' na'
    ((min k n : Nat) : Int) zeros8 [] (na' + 4) ch1 h12na' htail'
  have hEALXH := stepFnIter_chain hEALX hHead
  rcases hsplit with ⟨hn0, hB7, hC0⟩ | ⟨hB'12, hBlk⟩
  · -- the queue was never enqueued: `n = 0`, no dequeues
    subst hn0
    have hm0 : min k 0 = 0 := by omega
    rw [hm0] at hEALXH
    rw [show (decide ((0 : Int) < ((0 : Nat) : Int))) = false from
      decide_eq_false (by omega)] at hEALXH
    -- massage into the exit shape at `m = 0`
    rw [show (zeros8 : List Int) = qPre 0 seed from
      (qPre_zero seed).symm,
      show ((0 : Int)) = ((0 : Nat) : Int) from rfl] at hEALXH
    have hXit := q_exit qProg 0 seed k 0 B' C' tail' na' [] (na' + 4)
      ch1 hfnQ hmets (Nat.le_refl 0) (by omega) (Nat.zero_le C')
      h12na' (by omega) htail' (fun x _ => rfl)
    have hFull := stepFnIter_chain hEALXH hXit
    refine ⟨B', C', na' + 4 + 3,
      tail' ++ (qdCells na' ((0 : Nat) : Int) (qPre 0 seed)
        ((0 : Nat) : Int) false
        ++ ([] ++ [(.base ⟨na' + 4⟩, u64cell ((0 - 0 : Nat) : Int)),
          (.base ⟨na' + 4 + 1⟩, slCell (qslV B' 0 (0 - 0) (C' - 0))),
          (.base ⟨na' + 4 + 2⟩, u64cell ((0 - 0 : Nat) : Int))])),
      ch1, ?_⟩
    rw [show 242 + 130 * 0 + 117 * min k 0 + (if 0 < k then 12 else 0)
        = 59 + 25 + 130 * 0 + (if 0 < k then 73 else 61) + 25 + 72
        from by
      by_cases hk0 : 0 < k
      · simp only [if_pos hk0, hm0]
        try omega
      · simp only [if_neg hk0, hm0]
        try omega]
    rw [hm0]
    exact hFull
  · -- the general case: the backing lives in the enqueue tail
    rw [show ((0 : Int)) = ((0 : Nat) : Int) from rfl,
      show (zeros8 : List Int) = qPre 0 seed from
        (qPre_zero seed).symm] at hEALXH
    obtain ⟨rest', na'', hdloop, hnale, hD4'', hdead''⟩ :=
      qd_loop qProg n seed k (min k n) B' C' tail' na' hfnD hmets
        (Nat.min_le_right k n) hcap hnC' h12na' hB'12 htail' hBlk
        0 (Nat.zero_le _) [] (na' + 4) ch1 (by omega) (fun x _ => rfl)
    rw [show n - 0 = n from by omega,
      show C' - 0 = C' from by omega] at hdloop
    rw [show (decide (((min k n : Nat) : Int)
        < ((min k n : Nat) : Int))) = false from
      decide_eq_false (by omega)] at hdloop
    have hEALXHL := stepFnIter_chain hEALXH hdloop
    have hXit := q_exit qProg n seed k (min k n) B' C' tail' na' rest'
      na'' ch1 hfnQ hmets (Nat.min_le_right k n) hcap hnC' h12na'
      hD4'' htail' hdead''
    have hFull := stepFnIter_chain hEALXHL hXit
    refine ⟨B', C', na'' + 3,
      tail' ++ (qdCells na' ((min k n : Nat) : Int)
        (qPre (min k n) seed) ((min k n : Nat) : Int) false
        ++ (rest'
          ++ [(.base ⟨na''⟩, u64cell ((n - min k n : Nat) : Int)),
            (.base ⟨na'' + 1⟩,
              slCell (qslV B' (min k n) (n - min k n) (C' - min k n))),
            (.base ⟨na'' + 2⟩,
              u64cell ((n - min k n : Nat) : Int))])),
      ch1, ?_⟩
    rw [show 242 + 130 * n + 117 * min k n + (if n < k then 12 else 0)
        = 59 + 25 + 130 * n + (if n < k then 73 else 61) + 25
          + 117 * (min k n - 0) + 72 from by
      by_cases hnk : n < k
      · simp only [if_pos hnk]
        omega
      · simp only [if_neg hnk]
        omega]
    exact hFull

/-! ## The user-facing statements -/

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8`, EVERY `seed < 2^64`, and EVERY `k < 2^64`, running the Go
harness `queue_harness_r(n, seed, k)` through the machine's native
function entry completes normally past one fuel bound, AT EVERY
NONDETERMINISM-CHOICE STREAM, and returns three values: the `n`
enqueued values as a fixed-cap array, `enqueued.take k` — FIFO order,
truncated at what the queue holds — and the remaining queue size,
`n − k` truncated at zero. The postcondition is a relation over the
RETURNED DATA — no family function appears in it.

Honesty clauses, recorded rather than hidden (the stack mirror's
apply, FIFO for LIFO):

* **`∀ ch` DOES REAL WORK HERE** — each `append` that outgrows its
  backing draws one capacity choice from the machine's growth
  envelope; the proof is CAPACITY- AND ADDRESS-GENERIC (`qEnqInv`),
  so the theorem holds at every stream. The step COUNT is
  choice-invariant; the heap layout is not.
* **`∃ enqueued` is family-determined** — the witness is
  `qFam n seed = [seed, seed+1, …]` reduced mod 2^64.
* **The arithmetic wraps, and the claim covers the wrap region** —
  the domain is the FULL `seed < 2^64`.
* **The cap `n ≤ 8` is a toy bound** — the program's own
  `queueCapN = 8` observation arrays.
* **The third value is the REMAINING queue size, and `n − k` is Nat
  subtraction** — the Go dequeues `min(k, n)` values and returns
  `qsize(q) = n − min(k, n) = (n - k : Nat)`.
* **The fuel bound `247·n + 254` is a BOUND, not the exact count.**
  The measured count is `242 + 130·n + 117·min(k,n) + 12·[n < k]`
  (proved as `q_run`'s exact count); the shipped `N` equals it
  exactly when `k > n` and is loose by `117·(n − k) + 12` when
  `k ≤ n`.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds. -/
theorem queue_ok (n seed k : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    ∃ enqueued : List Int, enqueued.length = n ∧
      ∃ N : Nat, ∀ fuel ≥ N, ∀ ch : Choices,
        runFunctionWithContextM fuel queueLowered.typeDefs.toList
            queueLowered.funcs queueHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (k : Int) .uint64]
            queueLowered.methods ch
          = .ok { values := #[qArr8 enqueued,
                              qArr8 (enqueued.take k),
                              .int ((n - k : Nat) : Int) .uint64] } := by
  refine ⟨qFam n seed, qFam_length n seed, 247 * n + 254,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨Bf, Cf, naf, Tf, ch', hrun⟩ := q_run n seed k hcap hseed hk ch
  have hle : 242 + 130 * n + 117 * min k n
      + (if n < k then 12 else 0) ≤ fuel := by
    by_cases hnk : n < k
    · simp only [if_pos hnk]
      omega
    · simp only [if_neg hnk]
      omega
  have hfold := runConfig_of_stepFnIter hrun
    (fuel - (242 + 130 * n + 117 * min k n + (if n < k then 12 else 0)))
  rw [Nat.add_sub_cancel' hle] at hfold
  have hst : qHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
        ((k : Nat) : Int)
      = qSt qProg (qHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
          ((k : Nat) : Int)) 6 := rfl
  have hc0 : qHC0
      = Config.exec queueHarnessRFunc.body [baseScope] qStop := rfl
  rw [qH_entry_eq (n : Int) (seed : Int) (k : Int) fuel ch,
    unorm_nat_of_lt (by omega : n < 2 ^ 64), unorm_nat_of_lt hseed,
    unorm_nat_of_lt hk, hst, hc0, hfold, runConfig_next_stop]
  simp only [bind, Except.bind, q_readback, pure, Except.pure]
  rw [show ((n - k : Nat) : Int) = ((n - min k n : Nat) : Int) from by
    congr 1
    omega]
  rw [qArr8, qArr8, ← qPre_full, qFam_take, ← qPre_full]

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly
those three values — derived from `queue_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem queue_readout (n seed k : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (hk : k < 2 ^ 64) :
    ∃ enqueued : List Int, enqueued.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel queueLowered.typeDefs.toList
            queueLowered.funcs queueHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (k : Int) .uint64]
            queueLowered.methods ch
          = .ok r →
        r = { values := #[qArr8 enqueued,
                          qArr8 (enqueued.take k),
                          .int ((n - k : Nat) : Int) .uint64] } := by
  obtain ⟨enqueued, hlen, N, htot⟩ := queue_ok n seed k hcap hseed hk
  exact ⟨enqueued, hlen, harness_readout_of_total ⟨N, htot⟩⟩

end GoLean.Examples.SliceQueue
