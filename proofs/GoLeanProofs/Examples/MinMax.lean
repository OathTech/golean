import GoLeanProofs.Examples.MinMaxProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps

/-!
# Verified example: min/max of a slice (verified-examples slice 2c,
2026-08-13)

The Go program is the canonical corpus source
`Corpus/coverage/exec/examples/minmax/main.go` (differentially green
against `go run` on 6 rows, INCLUDING the empty-slice PANIC row
`examples/minmax/empty-panics` — `minMax` of an empty slice panics at
`s[0]`, which is why the headline carries `hne : xs ≠ []`; the panic
row pins that boundary in the oracle, and the theorem honestly
excludes it). `minMaxLowered` is the pinned frontend lowering
(`scripts/check-golden`, both links).

The user-facing statement is `minmax_ok` — the §9 memory-quantified
headline in the reverse shape (design note
`docs/2026-08-12_example-spec-form.md` §9): input slice `xs` at an
arbitrary placement `base`, an arbitrary disjoint frame `fr`,
completion + BOTH result values + the backing cell UNCHANGED (the
program is read-only on its input — the "total heap" story: result
cells, input cell, and pointwise frame preservation together account
for every address the claim speaks about) at every choice stream past
one fuel bound. Statement hypotheses recorded honestly:

* `hne : xs ≠ []` — Go PANICS on the empty slice (`s[0]`); the corpus
  row `examples/minmax/empty-panics` pins it. Not a proof-method
  limit: the claim as stated would be FALSE at `xs = []`.
* `hb0 : base ≠ 0`, `hb1 : base ≠ 1` — the driver's result cells sit
  at addresses 0 and 1 (`resCells`, bound by `minMaxEnv`), so the
  input's backing cell must not collide with them. A harness-layout
  condition, visible rather than hidden.
* `hlen : xs.length < 2 ^ 63` — the reverse precedent verbatim: the
  driver's slice expression evaluates `len` as a Go `int` literal, and
  a length at or beyond `2^63` wraps negative and panics the bounds
  check. Go's own `int` domain, not a proof-method limit.

**Proof route** (the reverse route, replicated as directed): direct
machine-step segments (`with_unfolding_all rfl` raw segments split at
the data-dependent branch points; conditioned single steps through the
`SliceMem` executable facts), ONE strong induction on the remaining
measure `μ = len − m` carrying both the value half (loop-head state
pinned exactly: lo = `minSpec (xs.take m)`, hi = `maxSpec (xs.take m)`)
and the completion half (explicit affine fuel bound `37 + 96·len`);
then the executable frame theorem transfers the canonical run
(`base = 2`, tight seed, dom = {0,1,2}, na₀ = 3) to every admissible
framed placement through the input-relocating renaming
`relocShift base na` — nothing is re-run at a framed placement.

Scope honesty (the charter's two-questions separation): usability
evidence only — never machine-hardening evidence.
-/

namespace GoLean.Examples.MinMax

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The mathematical reference functions -/

/-- Minimum of a list of `Int`s (0 on `[]` — the headline never
consumes that case, `hne` excludes it). -/
def minSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => min v (minSpec (w :: rest))

/-- Maximum of a list of `Int`s (0 on `[]` — never consumed, as
`minSpec`). -/
def maxSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => max v (maxSpec (w :: rest))

/-! ## The program-side statement vocabulary -/

/-- The first body conditional: `if s[i] < lo { lo = s[i] }`. -/
abbrev mmLoIf : Stmt :=
  .ifThenElse
    (.lessCmp (.indexGet (.var "s") (.var "i")) (.var "lo"))
    (.block #[]
      #[.seqn #[.assign (.var "lo") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[])

/-- The second body conditional: `if s[i] > hi { hi = s[i] }`. -/
abbrev mmHiIf : Stmt :=
  .ifThenElse
    (.greaterCmp (.indexGet (.var "s") (.var "i")) (.var "hi"))
    (.block #[]
      #[.seqn #[.assign (.var "hi") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[])

/-- The frontend's `for`-desugar body: the `$forFirst` dispatch (post
statement `i = i + 1` on later passes), the exit test `i < len(s)`
ending in `break`, then the two conditionals. -/
abbrev mmWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "i")
          (.length (.var "s") (some (.slice (.int .uint64)))))
        (.seqn #[])
        .breakStmt,
      .block #[] #[mmLoIf, mmHiIf]]

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def minMaxFunc : Func :=
  { id := { key := "minMax" },
    args := #[{ id := "s", typ := .slice (.int .uint64) }],
    results := #[{ id := "$res0", typ := .int .uint64 },
                 { id := "$res1", typ := .int .uint64 }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "lo", typ := .int .uint64 },
            .initialization { id := "hi", typ := .int .uint64 },
            .assignMany #[.var "lo", .var "hi"]
              #[.indexGet (.var "s") (.intLit 0 .int),
                .indexGet (.var "s") (.intLit 0 .int)]],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .int },
                .assign (.var "i") (.intLit 1 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) mmWhileBody]],
        .seqn
          #[.assign (.var "$res0") (.var "lo"),
            .assign (.var "$res1") (.var "hi"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? minMaxLowered.funcs ⟨"minMax"⟩ = some minMaxFunc :=
  rfl

/-- The driver environment: the two harness result cells. -/
def minMaxEnv : LocalEnv := [[("$mn", .base ⟨0⟩), ("$mx", .base ⟨1⟩)]]

/-- The harness result cells (addresses 0 and 1, zeroed uint64). -/
def resCells : Heap :=
  [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩),
   (.base ⟨1⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]

/-- The driver: `$mn, $mx = minMax(s)` with the slice handle over the
backing array at `base` as the literal argument. -/
def minMaxCall (xs : List Int) (base : Nat) : Stmt :=
  .call #[.var "$mn", .var "$mx"] ⟨"minMax"⟩
    #[.slice (.locLit (.base ⟨base⟩)) (.intLit 0 .int)
        (.intLit xs.length .int) none]

/-- The framed seed: result cells at 0/1, the input's backing cell at
`base`, an arbitrary frame `fr`, allocator at `na`. The canonical
placement is `minMaxSeed xs 2 [] 3` — TIGHT (dom = {0, 1, 2}, na₀ = 3),
as the frame theorem's seed discharge requires. -/
def minMaxSeed (xs : List Int) (base : Nat) (fr : Heap) (na : Nat) :
    ExecState :=
  { types := minMaxLowered.typeDefs.toList, functions := minMaxLowered.funcs,
    methods := minMaxLowered.methods,
    heap := resCells ++ sliceCells xs base ++ fr, nextAddr := na }

/-! ## The pure layer: prefix min/max surgery -/

private theorem getD_mem {xs : List Int} {k : Nat} (hk : k < xs.length) :
    xs.getD k 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

private theorem take_ne_nil {xs : List Int} {m : Nat} (hm1 : 1 ≤ m)
    (hne : xs ≠ []) : xs.take m ≠ [] := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons v t =>
      intro hc
      have hlen := congrArg List.length hc
      simp only [List.length_take, List.length_cons, List.length_nil] at hlen
      omega

private theorem take_succ_snoc {xs : List Int} {m : Nat}
    (hm : m < xs.length) :
    xs.take (m + 1) = xs.take m ++ [xs.getD m 0] := by
  have hx : xs[m]? = some (xs.getD m 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  rw [List.take_add_one, hx]
  rfl

/-- Appending one element to a nonempty list steps `minSpec` by `min`. -/
private theorem minSpec_snoc (w : Int) (t : List Int) (v : Int) :
    minSpec ((w :: t) ++ [v]) = min (minSpec (w :: t)) v := by
  induction t generalizing w with
  | nil => simp [minSpec]
  | cons x rest ih =>
      show min w (minSpec ((x :: rest) ++ [v]))
        = min (minSpec (w :: x :: rest)) v
      rw [ih x]
      show min w (min (minSpec (x :: rest)) v)
        = min (min w (minSpec (x :: rest))) v
      omega

private theorem maxSpec_snoc (w : Int) (t : List Int) (v : Int) :
    maxSpec ((w :: t) ++ [v]) = max (maxSpec (w :: t)) v := by
  induction t generalizing w with
  | nil => simp [maxSpec]
  | cons x rest ih =>
      show max w (maxSpec ((x :: rest) ++ [v]))
        = max (maxSpec (w :: x :: rest)) v
      rw [ih x]
      show max w (max (maxSpec (x :: rest)) v)
        = max (max w (maxSpec (x :: rest))) v
      omega

/-- **One machine iteration advances the prefix minimum**. -/
private theorem minSpec_take_succ {xs : List Int} {m : Nat}
    (hm1 : 1 ≤ m) (hm : m < xs.length) :
    minSpec (xs.take (m + 1)) = min (minSpec (xs.take m)) (xs.getD m 0) := by
  have hne : xs ≠ [] := by intro hc; subst hc; simp at hm
  rw [take_succ_snoc hm]
  match hx : xs.take m, take_ne_nil hm1 hne with
  | w :: t, _ => exact minSpec_snoc w t _

private theorem maxSpec_take_succ {xs : List Int} {m : Nat}
    (hm1 : 1 ≤ m) (hm : m < xs.length) :
    maxSpec (xs.take (m + 1)) = max (maxSpec (xs.take m)) (xs.getD m 0) := by
  have hne : xs ≠ [] := by intro hc; subst hc; simp at hm
  rw [take_succ_snoc hm]
  match hx : xs.take m, take_ne_nil hm1 hne with
  | w :: t, _ => exact maxSpec_snoc w t _

private theorem minSpec_take_one {xs : List Int} (hne : xs ≠ []) :
    minSpec (xs.take 1) = xs.getD 0 0 := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons v t => simp [minSpec, List.take]

private theorem maxSpec_take_one {xs : List Int} (hne : xs ≠ []) :
    maxSpec (xs.take 1) = xs.getD 0 0 := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons v t => simp [maxSpec, List.take]

/-- The prefix minimum is an element (the range hypotheses transport). -/
private theorem minSpec_mem : ∀ {l : List Int}, l ≠ [] → minSpec l ∈ l := by
  intro l
  induction l with
  | nil => exact fun h => absurd rfl h
  | cons v t ih =>
      intro _
      cases t with
      | nil => simp [minSpec]
      | cons w rest =>
          show min v (minSpec (w :: rest)) ∈ v :: w :: rest
          rcases (by rw [Int.min_def]; split <;> simp :
              min v (minSpec (w :: rest)) = v
                ∨ min v (minSpec (w :: rest)) = minSpec (w :: rest)) with h | h
          · rw [h]; exact List.mem_cons_self ..
          · rw [h]
            exact List.mem_cons_of_mem _ (ih (by simp))

private theorem maxSpec_mem : ∀ {l : List Int}, l ≠ [] → maxSpec l ∈ l := by
  intro l
  induction l with
  | nil => exact fun h => absurd rfl h
  | cons v t ih =>
      intro _
      cases t with
      | nil => simp [maxSpec]
      | cons w rest =>
          show max v (maxSpec (w :: rest)) ∈ v :: w :: rest
          rcases (by rw [Int.max_def]; split <;> simp :
              max v (maxSpec (w :: rest)) = v
                ∨ max v (maxSpec (w :: rest)) = maxSpec (w :: rest)) with h | h
          · rw [h]; exact List.mem_cons_self ..
          · rw [h]
            exact List.mem_cons_of_mem _ (ih (by simp))

private theorem minTake_range {xs : List Int} {m : Nat}
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hm1 : 1 ≤ m) (hne : xs ≠ []) :
    0 ≤ minSpec (xs.take m) ∧ minSpec (xs.take m) < 2 ^ 64 :=
  hxs _ (List.mem_of_mem_take (minSpec_mem (take_ne_nil hm1 hne)))

private theorem maxTake_range {xs : List Int} {m : Nat}
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hm1 : 1 ≤ m) (hne : xs ≠ []) :
    0 ≤ maxSpec (xs.take m) ∧ maxSpec (xs.take m) < 2 ^ 64 :=
  hxs _ (List.mem_of_mem_take (maxSpec_mem (take_ne_nil hm1 hne)))

/-! ## The machine layer: canonical-placement configurations

Transcribed from the machine (probe-verified against the concrete run
`xs = [3, 1, 4]`; every raw segment below re-checks the transcription
by `rfl`). Address layout at the canonical placement: 0 = `$mn`,
1 = `$mx` (the harness result cells), 2 = the backing array, 3 = the
parameter `s` (the handle), 4 = `$res0`, 5 = `$res1`, 6 = `lo`,
7 = `hi`, 8 = `i`, 9 = `$forFirst`; allocator parked at 10 for the
whole loop. -/

private abbrev ucell (v : Int) : HeapCell := ⟨some (.int .uint64), .int v .uint64⟩
private abbrev icell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
private abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
private abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
private abbrev hcell (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ⟨2⟩), 0, n, n⟩⟩
private abbrev sliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨2⟩), 0, n, n⟩

private def envB : LocalEnv :=
  [[("hi", .base ⟨7⟩), ("lo", .base ⟨6⟩)],
   [("$res1", .base ⟨5⟩), ("$res0", .base ⟨4⟩), ("s", .base ⟨3⟩)]]
private def envI : LocalEnv := [("i", .base ⟨8⟩)] :: envB
private def envIn : LocalEnv := [("$forFirst", .base ⟨9⟩)] :: envI
private def envC : LocalEnv := [] :: envIn
private def envB2 : LocalEnv := [] :: envC
private def envB3 : LocalEnv := [] :: envB2

private def mmShapes : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "$mn"]), (.chain [], [.ref "$mx"])]
private def frameK : Cont :=
  .frame mmShapes minMaxEnv [.base ⟨4⟩, .base ⟨5⟩] [] .stop false
private def entryK : Cont := .callArgsK ⟨"minMax"⟩ mmShapes [] [] minMaxEnv .stop

private def mmTailSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "lo"),
          .assign (.var "$res1") (.var "hi"), .returnStmt]
private def mmIffBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 1 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) mmWhileBody]]

private def entryTail : Cont := .seq [mmIffBlock, mmTailSeqn] envB frameK
private def tref6 : TargetRef := .chain (.addr (.base ⟨6⟩)) [] []
private def tref7 : TargetRef := .chain (.addr (.base ⟨7⟩)) [] []
private def rhs1K : Cont :=
  .rhsK .vals [tref6, tref7] []
    [.indexGet (.var "s") (.intLit 0 .int)] (.seqn #[]) envB entryTail
private def rhs2K (w : Int) : Cont :=
  .rhsK .vals [tref6, tref7] [.int w .uint64] [] (.seqn #[]) envB entryTail

private def headTail : Cont :=
  .seq [] envIn (.seq [] envI (.seq [mmTailSeqn] envB frameK))
/-- The loop-head configuration. -/
private def headCfg : Config :=
  .exec (.while (.boolLit true) mmWhileBody) envIn headTail
private def loopK : Cont := .loop (.boolLit true) mmWhileBody envIn headTail
/-- The exit test's delivery continuation (the loop's segment split
point). -/
private def cmpIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt envC
    (.seq [.block #[] #[mmLoIf, mmHiIf]] envC loopK)
/-- The `len(s)` apply point inside the exit test (`iv` = the counter
value riding in the comparison's operand list). -/
private def lenApplyK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] envC
    (.strictK .lessCmp [.int iv .int] [] envC cmpIfK)

private def loIfK : Cont :=
  .ifK (.block #[]
      #[.seqn #[.assign (.var "lo") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[]) envB2 (.seq [mmHiIf] envB2 (.seq [] envC loopK))
private def loCmpK : Cont := .strictK .lessCmp [] [.var "lo"] envB2 loIfK
private def loStoreK : Cont :=
  .rhsK .vals [tref6] [] [] (.seqn #[]) envB3
    (.seq [] envB3 (.seq [mmHiIf] envB2 (.seq [] envC loopK)))
private def hiIfK : Cont :=
  .ifK (.block #[]
      #[.seqn #[.assign (.var "hi") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[]) envB2 (.seq [] envB2 (.seq [] envC loopK))
private def hiCmpK : Cont := .strictK .greaterCmp [] [.var "hi"] envB2 hiIfK
private def hiStoreK : Cont :=
  .rhsK .vals [tref7] [] [] (.seqn #[]) envB3
    (.seq [] envB3 (.seq [] envB2 (.seq [] envC loopK)))

/-- The in-loop state: backing list `l` (never written), `lo`/`hi`
cells, counter `iv`, the `$forFirst` flag. -/
private def mmStateP (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ffv : Bool) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs,
    methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell 0), (.base ⟨1⟩, ucell 0),
             (.base ⟨2⟩, arrCell n l), (.base ⟨3⟩, hcell n),
             (.base ⟨4⟩, ucell 0), (.base ⟨5⟩, ucell 0),
             (.base ⟨6⟩, ucell lov), (.base ⟨7⟩, ucell hiv),
             (.base ⟨8⟩, icell iv), (.base ⟨9⟩, bcell ffv)],
    nextAddr := 10 }

/-- The mid-entry state: frame entered, `lo`/`hi` allocated at
defaults. -/
private def σE1 (xs : List Int) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs,
    methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell 0), (.base ⟨1⟩, ucell 0),
             (.base ⟨2⟩, arrCell xs.length xs), (.base ⟨3⟩, hcell xs.length),
             (.base ⟨4⟩, ucell 0), (.base ⟨5⟩, ucell 0),
             (.base ⟨6⟩, ucell 0), (.base ⟨7⟩, ucell 0)],
    nextAddr := 8 }

/-- The exit-test state after the dispatch of iteration `m`: prefix
min/max in the `lo`/`hi` cells, counter at `m`. -/
private abbrev cmpState (xs : List Int) (m : Nat) : ExecState :=
  mmStateP xs.length xs (minSpec (xs.take m)) (maxSpec (xs.take m))
    ((m : Nat) : Int) false

/-- The canonical terminal state: results delivered to the harness
cells, backing UNCHANGED. -/
private def mmFinal (xs : List Int) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs,
    methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell (minSpec xs)), (.base ⟨1⟩, ucell (maxSpec xs)),
             (.base ⟨2⟩, arrCell xs.length xs), (.base ⟨3⟩, hcell xs.length),
             (.base ⟨4⟩, ucell (minSpec xs)), (.base ⟨5⟩, ucell (maxSpec xs)),
             (.base ⟨6⟩, ucell (minSpec xs)), (.base ⟨7⟩, ucell (maxSpec xs)),
             (.base ⟨8⟩, icell ((xs.length : Nat) : Int)),
             (.base ⟨9⟩, bcell false)],
    nextAddr := 10 }

/-! ## Generic single-step glue (the branchy steps) -/

private theorem stepFnIter_one {σ : ExecState} {c : Config} {ch : Choices}
    {r : Config × ExecState × Choices}
    (h : stepFn σ c ch = .ok r) : stepFnIter 1 σ c ch = .ok r := by
  obtain ⟨c', σ', ch'⟩ := r
  simp [stepFnIter, h, Bind.bind, Except.bind]

/-- The strict-apply machine step, conditioned on the op fact. -/
private theorem stepFn_strict_apply {σ σ' : ExecState} {op : StrictOp}
    {done : List GoValue} {v out : GoValue} {env : LocalEnv} {k : Cont}
    {ch : Choices}
    (h : applyStrictOp σ op (v :: done).reverse = .ok (out, σ')) :
    stepFn σ (.retV v (.strictK op done [] env k)) ch
      = .ok (.retV out k, σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- The integer `<` strict-op fact (both operand kinds free: the
machine compares the `Int` payloads). -/
private theorem applyStrictOp_lessCmp_int {σ : ExecState} {a b : Int}
    {k k' : IntKind} :
    applyStrictOp σ .lessCmp [.int a k, .int b k']
      = .ok (.bool (decide (a < b)), σ) := rfl

/-! ## Heap lookup facts at the pinned states -/

private theorem lookup_seed (xs : List Int) :
    Heap.lookup (minMaxSeed xs 2 [] 3).heap (.base ⟨2⟩)
      = some ⟨some (.array xs.length (.int .uint64)),
          .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
  simp [minMaxSeed, resCells, sliceCells, Heap.lookup]

private theorem lookup_σE1 (xs : List Int) :
    Heap.lookup (σE1 xs).heap (.base ⟨2⟩)
      = some ⟨some (.array xs.length (.int .uint64)),
          .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
  simp [σE1, Heap.lookup]

private theorem lookup_state (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ffv : Bool) :
    Heap.lookup (mmStateP n l lov hiv iv ffv).heap (.base ⟨2⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [mmStateP, Heap.lookup]

private theorem getElem?_mapU (l : List Int) (k : Nat) (hk : k < l.length) :
    (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[k]?
      = some (.int (l.getD k 0) .uint64) := by
  simp [List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]

/-! ## Raw run segments (`with_unfolding_all rfl` — pure definitional
evaluation of the interpreter with the list content, `lo`/`hi`, and the
counter symbolic; splits exactly at the data-dependent branch points:
the slice-expression apply, the five `indexGet` applies, the per-pass
`len(s)` apply, and the three value-dependent `if` deliveries). -/

/-- Entry A: driver start → the slice-expression apply point. -/
private theorem mm_entryA_raw (xs : List Int) (ch : Choices) :
    stepFnIter 7 (minMaxSeed xs 2 [] 3)
      (.exec (minMaxCall xs 2) minMaxEnv .stop) ch
      = .ok (.retV (.int (IntKind.normalize .int (xs.length : Int)) .int)
            (.strictK (.sliceExpr false) [.int 0 .int, .addr (.base ⟨2⟩)]
              [] minMaxEnv entryK),
          minMaxSeed xs 2 [] 3, ch) := by
  with_unfolding_all rfl

/-- Entry B: frame entry (param + result-cell allocs), `lo`/`hi`
declaration, first `s[0]` operand walk → the first index-read apply
point. -/
private theorem mm_entryB_raw (xs : List Int) (ch : Choices) :
    stepFnIter 18 (minMaxSeed xs 2 [] 3) (.retV (sliceH xs.length) entryK) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [sliceH xs.length] [] envB rhs1K),
          σE1 xs, ch) := by
  with_unfolding_all rfl

/-- Entry C: first element delivered → the second `s[0]` apply point. -/
private theorem mm_entryC_raw (xs : List Int) (w : Int) (ch : Choices) :
    stepFnIter 5 (σE1 xs) (.retV (.int w .uint64) rhs1K) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [sliceH xs.length] [] envB (rhs2K w)),
          σE1 xs, ch) := by
  with_unfolding_all rfl

/-- Entry D: both reads delivered → the `lo`/`hi` stores (uint64 cell
normalization wraps the values), `i := 1`, the `$forFirst` block → the
loop head. -/
private theorem mm_entryD_raw (xs : List Int) (w1 w2 : Int) (ch : Choices) :
    stepFnIter 34 (σE1 xs) (.retV (.int w2 .uint64) (rhs2K w1)) ch
      = .ok (headCfg,
          mmStateP xs.length xs (IntKind.normalize .uint64 w1)
            (IntKind.normalize .uint64 w2) 1 true, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch: head with the flag up → the `len(s)` apply
point of the exit test (counter unchanged, flag lowered). -/
private theorem mm_dispA_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 25 (mmStateP n l lov hiv iv true) headCfg ch
      = .ok (.retV (sliceH n) (lenApplyK iv),
          mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → `i = i + 1`, then
the `len(s)` apply point (the counter-increment lag: the stored and
riding values carry the machine's double normalization). -/
private theorem mm_dispB_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 29 (mmStateP n l lov hiv iv false) headCfg ch
      = .ok (.retV (sliceH n)
            (lenApplyK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          mmStateP n l lov hiv
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1))) false,
          ch) := by
  with_unfolding_all rfl

/-- Body entry: exit test true → the `s[i]` apply point of the first
conditional. -/
private theorem mm_bodyA_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 11 (mmStateP n l lov hiv iv false) (.retV (.bool true) cmpIfK)
      ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH n] [] envB2 loCmpK),
          mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- Body: element delivered → `lo` load, the `<` compare delivery. -/
private theorem mm_bodyB_raw (n : Nat) (l : List Int) (lov hiv iv w : Int)
    (ch : Choices) :
    stepFnIter 3 (mmStateP n l lov hiv iv false)
      (.retV (.int w .uint64) loCmpK) ch
      = .ok (.retV (.bool (decide (w < lov))) loIfK,
          mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `lo`-branch taken: → the `s[i]` apply point of the assignment's
RHS. -/
private theorem mm_loT_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 12 (mmStateP n l lov hiv iv false) (.retV (.bool true) loIfK)
      ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH n] [] envB3 loStoreK),
          mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `lo`-branch store: element delivered → `lo := w` (uint64 cell
normalization), → the `s[i]` apply point of the SECOND conditional. -/
private theorem mm_loT2_raw (n : Nat) (l : List Int) (lov hiv iv w : Int)
    (ch : Choices) :
    stepFnIter 12 (mmStateP n l lov hiv iv false)
      (.retV (.int w .uint64) loStoreK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH n] [] envB2 hiCmpK),
          mmStateP n l (IntKind.normalize .uint64 w) hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `lo`-branch skipped: → the `s[i]` apply point of the second
conditional, state untouched. -/
private theorem mm_loF_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 9 (mmStateP n l lov hiv iv false) (.retV (.bool false) loIfK)
      ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH n] [] envB2 hiCmpK),
          mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- Second conditional: element delivered → `hi` load, the `>` compare
delivery (the machine's `>` is `<` with swapped operands). -/
private theorem mm_hiB_raw (n : Nat) (l : List Int) (lov hiv iv w : Int)
    (ch : Choices) :
    stepFnIter 3 (mmStateP n l lov hiv iv false)
      (.retV (.int w .uint64) hiCmpK) ch
      = .ok (.retV (.bool (decide (hiv < w))) hiIfK,
          mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `hi`-branch taken: → the `s[i]` apply point of the assignment's
RHS. -/
private theorem mm_hiT_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 12 (mmStateP n l lov hiv iv false) (.retV (.bool true) hiIfK)
      ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH n] [] envB3 hiStoreK),
          mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `hi`-branch store: element delivered → `hi := w` → back to the loop
head. -/
private theorem mm_hiT2_raw (n : Nat) (l : List Int) (lov hiv iv w : Int)
    (ch : Choices) :
    stepFnIter 8 (mmStateP n l lov hiv iv false)
      (.retV (.int w .uint64) hiStoreK) ch
      = .ok (headCfg,
          mmStateP n l lov (IntKind.normalize .uint64 w) iv false, ch) := by
  with_unfolding_all rfl

/-- `hi`-branch skipped: → back to the loop head, state untouched. -/
private theorem mm_hiF_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 5 (mmStateP n l lov hiv iv false) (.retV (.bool false) hiIfK)
      ch
      = .ok (headCfg, mmStateP n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- Exit: test false → break unwinding, `$res0 = lo; $res1 = hi;
return`, frame exit stores into the harness cells 0/1 (each uint64
store re-normalizes) → the driver terminal. -/
private theorem mm_exit_raw (n : Nat) (l : List Int) (lov hiv iv : Int)
    (ch : Choices) :
    stepFnIter 39 (mmStateP n l lov hiv iv false) (.retV (.bool false) cmpIfK)
      ch
      = .ok (.next .stop,
          { types := minMaxLowered.typeDefs.toList,
            functions := minMaxLowered.funcs,
            methods := minMaxLowered.methods,
            heap := [(.base ⟨0⟩,
                      ucell (IntKind.normalize .uint64
                        (IntKind.normalize .uint64 lov))),
                     (.base ⟨1⟩,
                      ucell (IntKind.normalize .uint64
                        (IntKind.normalize .uint64 hiv))),
                     (.base ⟨2⟩, arrCell n l), (.base ⟨3⟩, hcell n),
                     (.base ⟨4⟩, ucell (IntKind.normalize .uint64 lov)),
                     (.base ⟨5⟩, ucell (IntKind.normalize .uint64 hiv)),
                     (.base ⟨6⟩, ucell lov), (.base ⟨7⟩, ucell hiv),
                     (.base ⟨8⟩, icell iv), (.base ⟨9⟩, bcell false)],
            nextAddr := 10 }, ch) := by
  with_unfolding_all rfl

/-! ## Cleaned segments and the loop induction -/

/-- **The entry, cleaned**: seed → the loop head within 67 steps, with
`lo = hi = xs[0]` (`hne` discharges the `s[0]` bounds check — this is
exactly the panic the empty-slice corpus row exhibits). -/
private theorem mm_entry (xs : List Int) (hne : xs ≠ [])
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (ch : Choices) :
    stepFnIter 67 (minMaxSeed xs 2 [] 3)
      (.exec (minMaxCall xs 2) minMaxEnv .stop) ch
      = .ok (headCfg,
          mmStateP xs.length xs (xs.getD 0 0) (xs.getD 0 0) 1 true, ch) := by
  have h0 : 0 < xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hv0 := hxs _ (getD_mem h0)
  have hA := mm_entryA_raw xs ch
  rw [inorm_nat_of_lt hlen] at hA
  have happ1 : applyStrictOp (minMaxSeed xs 2 [] 3) (.sliceExpr false)
      [.addr (.base ⟨2⟩), .int 0 .int, .int ((xs.length : Nat) : Int) .int]
      = .ok (sliceH xs.length, minMaxSeed xs 2 [] 3) :=
    applyStrictOp_sliceExpr_array (lookup_seed xs) (by simp)
  have h8 := stepFnIter_chain hA
    (stepFnIter_one
      (stepFn_strict_apply (done := [.int 0 .int, .addr (.base ⟨2⟩)]) happ1))
  have h26 := stepFnIter_chain h8 (mm_entryB_raw xs ch)
  have hget0 : (⟨xs.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + 0]?
      = some (.int (xs.getD 0 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ h0]
  have hidx1 : stepFn (σE1 xs)
      (.retV (.int 0 .int)
        (.strictK .indexGet [sliceH xs.length] [] envB rhs1K)) ch
      = .ok (.retV (.int (xs.getD 0 0) .uint64) rhs1K, σE1 xs, ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice (lookup_σE1 xs) (Nat.le_refl _) h0 hget0)
  have h27 := stepFnIter_chain h26 (stepFnIter_one hidx1)
  have h32 := stepFnIter_chain h27 (mm_entryC_raw xs (xs.getD 0 0) ch)
  have hidx2 : stepFn (σE1 xs)
      (.retV (.int 0 .int)
        (.strictK .indexGet [sliceH xs.length] [] envB (rhs2K (xs.getD 0 0))))
        ch
      = .ok (.retV (.int (xs.getD 0 0) .uint64) (rhs2K (xs.getD 0 0)),
          σE1 xs, ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice (lookup_σE1 xs) (Nat.le_refl _) h0 hget0)
  have h33 := stepFnIter_chain h32 (stepFnIter_one hidx2)
  have hD := mm_entryD_raw xs (xs.getD 0 0) (xs.getD 0 0) ch
  rw [unorm_of_range hv0.1 hv0.2] at hD
  exact stepFnIter_chain h33 hD

/-- **One iteration, cleaned**: exit test true at counter `m` → the
next exit-test delivery, with the prefix min/max advanced to
`m + 1` — the two data-dependent conditionals resolved by case
analysis, the pure step lemmas connecting the machine's branch
outcomes to `minSpec`/`maxSpec`. -/
private theorem mm_iter (xs : List Int) (m : Nat)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (hm1 : 1 ≤ m) (hm : m < xs.length) (ch : Choices) :
    ∃ k : Nat, k ≤ 96 ∧
      stepFnIter k (cmpState xs m) (.retV (.bool true) cmpIfK) ch
        = .ok (.retV (.bool (decide
              (((m + 1 : Nat) : Int) < ((xs.length : Nat) : Int)))) cmpIfK,
            cmpState xs (m + 1), ch) := by
  have hne : xs ≠ [] := by intro hc; subst hc; simp at hm
  have hw := hxs _ (getD_mem hm)
  have hget : (⟨xs.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int (xs.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ hm]
  -- Phase 1: through the first conditional, to the second `s[i]`
  -- apply point, with lo advanced.
  have phase1 : ∃ k₁ : Nat, k₁ ≤ 40 ∧
      stepFnIter k₁ (cmpState xs m) (.retV (.bool true) cmpIfK) ch
        = .ok (.retV (.int ((m : Nat) : Int) .int)
              (.strictK .indexGet [sliceH xs.length] [] envB2 hiCmpK),
            mmStateP xs.length xs (minSpec (xs.take (m + 1)))
              (maxSpec (xs.take m)) ((m : Nat) : Int) false, ch) := by
    have hA := mm_bodyA_raw xs.length xs (minSpec (xs.take m))
      (maxSpec (xs.take m)) ((m : Nat) : Int) ch
    have hidx1 : stepFn (cmpState xs m)
        (.retV (.int ((m : Nat) : Int) .int)
          (.strictK .indexGet [sliceH xs.length] [] envB2 loCmpK)) ch
        = .ok (.retV (.int (xs.getD m 0) .uint64) loCmpK,
            cmpState xs m, ch) :=
      stepFn_strict_apply
        (applyStrictOp_indexGet_slice (lookup_state _ _ _ _ _ _)
          (Nat.le_refl _) hm hget)
    have hB := mm_bodyB_raw xs.length xs (minSpec (xs.take m))
      (maxSpec (xs.take m)) ((m : Nat) : Int) (xs.getD m 0) ch
    have h15 := stepFnIter_chain
      (stepFnIter_chain hA (stepFnIter_one hidx1)) hB
    by_cases hlt : xs.getD m 0 < minSpec (xs.take m)
    · -- lo updates
      rw [show (decide (xs.getD m 0 < minSpec (xs.take m))) = true from
        decide_eq_true hlt] at h15
      have hC := mm_loT_raw xs.length xs (minSpec (xs.take m))
        (maxSpec (xs.take m)) ((m : Nat) : Int) ch
      have hidx2 : stepFn (cmpState xs m)
          (.retV (.int ((m : Nat) : Int) .int)
            (.strictK .indexGet [sliceH xs.length] [] envB3 loStoreK)) ch
          = .ok (.retV (.int (xs.getD m 0) .uint64) loStoreK,
              cmpState xs m, ch) :=
        stepFn_strict_apply
          (applyStrictOp_indexGet_slice (lookup_state _ _ _ _ _ _)
            (Nat.le_refl _) hm hget)
      have hD := mm_loT2_raw xs.length xs (minSpec (xs.take m))
        (maxSpec (xs.take m)) ((m : Nat) : Int) (xs.getD m 0) ch
      rw [unorm_of_range hw.1 hw.2] at hD
      refine ⟨40, Nat.le_refl _, ?_⟩
      rw [show minSpec (xs.take (m + 1)) = xs.getD m 0 from by
        rw [minSpec_take_succ hm1 hm]; omega]
      exact stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h15 hC) (stepFnIter_one hidx2)) hD
    · -- lo stays
      rw [show (decide (xs.getD m 0 < minSpec (xs.take m))) = false from
        decide_eq_false hlt] at h15
      have hC := mm_loF_raw xs.length xs (minSpec (xs.take m))
        (maxSpec (xs.take m)) ((m : Nat) : Int) ch
      refine ⟨24, by omega, ?_⟩
      rw [show minSpec (xs.take (m + 1)) = minSpec (xs.take m) from by
        rw [minSpec_take_succ hm1 hm]; omega]
      exact stepFnIter_chain h15 hC
  obtain ⟨k₁, hk₁, h1⟩ := phase1
  -- Phase 2: through the second conditional, back to the loop head,
  -- with hi advanced.
  have phase2 : ∃ k₂ : Nat, k₂ ≤ 25 ∧
      stepFnIter k₂
        (mmStateP xs.length xs (minSpec (xs.take (m + 1)))
          (maxSpec (xs.take m)) ((m : Nat) : Int) false)
        (.retV (.int ((m : Nat) : Int) .int)
          (.strictK .indexGet [sliceH xs.length] [] envB2 hiCmpK)) ch
        = .ok (headCfg,
            mmStateP xs.length xs (minSpec (xs.take (m + 1)))
              (maxSpec (xs.take (m + 1))) ((m : Nat) : Int) false, ch) := by
    have hidx3 : stepFn
        (mmStateP xs.length xs (minSpec (xs.take (m + 1)))
          (maxSpec (xs.take m)) ((m : Nat) : Int) false)
        (.retV (.int ((m : Nat) : Int) .int)
          (.strictK .indexGet [sliceH xs.length] [] envB2 hiCmpK)) ch
        = .ok (.retV (.int (xs.getD m 0) .uint64) hiCmpK,
            mmStateP xs.length xs (minSpec (xs.take (m + 1)))
              (maxSpec (xs.take m)) ((m : Nat) : Int) false, ch) :=
      stepFn_strict_apply
        (applyStrictOp_indexGet_slice (lookup_state _ _ _ _ _ _)
          (Nat.le_refl _) hm hget)
    have hB := mm_hiB_raw xs.length xs (minSpec (xs.take (m + 1)))
      (maxSpec (xs.take m)) ((m : Nat) : Int) (xs.getD m 0) ch
    have h4 := stepFnIter_chain (stepFnIter_one hidx3) hB
    by_cases hgt : maxSpec (xs.take m) < xs.getD m 0
    · -- hi updates
      rw [show (decide (maxSpec (xs.take m) < xs.getD m 0)) = true from
        decide_eq_true hgt] at h4
      have hC := mm_hiT_raw xs.length xs (minSpec (xs.take (m + 1)))
        (maxSpec (xs.take m)) ((m : Nat) : Int) ch
      have hidx4 : stepFn
          (mmStateP xs.length xs (minSpec (xs.take (m + 1)))
            (maxSpec (xs.take m)) ((m : Nat) : Int) false)
          (.retV (.int ((m : Nat) : Int) .int)
            (.strictK .indexGet [sliceH xs.length] [] envB3 hiStoreK)) ch
          = .ok (.retV (.int (xs.getD m 0) .uint64) hiStoreK,
              mmStateP xs.length xs (minSpec (xs.take (m + 1)))
                (maxSpec (xs.take m)) ((m : Nat) : Int) false, ch) :=
        stepFn_strict_apply
          (applyStrictOp_indexGet_slice (lookup_state _ _ _ _ _ _)
            (Nat.le_refl _) hm hget)
      have hD := mm_hiT2_raw xs.length xs (minSpec (xs.take (m + 1)))
        (maxSpec (xs.take m)) ((m : Nat) : Int) (xs.getD m 0) ch
      rw [unorm_of_range hw.1 hw.2] at hD
      refine ⟨25, Nat.le_refl _, ?_⟩
      rw [show maxSpec (xs.take (m + 1)) = xs.getD m 0 from by
        rw [maxSpec_take_succ hm1 hm]; omega]
      exact stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h4 hC) (stepFnIter_one hidx4)) hD
    · -- hi stays
      rw [show (decide (maxSpec (xs.take m) < xs.getD m 0)) = false from
        decide_eq_false hgt] at h4
      have hC := mm_hiF_raw xs.length xs (minSpec (xs.take (m + 1)))
        (maxSpec (xs.take m)) ((m : Nat) : Int) ch
      refine ⟨9, by omega, ?_⟩
      rw [show maxSpec (xs.take (m + 1)) = maxSpec (xs.take m) from by
        rw [maxSpec_take_succ hm1 hm]; omega]
      exact stepFnIter_chain h4 hC
  obtain ⟨k₂, hk₂, h2⟩ := phase2
  -- Phase 3: the later-pass dispatch (`i = i + 1`), the exit test.
  have hDisp := mm_dispB_raw xs.length xs (minSpec (xs.take (m + 1)))
    (maxSpec (xs.take (m + 1))) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hDisp
  have hlenap : applyStrictOp
      (mmStateP xs.length xs (minSpec (xs.take (m + 1)))
        (maxSpec (xs.take (m + 1))) ((m + 1 : Nat) : Int) false)
      (.lengthOf (some (.slice (.int .uint64)))) [sliceH xs.length]
      = .ok (.int ((xs.length : Nat) : Int) .int,
          mmStateP xs.length xs (minSpec (xs.take (m + 1)))
            (maxSpec (xs.take (m + 1))) ((m + 1 : Nat) : Int) false) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have h3a := stepFnIter_chain hDisp
    (stepFnIter_one (stepFn_strict_apply (done := []) hlenap))
  have h3 := stepFnIter_chain h3a
    (stepFnIter_one (stepFn_strict_apply
      (done := [.int ((m + 1 : Nat) : Int) .int]) applyStrictOp_lessCmp_int))
  exact ⟨k₁ + (k₂ + 31), by omega,
    stepFnIter_chain h1 (stepFnIter_chain h2 h3)⟩

/-- **The loop**, by strong induction on the remaining measure
`μ = len − m` (unit decrease): from the exit-test delivery of iteration
`m`, the run reaches the driver terminal within `96·μ + 39` steps, at
the pinned terminal state (the prefix min/max at `m = len` IS the whole
list's min/max). -/
private theorem mm_loop (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63) :
    ∀ μ m, 1 ≤ m → m ≤ xs.length → μ = xs.length - m → ∀ ch : Choices,
      ∃ k : Nat, k ≤ 96 * μ + 39 ∧
        stepFnIter k (cmpState xs m)
          (.retV (.bool (decide
            (((m : Nat) : Int) < ((xs.length : Nat) : Int)))) cmpIfK) ch
          = .ok (.next .stop, mmFinal xs, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm1 hmn hμ ch
    rcases Nat.lt_or_ge m xs.length with hlt | hge
    · -- iterate
      rw [show (decide (((m : Nat) : Int) < ((xs.length : Nat) : Int)))
          = true from decide_eq_true (by omega)]
      obtain ⟨k₁, hk₁, hiter⟩ := mm_iter xs m hxs hlen hm1 hlt ch
      obtain ⟨k₂, hk₂, hrest⟩ := ih (xs.length - (m + 1)) (by omega) (m + 1)
        (by omega) (by omega) rfl ch
      exact ⟨k₁ + k₂, by omega, stepFnIter_chain hiter hrest⟩
    · -- exit: m = len
      have hmeq : m = xs.length := by omega
      subst hmeq
      have hne : xs ≠ [] := by
        intro hc
        rw [hc] at hm1
        simp at hm1
      rw [show (decide (((xs.length : Nat) : Int) < ((xs.length : Nat) : Int)))
          = false from decide_eq_false (by omega)]
      have hlo := minTake_range (m := xs.length) hxs hm1 hne
      have hhi := maxTake_range (m := xs.length) hxs hm1 hne
      have hX := mm_exit_raw xs.length xs (minSpec (xs.take xs.length))
        (maxSpec (xs.take xs.length)) ((xs.length : Nat) : Int) ch
      rw [unorm_of_range hlo.1 hlo.2, unorm_of_range hlo.1 hlo.2,
        unorm_of_range hhi.1 hhi.2, unorm_of_range hhi.1 hhi.2,
        List.take_length] at hX
      refine ⟨39, by omega, ?_⟩
      show stepFnIter 39
          (mmStateP xs.length xs (minSpec (xs.take xs.length))
            (maxSpec (xs.take xs.length)) ((xs.length : Nat) : Int) false)
          (.retV (.bool false) cmpIfK) ch
        = .ok (.next .stop, mmFinal xs, ch)
      rw [List.take_length]
      exact hX

/-- **The canonical run, end to end**: from the tight canonical seed
the driver completes at the `.normal` terminal within `37 + 96·len`
steps, at the pinned terminal state. -/
private theorem mm_runs (xs : List Int) (hne : xs ≠ [])
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 37 + 96 * xs.length ∧
      stepFnIter k (minMaxSeed xs 2 [] 3)
        (.exec (minMaxCall xs 2) minMaxEnv .stop) ch
        = .ok (.next .stop, mmFinal xs, ch) := by
  have h1len : 1 ≤ xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hE := mm_entry xs hne hxs hlen ch
  have hDA := mm_dispA_raw xs.length xs (xs.getD 0 0) (xs.getD 0 0) 1 ch
  have h92 := stepFnIter_chain hE hDA
  have hlenap : applyStrictOp
      (mmStateP xs.length xs (xs.getD 0 0) (xs.getD 0 0) 1 false)
      (.lengthOf (some (.slice (.int .uint64)))) [sliceH xs.length]
      = .ok (.int ((xs.length : Nat) : Int) .int,
          mmStateP xs.length xs (xs.getD 0 0) (xs.getD 0 0) 1 false) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have h93 := stepFnIter_chain h92
    (stepFnIter_one (stepFn_strict_apply (done := []) hlenap))
  have h94 := stepFnIter_chain h93
    (stepFnIter_one (stepFn_strict_apply
      (done := [.int 1 .int]) applyStrictOp_lessCmp_int))
  obtain ⟨k, hk, hloop⟩ := mm_loop xs hxs hlen (xs.length - 1) 1
    (Nat.le_refl 1) h1len rfl ch
  refine ⟨94 + k, by omega, ?_⟩
  refine stepFnIter_chain ?_ hloop
  show stepFnIter 94 (minMaxSeed xs 2 [] 3)
      (.exec (minMaxCall xs 2) minMaxEnv .stop) ch
    = .ok (.retV (.bool (decide
          (((1 : Nat) : Int) < ((xs.length : Nat) : Int)))) cmpIfK,
        mmStateP xs.length xs (minSpec (xs.take 1)) (maxSpec (xs.take 1))
          ((1 : Nat) : Int) false, ch)
  rw [minSpec_take_one hne, maxSpec_take_one hne]
  exact h94

/-! ## The canonical-placement total run -/

/-- **Total correctness at the canonical placement**: past fuel
`37 + 96·len`, at every choice stream, execution completes normally at
the pinned terminal state. -/
private theorem minmax_total_canonical (xs : List Int) (hne : xs ≠ [])
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63) :
    ∀ fuel : Nat, 37 + 96 * xs.length ≤ fuel → ∀ ch : Choices,
      execStmtLoop fuel (minMaxSeed xs 2 [] 3)
        (.exec (minMaxCall xs 2) minMaxEnv .stop) ch
        = .ok (.normal (mmFinal xs), ch) := by
  intro fuel hfuel ch
  obtain ⟨k, hk, hrun⟩ := mm_runs xs hne hxs hlen ch
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]

/-! ## The framed form: the frame theorem consumed at an
input-RELOCATING renaming

The canonical placement fixes the two harness result cells (0, 1 —
`ρ`-fixed) and relocates the input cell `2 ↦ base` and the fresh region
`[3, ∞) ↦ [na, ∞)`. The canonical seed is TIGHT (dom = {0, 1, 2},
na₀ = 3), exactly what `fr_avoid`'s seed discharge needs. -/

open GoLean.Frame

/-- The input-relocating renaming: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ base`,
`3 + k ↦ na + k`. -/
private def relocShift (base na : Nat) : Nat → Nat :=
  fun x => if x = 0 then 0 else if x = 1 then 1 else if x = 2 then base
    else na + (x - 3)

/-- Loc-freedom of the wrapped-integer backing array (the rename
identity's premise). -/
private theorem locSup_mapU (l : List Int) :
    GoValue.locSup (.array ⟨l.map (fun v => .int v .uint64)⟩) = 0 := by
  show goValueListSup (l.map (fun v => .int v .uint64)) = 0
  induction l with
  | nil => rfl
  | cons v rest ih => simpa [goValueListSup, GoValue.locSup] using ih

/-- The seed simulation: the canonical seed beside the framed seed at
an arbitrary admissible placement, through the relocating shift. -/
private theorem mmSeedFrameSim (xs : List Int) (base : Nat) (fr : Heap)
    (na : Nat) (hb0 : base ≠ 0) (hb1 : base ≠ 1)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hf1 : Heap.lookup fr (.base ⟨1⟩) = none)
    (hwf : MachineWf
      { functions := minMaxLowered.funcs,
        heap := resCells ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (minMaxCall xs base) minMaxEnv .stop)) :
    FrameSim (relocShift base na) 3 na fr (minMaxSeed xs 2 [] 3)
      (minMaxSeed xs base fr na) := by
  have hs := hwf.1
  simp only [StateWf, ExecState.locSup, Heap.locSup, resCells, sliceCells,
    List.cons_append, List.nil_append, Loc.locSup, Loc.rootBase,
    HeapCell.locSup, GoValue.locSup, Nat.max_le] at hs
  have hbase : base + 1 ≤ na := by omega
  have h2na : 2 ≤ na := by omega
  have hfrsup : Heap.locSup fr ≤ na := by omega
  have hren2 : renameLoc (relocShift base na) (.base ⟨2⟩) = .base ⟨base⟩ := by
    simp [renameLoc, relocShift]
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- inj
    intro x y hxy
    simp only [relocShift] at hxy
    repeat' split at hxy
    all_goals omega
  · -- shift
    intro k
    simp only [relocShift]
    repeat' split
    all_goals omega
  · -- next_eq: na = ρ 3
    simp [minMaxSeed, relocShift]
  · -- alloc_reg
    exact Nat.le_refl 3
  · -- lookup_img
    intro l
    by_cases hl0 : l = .base ⟨0⟩
    · subst hl0
      rw [show renameLoc (relocShift base na) (.base ⟨0⟩) = .base ⟨0⟩ from by
        simp [renameLoc, relocShift]]
      simp [minMaxSeed, resCells, sliceCells, Heap.lookup, renameCell,
        renameValue]
    · by_cases hl1 : l = .base ⟨1⟩
      · subst hl1
        rw [show renameLoc (relocShift base na) (.base ⟨1⟩) = .base ⟨1⟩ from by
          simp [renameLoc, relocShift]]
        simp [minMaxSeed, resCells, sliceCells, Heap.lookup, renameCell,
          renameValue]
      · by_cases hl2 : l = .base ⟨2⟩
        · subst hl2
          rw [hren2]
          have hne0 : ((.base ⟨0⟩ : Loc) == (.base ⟨base⟩ : Loc)) = false :=
            beq_false_of_ne (by
              intro hc
              exact hb0 (by
                injection hc with h
                injection h with h'
                exact h'.symm))
          have hne1 : ((.base ⟨1⟩ : Loc) == (.base ⟨base⟩ : Loc)) = false :=
            beq_false_of_ne (by
              intro hc
              exact hb1 (by
                injection hc with h
                injection h with h'
                exact h'.symm))
          have hcell : renameCell (relocShift base na)
              (⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ : HeapCell)
              = ⟨some (.array xs.length (.int .uint64)),
                 .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
            simp [renameCell, renameValue_locFree _ _ (locSup_mapU xs)]
          simp only [minMaxSeed, resCells, sliceCells, List.cons_append,
            List.nil_append, Heap.lookup, hne0, hne1]
          simp [hcell]
        · -- l outside the seed's domain
          have hcanon : Heap.lookup (minMaxSeed xs 2 [] 3).heap l = none := by
            have hne0 : ((.base ⟨0⟩ : Loc) == l) = false :=
              beq_false_of_ne (fun h => hl0 h.symm)
            have hne1 : ((.base ⟨1⟩ : Loc) == l) = false :=
              beq_false_of_ne (fun h => hl1 h.symm)
            have hne2 : ((.base ⟨2⟩ : Loc) == l) = false :=
              beq_false_of_ne (fun h => hl2 h.symm)
            simp only [minMaxSeed, resCells, sliceCells, List.cons_append,
              List.nil_append, Heap.lookup, hne0, hne1, hne2]
            rfl
          rw [hcanon]
          -- the framed seed's three keys all miss `renameLoc ρ l`
          have hkey : ∀ K : Nat, (K = 0 ∨ K = 1 ∨ K = base) →
              ((.base ⟨K⟩ : Loc) == renameLoc (relocShift base na) l)
                = false := by
            intro K hK
            refine beq_false_of_ne (fun hc => ?_)
            cases l with
            | base a =>
                simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at hc
                by_cases ha0 : a.id = 0
                · exact hl0 (by
                    obtain ⟨id⟩ := a
                    simp only at ha0
                    subst ha0
                    rfl)
                · by_cases ha1 : a.id = 1
                  · exact hl1 (by
                      obtain ⟨id⟩ := a
                      simp only at ha1
                      subst ha1
                      rfl)
                  · by_cases ha2 : a.id = 2
                    · exact hl2 (by
                        obtain ⟨id⟩ := a
                        simp only at ha2
                        subst ha2
                        rfl)
                    · simp only [relocShift, if_neg ha0, if_neg ha1,
                        if_neg ha2] at hc
                      omega
            | field b tid f => simp [renameLoc] at hc
            | index b i => simp [renameLoc] at hc
          simp only [minMaxSeed, resCells, sliceCells, List.cons_append,
            List.nil_append, Heap.lookup, hkey 0 (by omega),
            hkey 1 (by omega), hkey base (by omega)]
          rfl
  · -- frame_pres
    intro l c hl
    have hne0 : ((.base ⟨0⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hf0] at hl
      cases hl
    have hne1 : ((.base ⟨1⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hf1] at hl
      cases hl
    have hneb : ((.base ⟨base⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hfb] at hl
      cases hl
    simp only [minMaxSeed, resCells, sliceCells, List.cons_append,
      List.nil_append, Heap.lookup, hne0, hne1, hneb]
    exact hl
  · -- fr_avoid
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      simpa [relocShift] using hf0
    · by_cases ha1 : a = 1
      · subst ha1
        simpa [relocShift] using hf1
      · by_cases ha2 : a = 2
        · subst ha2
          simpa [relocShift] using hfb
        · cases hlk : Heap.lookup fr (.base ⟨relocShift base na a⟩) with
          | none => rfl
          | some c =>
              exfalso
              have hkey := Heap.lookup_key_locSup hlk
              simp only [Loc.locSup, Loc.rootBase] at hkey
              simp only [relocShift, if_neg ha0, if_neg ha1, if_neg ha2]
                at hkey
              omega
  · -- bodies_inv
    exact renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
      (fs := minMaxLowered.funcs)
      (by decide : funcListSup minMaxLowered.funcs.toList ≤ 0)

/-- The driver configuration renames to the framed driver: the
relocating shift carries the `locLit` base pointer `2 ↦ base` and fixes
the harness cells `0`, `1` (so `minMaxEnv` is `ρ`-invariant) — the
∀-placement realization. -/
private theorem mm_cfg_ren (xs : List Int) (base na : Nat) :
    renameConfig (relocShift base na)
      (.exec (minMaxCall xs 2) minMaxEnv .stop)
      = .exec (minMaxCall xs base) minMaxEnv .stop := by
  simp [renameConfig, renameCont, renameEnv, renameScope, renameStmt,
    minMaxCall, minMaxEnv, renameExprList, renameExpr, renameOptExpr,
    renameAssignee, renameLoc, relocShift]

/-! ## Terminal-state readout facts -/

private theorem lookup_final0 (xs : List Int) :
    Heap.lookup (mmFinal xs).heap (.base ⟨0⟩)
      = some (ucell (minSpec xs)) := rfl

private theorem lookup_final1 (xs : List Int) :
    Heap.lookup (mmFinal xs).heap (.base ⟨1⟩)
      = some (ucell (maxSpec xs)) := rfl

private theorem lookup_final2 (xs : List Int) :
    Heap.lookup (mmFinal xs).heap (.base ⟨2⟩)
      = some (arrCell xs.length xs) := rfl

/-! ## The headline -/

/-- **The framed total form — proof-side supporting layer per §11 (the
memory-quantified form, kept)**: *for any nonempty list
`xs` of uint64 values, wherever it lives in memory, with anything else
present: `$mn, $mx = minMax(s)` completes normally — past one fuel
bound, at every nondeterminism-choice stream — the result cells then
hold exactly `minSpec xs` and `maxSpec xs`, the input's backing cell is
UNCHANGED (the program is read-only on its input), and no other memory
is touched.*

Hypotheses recorded honestly (module docstring for the full reasoning):
`hne` — Go PANICS on the empty slice at `s[0]` (corpus row
`examples/minmax/empty-panics`); `hb0`/`hb1` — the harness result cells
sit at addresses 0 and 1, so the input must not collide with them;
`hlen` — Go's own `int` domain for the driver's `len` literal (the
reverse precedent).

The proof: total correctness at the TIGHT canonical placement
(`base = 2`, empty frame — direct machine-step segments + strong
induction on the remaining measure `len − m`, both value and completion
halves from the one induction), then the executable frame theorem's
success-run transfer `execStmtLoop_ren` at the input-RELOCATING
renaming `relocShift base na`. Value readout transfers through the
terminal `FrameSim`'s pointwise heap characterization (cells 0/1 are
`ρ`-fixed; the backing cell maps `2 ↦ base`); frame preservation is its
`frame_pres` clause verbatim. The USER-FACING headline is `minmax_ok`
below (harness ruling 2026-08-13, design note §11); this
memory-quantified form stays as the supporting layer. -/
theorem minmax_framed (xs : List Int) (hne : xs ≠ [])
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (base : Nat) (hb0 : base ≠ 0) (hb1 : base ≠ 1)
    (fr : Heap) (na : Nat)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hf1 : Heap.lookup fr (.base ⟨1⟩) = none)
    (hwf : MachineWf
      { functions := minMaxLowered.funcs,
        heap := resCells ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (minMaxCall xs base) minMaxEnv .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel minMaxEnv (minMaxSeed xs base fr na) ch
            (minMaxCall xs base)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int (minSpec xs) .uint64)
        ∧ loadLoc σf (.base ⟨1⟩) = .ok (.int (maxSpec xs) .uint64)
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c := by
  have hSF := mmSeedFrameSim xs base fr na hb0 hb1 hfb hf0 hf1 hwf
  refine ⟨37 + 96 * xs.length, fun fuel hfuel ch => ?_⟩
  have hrunC := minmax_total_canonical xs hne hxs hlen fuel hfuel ch
  obtain ⟨outF, hrunF, hout⟩ := Frame.execStmtLoop_ren fuel hSF hrunC
  rw [mm_cfg_ren xs base na] at hrunF
  cases outF with
  | normal σF =>
      obtain ⟨hSF', -⟩ := hout
      refine ⟨σF, ch, hrunF, ?_, ?_, ?_, ?_⟩
      · have hlook := hSF'.lookup_some (lookup_final0 xs)
        rw [show renameLoc (relocShift base na) (.base ⟨0⟩) = .base ⟨0⟩ from
          by simp [renameLoc, relocShift]] at hlook
        rw [show renameCell (relocShift base na) (ucell (minSpec xs))
            = ucell (minSpec xs) from rfl] at hlook
        simp [loadLoc, hlook]
      · have hlook := hSF'.lookup_some (lookup_final1 xs)
        rw [show renameLoc (relocShift base na) (.base ⟨1⟩) = .base ⟨1⟩ from
          by simp [renameLoc, relocShift]] at hlook
        rw [show renameCell (relocShift base na) (ucell (maxSpec xs))
            = ucell (maxSpec xs) from rfl] at hlook
        simp [loadLoc, hlook]
      · have hlook := hSF'.lookup_some (lookup_final2 xs)
        rw [show renameLoc (relocShift base na) (.base ⟨2⟩) = .base ⟨base⟩
          from by simp [renameLoc, relocShift]] at hlook
        have hcell : renameCell (relocShift base na)
            (arrCell xs.length xs) = arrCell xs.length xs := by
          simp [renameCell, renameValue_locFree _ _ (locSup_mapU xs)]
        rw [hcell] at hlook
        exact hlook
      · intro a c hac
        exact hSF'.frame_pres (.base ⟨a⟩) c hac
  | returned σF => exact hout.elim
  | broke σF => exact hout.elim
  | continued σF => exact hout.elim

/-- **The framed D1 run-conditioned twin — proof-side supporting layer
per §11 (the memory-quantified form, kept)**: any normal completion of
the framed driver, at ANY fuel and choice stream, delivers the same
four clauses — derived from `minmax_framed` via
`normal_readout_of_total`, no second walk. -/
theorem minmax_framed_readout (xs : List Int) (hne : xs ≠ [])
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (base : Nat) (hb0 : base ≠ 0) (hb1 : base ≠ 1)
    (fr : Heap) (na : Nat)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hf1 : Heap.lookup fr (.base ⟨1⟩) = none)
    (hwf : MachineWf
      { functions := minMaxLowered.funcs,
        heap := resCells ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (minMaxCall xs base) minMaxEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel minMaxEnv (minMaxSeed xs base fr na) ch
          (minMaxCall xs base)
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int (minSpec xs) .uint64)
      ∧ loadLoc σf (.base ⟨1⟩) = .ok (.int (maxSpec xs) .uint64)
      ∧ Heap.lookup σf.heap (.base ⟨base⟩)
          = some ⟨some (.array xs.length (.int .uint64)),
              .array ⟨xs.map (fun v => .int v .uint64)⟩⟩
      ∧ ∀ (a : Nat) (c : HeapCell),
          Heap.lookup fr (.base ⟨a⟩) = some c →
          Heap.lookup σf.heap (.base ⟨a⟩) = some c :=
  GoLean.Surface.normal_readout_of_total
    (minmax_framed xs hne hxs hlen base hb0 hb1 fr na hfb hf0 hf1 hwf)

/-! ## The harness restatement (harness ruling 2026-08-13, design note
`docs/2026-08-12_example-spec-form.md` §11)

The USER-FACING form: one fixed three-phase Go harness

```go
func minmax_harness(n, seed uint64) (uint64, uint64) {
    s := make([]uint64, n)              // setup: build the input family
    for i := uint64(0); i < n; i++ { s[i] = seed + i }
    return minMax(s)                    // call under test; returned pair
}                                       // is the observable
```

stated over the machine's native function entry
`runFunctionWithContextM`: termination + the returned values only — no
heap readback, no seed/cell/frame vocabulary (the implicit framing
property is inherent in the empty-heap entry).

**INPUT-FAMILY HONESTY** (recorded per §11's designed-not-built input
pick): the `(n, seed)` quantification covers exactly the `mmFamily`
family `s[i] = (seed + i) mod 2^64` — an input FAMILY, honestly weaker
than a ∀xs claim over all slices (that form is `minmax_framed` above,
the kept proof-side layer; the ∀xs HARNESS form waits on the
choice-consuming input pick, §11). The family WRAPS at `2^64`
deliberately: when `seed + i` crosses the boundary the wrapped values
fall BELOW `seed`, so min/max are genuinely data-dependent — the
minimum is not always `s[0]` and the maximum not always `s[n-1]`; that
is the family's value as a test vector.

Statement hypotheses, recorded honestly: `h1 : 1 ≤ n` is Go's OWN
empty-slice panic boundary (`minMax` of an empty slice panics at
`s[0]`; corpus row `examples/minmax/empty-panics` pins it — the claim
as stated would be false at `n = 0`); `hn : n < 2^63` is Go's `int`
domain for `len` (the reverse precedent); `hseed : seed < 2^64` is the
argument's own type domain.

Proof route: the setup loop gets its own plain induction (invariant:
backing = family-prefix ++ zeros; the element store discharged by
`SliceMem.storeTarget_slice_u64` with `l := prefix ++ replicate`); the
`make([]uint64, n)` apply at SYMBOLIC `n` is one conditioned step
(`applyStmtOp_makeSlice_u64`, via the shared
`buildDefaultArrayValue_int`); then the minMax segments and the
prefix-min/max strong induction port from the framed layer above at
the harness's address layout, over `mmFamily n seed` as the abstract
list (elements in range by construction — the `% 2^64` in the family).
Address layout: 0 = `n`, 1 = `seed`, 2/3 = the harness results,
4 = `$c12`, 5 = the backing array, 6 = `s`, 7 = the setup `i`,
8 = the setup `$forFirst`, 9/10 = `$c13`/`$c14`, 11–17 = the minMax
frame (`s`, `$res0`, `$res1`, `lo`, `hi`, `i`, `$forFirst`); allocator
parked at 18 for the whole minMax loop. -/

/-- **The input family** (in the headline statement): the slice the
harness's setup loop builds — `s[i] = (seed + i) mod 2^64`, the
machine's own wrapping uint64 addition, as abstract data. -/
def mmFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))

/-- The harness's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def mmHarnessFunc : Func :=
  { id := { key := "minmax_harness" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 },
                 { id := "$res1", typ := .int .uint64 }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "$c12", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c12") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "s", typ := .slice (.int .uint64) },
            .assign (.var "s") (.var "$c12")],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) shBody]],
        .seqn
          #[.initialization { id := "$c13", typ := .int .uint64 },
            .initialization { id := "$c14", typ := .int .uint64 },
            .call #[.var "$c13", .var "$c14"] ⟨"minMax"⟩ #[.var "s"]],
        .seqn
          #[.assign (.var "$res0") (.var "$c13"),
            .assign (.var "$res1") (.var "$c14"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
where
  /-- The setup loop's `for`-desugar body. -/
  shBody : Stmt :=
    .block #[]
      #[.ifThenElse (.var "$forFirst")
          (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
        .seqn #[],
        .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
        .block #[]
          #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
              (.add (.var "seed") (.var "i"))]]]

/-- The lowering pin: the harness in the theorem IS the frontend's
lowering of the corpus harness. -/
example : findFunctionIn? minMaxLowered.funcs ⟨"minmax_harness"⟩
    = some mmHarnessFunc := rfl

/-! ### The pure layer: the family and the setup-prefix surgery -/

private theorem mmFamily_length (n seed : Nat) :
    (mmFamily n seed).length = n := by
  simp [mmFamily]

private theorem mmFamily_ne_nil {n seed : Nat} (h1 : 1 ≤ n) :
    mmFamily n seed ≠ [] := by
  intro hc
  have := congrArg List.length hc
  simp [mmFamily_length] at this
  omega

private theorem mmFamily_getD {n seed i : Nat} (hi : i < n) :
    (mmFamily n seed).getD i 0 = (((seed + i) % 2 ^ 64 : Nat) : Int) := by
  simp [mmFamily, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]

private theorem mmFamily_range (n seed : Nat) :
    ∀ v ∈ mmFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [mmFamily, List.mem_map] at hv
  obtain ⟨i, -, rfl⟩ := hv
  constructor
  · omega
  · exact_mod_cast Nat.mod_lt _ (by omega)

/-- The setup-loop invariant list: the built family prefix, then the
`make`'s zeros. -/
private def setupList (n seed i : Nat) : List Int :=
  (mmFamily n seed).take i ++ List.replicate (n - i) 0

private theorem setupList_zero (n seed : Nat) :
    setupList n seed 0 = List.replicate n 0 := by
  simp [setupList]

private theorem setupList_full (n seed : Nat) :
    setupList n seed n = mmFamily n seed := by
  rw [setupList, Nat.sub_self, List.replicate_zero, List.append_nil,
    List.take_of_length_le (Nat.le_of_eq (mmFamily_length n seed))]

private theorem setupList_length {n seed i : Nat} (hi : i ≤ n) :
    (setupList n seed i).length = n := by
  simp only [setupList, List.length_append, List.length_take,
    List.length_replicate, mmFamily_length]
  omega

private theorem setupList_range (n seed i : Nat) :
    ∀ v ∈ setupList n seed i, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact mmFamily_range n seed v (List.mem_of_mem_take h)
  · rw [List.eq_of_mem_replicate h]
    omega

private theorem set_append_first {xs ys : List Int} {w : Int} :
    (xs ++ ys).set xs.length w = xs ++ ys.set 0 w := by
  induction xs with
  | nil => simp
  | cons x t ih => simp only [List.cons_append, List.length_cons, List.set, ih]

/-- **One setup store advances the prefix**: writing the family value
at position `i` turns invariant list `i` into invariant list `i + 1`. -/
private theorem setupList_set {n seed i : Nat} (hi : i < n) :
    (setupList n seed i).set i (((seed + i) % 2 ^ 64 : Nat) : Int)
      = setupList n seed (i + 1) := by
  have hlen : ((mmFamily n seed).take i).length = i := by
    simp only [List.length_take, mmFamily_length]
    omega
  have hset := set_append_first (xs := (mmFamily n seed).take i)
    (ys := List.replicate (n - i) 0)
    (w := (((seed + i) % 2 ^ 64 : Nat) : Int))
  rw [hlen] at hset
  rw [setupList, hset, show n - i = (n - i - 1) + 1 from by omega,
    List.replicate_succ, List.set_cons_zero, setupList,
    take_succ_snoc (by rw [mmFamily_length]; exact hi), mmFamily_getD hi,
    show n - (i + 1) = n - i - 1 from by omega]
  simp [List.append_assoc]

/-! ### Machine-integer facts for the setup arithmetic -/

/-- The wrapping normal form of a `Nat`-cast sum — the machine's uint64
`+` IS the family's `% 2^64`. -/
private theorem unorm_nat_wrap (x : Nat) :
    IntKind.normalize .uint64 ((x : Nat) : Int)
      = ((x % 2 ^ 64 : Nat) : Int) := by
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed]
  simp only [Bool.false_eq_true, if_false]
  omega

private theorem unorm_nat_of_lt {x : Nat} (h : x < 2 ^ 64) :
    IntKind.normalize .uint64 ((x : Nat) : Int) = ((x : Nat) : Int) :=
  unorm_of_range (by omega) (by exact_mod_cast h)

/-! ### Harness-layout environments, continuations, and states -/

private def hEnvA : LocalEnv :=
  [[("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
    ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]]
private def hEnvMS : LocalEnv :=
  [[("$c12", .base ⟨4⟩)],
   [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
    ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]]
private def hEnvS : LocalEnv :=
  [[("s", .base ⟨6⟩), ("$c12", .base ⟨4⟩)],
   [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
    ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]]
private def shEnvIn : LocalEnv :=
  [("$forFirst", .base ⟨8⟩)] :: [("i", .base ⟨7⟩)] :: hEnvS
private def shEnvC : LocalEnv := [] :: shEnvIn
private def shEnvB2 : LocalEnv := [] :: shEnvC
private def hEnvC : LocalEnv :=
  [[("$c14", .base ⟨10⟩), ("$c13", .base ⟨9⟩),
    ("s", .base ⟨6⟩), ("$c12", .base ⟨4⟩)],
   [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩),
    ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]]

private abbrev hSInitSeqn : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice (.int .uint64) },
          .assign (.var "s") (.var "$c12")]
private abbrev shLoopBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) mmHarnessFunc.shBody]]
private abbrev hCallSeqn : Stmt :=
  .seqn #[.initialization { id := "$c13", typ := .int .uint64 },
          .initialization { id := "$c14", typ := .int .uint64 },
          .call #[.var "$c13", .var "$c14"] ⟨"minMax"⟩ #[.var "s"]]
private abbrev hEpilogue : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c13"),
          .assign (.var "$res1") (.var "$c14"),
          .returnStmt]
private abbrev shStoreBlock : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.var "i"))]]

/-- The continuation after the `makeSlice` statement. -/
private def hkMS : Cont :=
  .seq [hSInitSeqn, shLoopBlock, hCallSeqn, hEpilogue] hEnvMS
    (.frame [] [] [] [] .stop false)
/-- The continuation below the setup loop. -/
private def shTailK : Cont :=
  .seq [hCallSeqn, hEpilogue] hEnvS (.frame [] [] [] [] .stop false)
private def shHeadTail : Cont :=
  .seq [] shEnvIn (.seq [] ([("i", .base ⟨7⟩)] :: hEnvS) shTailK)
/-- The setup loop-head configuration. -/
private def shHeadCfg : Config :=
  .exec (.while (.boolLit true) mmHarnessFunc.shBody) shEnvIn shHeadTail
private def shLoopK : Cont :=
  .loop (.boolLit true) mmHarnessFunc.shBody shEnvIn shHeadTail
/-- The setup exit test's delivery continuation (segment split
point). -/
private def shCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt shEnvC (.seq [shStoreBlock] shEnvC shLoopK)
private def shStTail : Cont :=
  .seq [] shEnvB2 (.seq [] shEnvC shLoopK)

private abbrev sliceH5 (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨5⟩), 0, n, n⟩
private abbrev hcellH (n : Nat) : HeapCell :=
  ⟨some (.slice (.int .uint64)), sliceH5 n⟩

/-- The prelude-built entry seed (two bound parameters, two zeroed
result cells). -/
private def mhSeedI (nv sv : Int) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs, methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell 0), (.base ⟨3⟩, ucell 0)],
    nextAddr := 4 }

/-- The harness-body start configuration (the prelude's `c₀`). -/
private def mhc₀ : Config :=
  .exec mmHarnessFunc.body hEnvA (.frame [] [] [] [] .stop false)

/-- At the `makeSlice` apply point (`$c12` allocated at its default). -/
private def σMS (nv sv : Int) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs, methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell 0), (.base ⟨3⟩, ucell 0),
             (.base ⟨4⟩, ⟨some (.slice (.int .uint64)),
                .slice ⟨none, 0, 0, 0⟩⟩)],
    nextAddr := 5 }

/-- After the `makeSlice` apply: the handle at 4, the zeroed backing at
5. -/
private def σMS' (nv sv : Int) (n : Nat) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs, methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell 0), (.base ⟨3⟩, ucell 0),
             (.base ⟨4⟩, hcellH n),
             (.base ⟨5⟩, arrCell n (List.replicate n 0))],
    nextAddr := 6 }

/-- The setup-loop state: parameters, the handle cells, the backing
list `l`, the setup counter, the setup flag. -/
private def shState (nv sv : Int) (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs, methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell 0), (.base ⟨3⟩, ucell 0),
             (.base ⟨4⟩, hcellH n), (.base ⟨5⟩, arrCell n l),
             (.base ⟨6⟩, hcellH n), (.base ⟨7⟩, ucell iv),
             (.base ⟨8⟩, bcell ffv)],
    nextAddr := 9 }

/-! ### The minMax frame at the harness layout -/

private def mEnvB : LocalEnv :=
  [[("hi", .base ⟨15⟩), ("lo", .base ⟨14⟩)],
   [("$res1", .base ⟨13⟩), ("$res0", .base ⟨12⟩), ("s", .base ⟨11⟩)]]
private def mEnvI : LocalEnv := [("i", .base ⟨16⟩)] :: mEnvB
private def mEnvIn : LocalEnv := [("$forFirst", .base ⟨17⟩)] :: mEnvI
private def mEnvC : LocalEnv := [] :: mEnvIn
private def mEnvB2 : LocalEnv := [] :: mEnvC
private def mEnvB3 : LocalEnv := [] :: mEnvB2

private def mShapes : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "$c13"]), (.chain [], [.ref "$c14"])]
private def mFrameK : Cont :=
  .frame mShapes hEnvC [.base ⟨12⟩, .base ⟨13⟩] []
    (.seq [hEpilogue] hEnvC (.frame [] [] [] [] .stop false)) false
private def mEntryTail : Cont := .seq [mmIffBlock, mmTailSeqn] mEnvB mFrameK
private def mtref14 : TargetRef := .chain (.addr (.base ⟨14⟩)) [] []
private def mtref15 : TargetRef := .chain (.addr (.base ⟨15⟩)) [] []
private def mRhs1K : Cont :=
  .rhsK .vals [mtref14, mtref15] []
    [.indexGet (.var "s") (.intLit 0 .int)] (.seqn #[]) mEnvB mEntryTail
private def mRhs2K (w : Int) : Cont :=
  .rhsK .vals [mtref14, mtref15] [.int w .uint64] [] (.seqn #[]) mEnvB
    mEntryTail

private def mHeadTail : Cont :=
  .seq [] mEnvIn (.seq [] mEnvI (.seq [mmTailSeqn] mEnvB mFrameK))
/-- The minMax loop-head configuration at the harness layout. -/
private def mHeadCfg : Config :=
  .exec (.while (.boolLit true) mmWhileBody) mEnvIn mHeadTail
private def mLoopK : Cont := .loop (.boolLit true) mmWhileBody mEnvIn mHeadTail
private def mCmpIfK : Cont :=
  .ifK (.seqn #[]) .breakStmt mEnvC
    (.seq [.block #[] #[mmLoIf, mmHiIf]] mEnvC mLoopK)
private def mLenApplyK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice (.int .uint64)))) [] [] mEnvC
    (.strictK .lessCmp [.int iv .int] [] mEnvC mCmpIfK)

private def mLoIfK : Cont :=
  .ifK (.block #[]
      #[.seqn #[.assign (.var "lo") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[]) mEnvB2 (.seq [mmHiIf] mEnvB2 (.seq [] mEnvC mLoopK))
private def mLoCmpK : Cont := .strictK .lessCmp [] [.var "lo"] mEnvB2 mLoIfK
private def mLoStoreK : Cont :=
  .rhsK .vals [mtref14] [] [] (.seqn #[]) mEnvB3
    (.seq [] mEnvB3 (.seq [mmHiIf] mEnvB2 (.seq [] mEnvC mLoopK)))
private def mHiIfK : Cont :=
  .ifK (.block #[]
      #[.seqn #[.assign (.var "hi") (.indexGet (.var "s") (.var "i"))]])
    (.seqn #[]) mEnvB2 (.seq [] mEnvB2 (.seq [] mEnvC mLoopK))
private def mHiCmpK : Cont := .strictK .greaterCmp [] [.var "hi"] mEnvB2 mHiIfK
private def mHiStoreK : Cont :=
  .rhsK .vals [mtref15] [] [] (.seqn #[]) mEnvB3
    (.seq [] mEnvB3 (.seq [] mEnvB2 (.seq [] mEnvC mLoopK)))

/-- The mid-entry state: minMax frame entered, `lo`/`hi` at defaults
(the setup counter parked at `n`). -/
private def σM1 (nv sv : Int) (n : Nat) (l : List Int) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs, methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell 0), (.base ⟨3⟩, ucell 0),
             (.base ⟨4⟩, hcellH n), (.base ⟨5⟩, arrCell n l),
             (.base ⟨6⟩, hcellH n), (.base ⟨7⟩, ucell ((n : Nat) : Int)),
             (.base ⟨8⟩, bcell false),
             (.base ⟨9⟩, ucell 0), (.base ⟨10⟩, ucell 0),
             (.base ⟨11⟩, hcellH n),
             (.base ⟨12⟩, ucell 0), (.base ⟨13⟩, ucell 0),
             (.base ⟨14⟩, ucell 0), (.base ⟨15⟩, ucell 0)],
    nextAddr := 16 }

/-- The in-minMax-loop state at the harness layout. -/
private def mState (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ffv : Bool) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs, methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell 0), (.base ⟨3⟩, ucell 0),
             (.base ⟨4⟩, hcellH n), (.base ⟨5⟩, arrCell n l),
             (.base ⟨6⟩, hcellH n), (.base ⟨7⟩, ucell ((n : Nat) : Int)),
             (.base ⟨8⟩, bcell false),
             (.base ⟨9⟩, ucell 0), (.base ⟨10⟩, ucell 0),
             (.base ⟨11⟩, hcellH n),
             (.base ⟨12⟩, ucell 0), (.base ⟨13⟩, ucell 0),
             (.base ⟨14⟩, ucell lov), (.base ⟨15⟩, ucell hiv),
             (.base ⟨16⟩, icell iv), (.base ⟨17⟩, bcell ffv)],
    nextAddr := 18 }

/-- The exit-test state after the dispatch of iteration `m`. -/
private abbrev mCmpState (nv sv : Int) (n : Nat) (l : List Int) (m : Nat) :
    ExecState :=
  mState nv sv n l (minSpec (l.take m)) (maxSpec (l.take m))
    ((m : Nat) : Int) false

/-- The terminal state: results delivered through the minMax frame,
`$c13`/`$c14`, and the harness result cells. -/
private def mhFinal (nv sv : Int) (n : Nat) (l : List Int) : ExecState :=
  { types := minMaxLowered.typeDefs.toList,
    functions := minMaxLowered.funcs, methods := minMaxLowered.methods,
    heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
             (.base ⟨2⟩, ucell (minSpec l)), (.base ⟨3⟩, ucell (maxSpec l)),
             (.base ⟨4⟩, hcellH n), (.base ⟨5⟩, arrCell n l),
             (.base ⟨6⟩, hcellH n), (.base ⟨7⟩, ucell ((n : Nat) : Int)),
             (.base ⟨8⟩, bcell false),
             (.base ⟨9⟩, ucell (minSpec l)), (.base ⟨10⟩, ucell (maxSpec l)),
             (.base ⟨11⟩, hcellH n),
             (.base ⟨12⟩, ucell (minSpec l)), (.base ⟨13⟩, ucell (maxSpec l)),
             (.base ⟨14⟩, ucell (minSpec l)), (.base ⟨15⟩, ucell (maxSpec l)),
             (.base ⟨16⟩, icell ((n : Nat) : Int)),
             (.base ⟨17⟩, bcell false)],
    nextAddr := 18 }

/-! ### Heap-lookup facts and step glue -/

private theorem lookup_shState (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ffv : Bool) :
    Heap.lookup (shState nv sv n l iv ffv).heap (.base ⟨5⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [shState, Heap.lookup]

private theorem lookup_σM1 (nv sv : Int) (n : Nat) (l : List Int) :
    Heap.lookup (σM1 nv sv n l).heap (.base ⟨5⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [σM1, Heap.lookup]

private theorem lookup_mState (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ffv : Bool) :
    Heap.lookup (mState nv sv n l lov hiv iv ffv).heap (.base ⟨5⟩)
      = some ⟨some (.array n (.int .uint64)),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [mState, Heap.lookup]

/-- The phase-2 store machine step, conditioned on the store fact
(reverse's `stepFn_store_step`). -/
private theorem stepFn_store_step {σ σ' : ExecState} {r : TargetRef}
    {val : GoValue} {rs : List TargetRef} {vs : List GoValue} {body : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : storeTarget σ r val = .ok σ') :
    stepFn σ (.next (.storeK (r :: rs) (val :: vs) body env k)) ch
      = .ok (.next (.storeK rs vs body env k), σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- The wide-statement apply machine step, conditioned on the op fact
(the `stmtOpK` analog of `stepFn_strict_apply`). -/
private theorem stepFn_stmtOp_apply {σ σ' : ExecState} {op : StmtOp}
    {nt : Nat} {done : List GoValue} {v : GoValue} {env : LocalEnv}
    {k : Cont} {ch : Choices}
    (h : applyStmtOp σ ch op nt (v :: done).reverse = .ok (σ', ch)) :
    stepFn σ (.retV v (.stmtOpK op nt done [] env k)) ch
      = .ok (.next k, σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- **The `make([]uint64, n)` apply at SYMBOLIC length** — the one
data-dependent step of the setup phase: the length check discharged by
`n : Nat`, the backing built by the shared `buildDefaultArrayValue_int`
(a replicate of zeros), the handle stored at the target cell. -/
private theorem applyStmtOp_makeSlice_u64 (nv sv : Int) (n : Nat)
    (ch : Choices) :
    applyStmtOp (σMS nv sv) ch (.makeSlice (.int .uint64) false) 1
      [.addr (.base ⟨4⟩), .int (n : Int) .uint64]
      = .ok (σMS' nv sv n, ch) := by
  have hbd := GoLean.Iris.buildDefaultArrayValue_int (σMS nv sv) .uint64 n
  have h1 : ¬ ((n : Int) < 0) := by omega
  have h2 : ¬ (n < n) := Nat.lt_irrefl n
  simp only [applyStmtOp, applyStmtOpCore, valueAsInt, natFromNonnegativeInt,
    Bind.bind, Except.bind, pure, Except.pure, if_neg h1, if_neg h2,
    Int.toNat_natCast, hbd]
  have hval : (GoValue.array (List.replicate n (GoValue.int 0 IntKind.uint64)).toArray)
      = .array ⟨(List.replicate n ((0 : Int))).map (fun v => .int v .uint64)⟩ := by
    simp [List.map_replicate]
  rw [hval]
  with_unfolding_all rfl

/-! ### Raw run segments (`with_unfolding_all rfl`; splits exactly at
the data-dependent points: the `makeSlice` apply, the element stores,
the value-dependent `if` deliveries, the five `indexGet` applies, the
per-pass `len(s)` apply) -/

/-- Entry A: harness-body start → the `makeSlice` apply point (`$c12`
allocated at its default). 10 steps. -/
private theorem mmh_entryA_raw (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (mhSeedI nv sv) mhc₀ ch
      = .ok (.retV (.int nv .uint64)
            (.stmtOpK (.makeSlice (.int .uint64) false) 1
              [.addr (.base ⟨4⟩)] [] hEnvMS hkMS),
          σMS nv sv, ch) := by
  with_unfolding_all rfl

/-- Entry B: after the `makeSlice` apply → the setup loop head (`s`
bound to the handle, `i := 0`, the `$forFirst` block). 42 steps. -/
private theorem mmh_entryB_raw (nv sv : Int) (n : Nat) (ch : Choices) :
    stepFnIter 42 (σMS' nv sv n) (.next hkMS) ch
      = .ok (shHeadCfg,
          shState nv sv n (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Setup first-pass dispatch: head with the flag up → the exit-test
delivery (`i < n` on the PARAMETER cell — `nv` symbolic). 25 steps. -/
private theorem sh_dispA_raw (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (shState nv sv n l iv true) shHeadCfg ch
      = .ok (.retV (.bool (decide (iv < nv))) shCmpK,
          shState nv sv n l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup later-pass dispatch: head with the flag down → `i = i + 1`
(uint64: the stored and riding values carry the machine's double
normalization), the exit test. 29 steps. -/
private theorem sh_dispB_raw (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (shState nv sv n l iv false) shHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < nv))) shCmpK,
          shState nv sv n l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Setup body: exit test true → the element-store point (`s[i]`'s
target chain resolved, `seed + i` computed — the machine's wrapping
uint64 add rides as one `normalize`). 18 steps. -/
private theorem sh_body_raw (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 18 (shState nv sv n l iv false) (.retV (.bool true) shCmpK) ch
      = .ok (.next (.storeK
            [.chain (sliceH5 n) [.int iv .uint64] [.index]]
            [.int (IntKind.normalize .uint64 (sv + iv)) .uint64]
            (.seqn #[]) shEnvB2 shStTail),
          shState nv sv n l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup store drain: element stored → back to the loop head. 5
steps. -/
private theorem sh_drain_raw (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ch : Choices) :
    stepFnIter 5 (shState nv sv n l iv false)
      (.next (.storeK [] [] (.seqn #[]) shEnvB2 shStTail)) ch
      = .ok (shHeadCfg, shState nv sv n l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup exit: test false → break unwinding, `$c13`/`$c14`
declarations, the `minMax` call's frame entry, `lo`/`hi` declarations,
the first `s[0]` operand walk → the first index-read apply point. 33
steps. -/
private theorem sh_exitC_raw (nv sv : Int) (n : Nat) (l : List Int)
    (ch : Choices) :
    stepFnIter 33 (shState nv sv n l ((n : Nat) : Int) false)
      (.retV (.bool false) shCmpK) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB mRhs1K),
          σM1 nv sv n l, ch) := by
  with_unfolding_all rfl

/-- minMax entry C: first element delivered → the second `s[0]` apply
point. 5 steps. -/
private theorem mmh_entryC_raw (nv sv : Int) (n : Nat) (l : List Int)
    (w : Int) (ch : Choices) :
    stepFnIter 5 (σM1 nv sv n l) (.retV (.int w .uint64) mRhs1K) ch
      = .ok (.retV (.int 0 .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB (mRhs2K w)),
          σM1 nv sv n l, ch) := by
  with_unfolding_all rfl

/-- minMax entry D: both reads delivered → the `lo`/`hi` stores,
`i := 1`, the `$forFirst` block → the minMax loop head. 34 steps. -/
private theorem mmh_entryD_raw (nv sv : Int) (n : Nat) (l : List Int)
    (w1 w2 : Int) (ch : Choices) :
    stepFnIter 34 (σM1 nv sv n l) (.retV (.int w2 .uint64) (mRhs2K w1)) ch
      = .ok (mHeadCfg,
          mState nv sv n l (IntKind.normalize .uint64 w1)
            (IntKind.normalize .uint64 w2) 1 true, ch) := by
  with_unfolding_all rfl

/-- minMax first-pass dispatch: head with the flag up → the `len(s)`
apply point. 25 steps. -/
private theorem mh_dispA_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 25 (mState nv sv n l lov hiv iv true) mHeadCfg ch
      = .ok (.retV (sliceH5 n) (mLenApplyK iv),
          mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- minMax later-pass dispatch: `i = i + 1` (int: double
normalization), then the `len(s)` apply point. 29 steps. -/
private theorem mh_dispB_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 29 (mState nv sv n l lov hiv iv false) mHeadCfg ch
      = .ok (.retV (sliceH5 n)
            (mLenApplyK
              (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          mState nv sv n l lov hiv
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1))) false,
          ch) := by
  with_unfolding_all rfl

/-- minMax body entry: exit test true → the `s[i]` apply point of the
first conditional. 11 steps. -/
private theorem mh_bodyA_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 11 (mState nv sv n l lov hiv iv false)
      (.retV (.bool true) mCmpIfK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB2 mLoCmpK),
          mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- minMax body: element delivered → `lo` load, the `<` compare
delivery. 3 steps. -/
private theorem mh_bodyB_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 3 (mState nv sv n l lov hiv iv false)
      (.retV (.int w .uint64) mLoCmpK) ch
      = .ok (.retV (.bool (decide (w < lov))) mLoIfK,
          mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `lo`-branch taken: → the `s[i]` apply point of the assignment's
RHS. 12 steps. -/
private theorem mh_loT_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 12 (mState nv sv n l lov hiv iv false)
      (.retV (.bool true) mLoIfK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB3 mLoStoreK),
          mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `lo`-branch store: element delivered → `lo := w` → the `s[i]` apply
point of the second conditional. 12 steps. -/
private theorem mh_loT2_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 12 (mState nv sv n l lov hiv iv false)
      (.retV (.int w .uint64) mLoStoreK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB2 mHiCmpK),
          mState nv sv n l (IntKind.normalize .uint64 w) hiv iv false,
          ch) := by
  with_unfolding_all rfl

/-- `lo`-branch skipped: → the `s[i]` apply point of the second
conditional, state untouched. 9 steps. -/
private theorem mh_loF_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 9 (mState nv sv n l lov hiv iv false)
      (.retV (.bool false) mLoIfK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB2 mHiCmpK),
          mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- Second conditional: element delivered → `hi` load, the `>` compare
delivery. 3 steps. -/
private theorem mh_hiB_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 3 (mState nv sv n l lov hiv iv false)
      (.retV (.int w .uint64) mHiCmpK) ch
      = .ok (.retV (.bool (decide (hiv < w))) mHiIfK,
          mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `hi`-branch taken: → the `s[i]` apply point of the assignment's
RHS. 12 steps. -/
private theorem mh_hiT_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 12 (mState nv sv n l lov hiv iv false)
      (.retV (.bool true) mHiIfK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB3 mHiStoreK),
          mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- `hi`-branch store: element delivered → `hi := w` → back to the loop
head. 8 steps. -/
private theorem mh_hiT2_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv w : Int) (ch : Choices) :
    stepFnIter 8 (mState nv sv n l lov hiv iv false)
      (.retV (.int w .uint64) mHiStoreK) ch
      = .ok (mHeadCfg,
          mState nv sv n l lov (IntKind.normalize .uint64 w) iv false,
          ch) := by
  with_unfolding_all rfl

/-- `hi`-branch skipped: → back to the loop head, state untouched. 5
steps. -/
private theorem mh_hiF_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 5 (mState nv sv n l lov hiv iv false)
      (.retV (.bool false) mHiIfK) ch
      = .ok (mHeadCfg, mState nv sv n l lov hiv iv false, ch) := by
  with_unfolding_all rfl

/-- Exit: test false → break unwinding, the minMax epilogue, the frame
exit into `$c13`/`$c14`, the harness epilogue, the entry barrier → the
entry terminal. 62 steps; each store re-normalizes. -/
private theorem mmh_exit_raw (nv sv : Int) (n : Nat) (l : List Int)
    (lov hiv iv : Int) (ch : Choices) :
    stepFnIter 62 (mState nv sv n l lov hiv iv false)
      (.retV (.bool false) mCmpIfK) ch
      = .ok (.next .stop,
          { types := minMaxLowered.typeDefs.toList,
            functions := minMaxLowered.funcs,
            methods := minMaxLowered.methods,
            heap := [(.base ⟨0⟩, ucell nv), (.base ⟨1⟩, ucell sv),
              (.base ⟨2⟩, ucell (IntKind.normalize .uint64
                (IntKind.normalize .uint64 (IntKind.normalize .uint64 lov)))),
              (.base ⟨3⟩, ucell (IntKind.normalize .uint64
                (IntKind.normalize .uint64 (IntKind.normalize .uint64 hiv)))),
              (.base ⟨4⟩, hcellH n), (.base ⟨5⟩, arrCell n l),
              (.base ⟨6⟩, hcellH n), (.base ⟨7⟩, ucell ((n : Nat) : Int)),
              (.base ⟨8⟩, bcell false),
              (.base ⟨9⟩, ucell (IntKind.normalize .uint64
                (IntKind.normalize .uint64 lov))),
              (.base ⟨10⟩, ucell (IntKind.normalize .uint64
                (IntKind.normalize .uint64 hiv))),
              (.base ⟨11⟩, hcellH n),
              (.base ⟨12⟩, ucell (IntKind.normalize .uint64 lov)),
              (.base ⟨13⟩, ucell (IntKind.normalize .uint64 hiv)),
              (.base ⟨14⟩, ucell lov), (.base ⟨15⟩, ucell hiv),
              (.base ⟨16⟩, icell iv), (.base ⟨17⟩, bcell false)],
            nextAddr := 18 }, ch) := by
  with_unfolding_all rfl

/-! ### The setup-loop induction -/

/-- **The setup loop**: from the exit-test delivery at counter `i` with
the invariant list (family prefix + zeros), exactly `53·(n − i)` steps
reach the final `false` delivery with the WHOLE family built. Plain
induction on the remaining count; the element store is the one
conditioned step per iteration. -/
private theorem sh_loop (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ μ i : Nat, i + μ = n → ∀ ch : Choices,
      stepFnIter (53 * μ)
        (shState (n : Int) (seed : Int) n (setupList n seed i)
          ((i : Nat) : Int) false)
        (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
          shCmpK) ch
        = .ok (.retV (.bool false) shCmpK,
            shState (n : Int) (seed : Int) n (mmFamily n seed)
              ((n : Nat) : Int) false, ch) := by
  intro μ
  induction μ with
  | zero =>
      intro i hi ch
      have heq : i = n := by omega
      subst heq
      rw [show (decide (((i : Nat) : Int) < ((i : Nat) : Int))) = false from
        decide_eq_false (by omega), setupList_full]
      rfl
  | succ μ' ih =>
      intro i hi ch
      have hilt : i < n := by omega
      rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hilt)]
      -- the body, with the wrapped sum cleaned to the family value
      have hB := sh_body_raw (n : Int) (seed : Int) n (setupList n seed i)
        ((i : Nat) : Int) ch
      rw [show IntKind.normalize .uint64 ((seed : Int) + ((i : Nat) : Int))
          = (((seed + i) % 2 ^ 64 : Nat) : Int) from by
        rw [show ((seed : Int) + ((i : Nat) : Int))
            = (((seed + i : Nat)) : Int) from by omega]
        exact unorm_nat_wrap _] at hB
      -- the element store
      have hw : (0 : Int) ≤ (((seed + i) % 2 ^ 64 : Nat) : Int)
          ∧ (((seed + i) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
        constructor
        · omega
        · exact_mod_cast Nat.mod_lt _ (by omega)
      have hst := storeTarget_slice_u64
        (σ := shState (n : Int) (seed : Int) n (setupList n seed i)
          ((i : Nat) : Int) false)
        (a := ⟨5⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
        (ik := .uint64) (l := setupList n seed i)
        (w := (((seed + i) % 2 ^ 64 : Nat) : Int))
        (lookup_shState _ _ _ _ _ _) (Nat.le_refl n) hilt
        (by rw [setupList_length (by omega)]; omega)
        (setupList_length (by omega)) (setupList_range n seed i) hw
      rw [Nat.zero_add] at hst
      have hstore : storeTarget
          (shState (n : Int) (seed : Int) n (setupList n seed i)
            ((i : Nat) : Int) false)
          (.chain (sliceH5 n) [.int ((i : Nat) : Int) .uint64] [.index])
          (.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64)
          = .ok (shState (n : Int) (seed : Int) n (setupList n seed (i + 1))
              ((i : Nat) : Int) false) := by
        rw [← setupList_set hilt]
        exact hst
      -- the drain and the next dispatch
      have hD := sh_drain_raw (n : Int) (seed : Int) n
        (setupList n seed (i + 1)) ((i : Nat) : Int) ch
      have hDB := sh_dispB_raw (n : Int) (seed : Int) n
        (setupList n seed (i + 1)) ((i : Nat) : Int) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64),
        unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64)] at hDB
      -- the IH at i + 1
      have hIH := ih (i + 1) (by omega) ch
      have hchain := stepFnIter_chain
        (stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain hB (stepFnIter_one (stepFn_store_step hstore)))
            hD)
          hDB)
        hIH
      rw [show 53 * (μ' + 1) = 18 + 1 + 5 + 29 + 53 * μ' from by omega]
      exact hchain

/-! ### The minMax loop induction (the framed layer's prefix-min/max
strong induction, at the harness layout) -/

/-- **One minMax iteration, cleaned** (the framed layer's `mm_iter`,
ported): exit test true at counter `m` → the next exit-test delivery,
prefix min/max advanced to `m + 1`. -/
private theorem mh_iter (nv sv : Int) (n : Nat) (l : List Int) (m : Nat)
    (hln : l.length = n) (hxs : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hn : n < 2 ^ 63) (hm1 : 1 ≤ m) (hm : m < n) (ch : Choices) :
    ∃ k : Nat, k ≤ 96 ∧
      stepFnIter k (mCmpState nv sv n l m) (.retV (.bool true) mCmpIfK) ch
        = .ok (.retV (.bool (decide
              (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) mCmpIfK,
            mCmpState nv sv n l (m + 1), ch) := by
  have hm' : m < l.length := by omega
  have hne : l ≠ [] := by
    intro hc
    rw [hc] at hln
    simp at hln
    omega
  have hw := hxs _ (getD_mem hm')
  have hget : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + m]?
      = some (.int (l.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ hm']
  -- Phase 1: through the first conditional, lo advanced.
  have phase1 : ∃ k₁ : Nat, k₁ ≤ 40 ∧
      stepFnIter k₁ (mCmpState nv sv n l m) (.retV (.bool true) mCmpIfK) ch
        = .ok (.retV (.int ((m : Nat) : Int) .int)
              (.strictK .indexGet [sliceH5 n] [] mEnvB2 mHiCmpK),
            mState nv sv n l (minSpec (l.take (m + 1)))
              (maxSpec (l.take m)) ((m : Nat) : Int) false, ch) := by
    have hA := mh_bodyA_raw nv sv n l (minSpec (l.take m))
      (maxSpec (l.take m)) ((m : Nat) : Int) ch
    have hidx1 : stepFn (mCmpState nv sv n l m)
        (.retV (.int ((m : Nat) : Int) .int)
          (.strictK .indexGet [sliceH5 n] [] mEnvB2 mLoCmpK)) ch
        = .ok (.retV (.int (l.getD m 0) .uint64) mLoCmpK,
            mCmpState nv sv n l m, ch) :=
      stepFn_strict_apply
        (applyStrictOp_indexGet_slice (lookup_mState _ _ _ _ _ _ _ _)
          (Nat.le_refl _) hm hget)
    have hB := mh_bodyB_raw nv sv n l (minSpec (l.take m))
      (maxSpec (l.take m)) ((m : Nat) : Int) (l.getD m 0) ch
    have h15 := stepFnIter_chain
      (stepFnIter_chain hA (stepFnIter_one hidx1)) hB
    by_cases hlt : l.getD m 0 < minSpec (l.take m)
    · rw [show (decide (l.getD m 0 < minSpec (l.take m))) = true from
        decide_eq_true hlt] at h15
      have hC := mh_loT_raw nv sv n l (minSpec (l.take m))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      have hidx2 : stepFn (mCmpState nv sv n l m)
          (.retV (.int ((m : Nat) : Int) .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB3 mLoStoreK)) ch
          = .ok (.retV (.int (l.getD m 0) .uint64) mLoStoreK,
              mCmpState nv sv n l m, ch) :=
        stepFn_strict_apply
          (applyStrictOp_indexGet_slice (lookup_mState _ _ _ _ _ _ _ _)
            (Nat.le_refl _) hm hget)
      have hD := mh_loT2_raw nv sv n l (minSpec (l.take m))
        (maxSpec (l.take m)) ((m : Nat) : Int) (l.getD m 0) ch
      rw [unorm_of_range hw.1 hw.2] at hD
      refine ⟨40, Nat.le_refl _, ?_⟩
      rw [show minSpec (l.take (m + 1)) = l.getD m 0 from by
        rw [minSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h15 hC) (stepFnIter_one hidx2)) hD
    · rw [show (decide (l.getD m 0 < minSpec (l.take m))) = false from
        decide_eq_false hlt] at h15
      have hC := mh_loF_raw nv sv n l (minSpec (l.take m))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      refine ⟨24, by omega, ?_⟩
      rw [show minSpec (l.take (m + 1)) = minSpec (l.take m) from by
        rw [minSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain h15 hC
  obtain ⟨k₁, hk₁, h1⟩ := phase1
  -- Phase 2: through the second conditional, hi advanced.
  have phase2 : ∃ k₂ : Nat, k₂ ≤ 25 ∧
      stepFnIter k₂
        (mState nv sv n l (minSpec (l.take (m + 1)))
          (maxSpec (l.take m)) ((m : Nat) : Int) false)
        (.retV (.int ((m : Nat) : Int) .int)
          (.strictK .indexGet [sliceH5 n] [] mEnvB2 mHiCmpK)) ch
        = .ok (mHeadCfg,
            mState nv sv n l (minSpec (l.take (m + 1)))
              (maxSpec (l.take (m + 1))) ((m : Nat) : Int) false, ch) := by
    have hidx3 : stepFn
        (mState nv sv n l (minSpec (l.take (m + 1)))
          (maxSpec (l.take m)) ((m : Nat) : Int) false)
        (.retV (.int ((m : Nat) : Int) .int)
          (.strictK .indexGet [sliceH5 n] [] mEnvB2 mHiCmpK)) ch
        = .ok (.retV (.int (l.getD m 0) .uint64) mHiCmpK,
            mState nv sv n l (minSpec (l.take (m + 1)))
              (maxSpec (l.take m)) ((m : Nat) : Int) false, ch) :=
      stepFn_strict_apply
        (applyStrictOp_indexGet_slice (lookup_mState _ _ _ _ _ _ _ _)
          (Nat.le_refl _) hm hget)
    have hB := mh_hiB_raw nv sv n l (minSpec (l.take (m + 1)))
      (maxSpec (l.take m)) ((m : Nat) : Int) (l.getD m 0) ch
    have h4 := stepFnIter_chain (stepFnIter_one hidx3) hB
    by_cases hgt : maxSpec (l.take m) < l.getD m 0
    · rw [show (decide (maxSpec (l.take m) < l.getD m 0)) = true from
        decide_eq_true hgt] at h4
      have hC := mh_hiT_raw nv sv n l (minSpec (l.take (m + 1)))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      have hidx4 : stepFn
          (mState nv sv n l (minSpec (l.take (m + 1)))
            (maxSpec (l.take m)) ((m : Nat) : Int) false)
          (.retV (.int ((m : Nat) : Int) .int)
            (.strictK .indexGet [sliceH5 n] [] mEnvB3 mHiStoreK)) ch
          = .ok (.retV (.int (l.getD m 0) .uint64) mHiStoreK,
              mState nv sv n l (minSpec (l.take (m + 1)))
                (maxSpec (l.take m)) ((m : Nat) : Int) false, ch) :=
        stepFn_strict_apply
          (applyStrictOp_indexGet_slice (lookup_mState _ _ _ _ _ _ _ _)
            (Nat.le_refl _) hm hget)
      have hD := mh_hiT2_raw nv sv n l (minSpec (l.take (m + 1)))
        (maxSpec (l.take m)) ((m : Nat) : Int) (l.getD m 0) ch
      rw [unorm_of_range hw.1 hw.2] at hD
      refine ⟨25, Nat.le_refl _, ?_⟩
      rw [show maxSpec (l.take (m + 1)) = l.getD m 0 from by
        rw [maxSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h4 hC) (stepFnIter_one hidx4)) hD
    · rw [show (decide (maxSpec (l.take m) < l.getD m 0)) = false from
        decide_eq_false hgt] at h4
      have hC := mh_hiF_raw nv sv n l (minSpec (l.take (m + 1)))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      refine ⟨9, by omega, ?_⟩
      rw [show maxSpec (l.take (m + 1)) = maxSpec (l.take m) from by
        rw [maxSpec_take_succ hm1 hm']; omega]
      exact stepFnIter_chain h4 hC
  obtain ⟨k₂, hk₂, h2⟩ := phase2
  -- Phase 3: the later-pass dispatch, the exit test.
  have hDisp := mh_dispB_raw nv sv n l (minSpec (l.take (m + 1)))
    (maxSpec (l.take (m + 1))) ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hDisp
  have hlenap : applyStrictOp
      (mState nv sv n l (minSpec (l.take (m + 1)))
        (maxSpec (l.take (m + 1))) ((m + 1 : Nat) : Int) false)
      (.lengthOf (some (.slice (.int .uint64)))) [sliceH5 n]
      = .ok (.int ((n : Nat) : Int) .int,
          mState nv sv n l (minSpec (l.take (m + 1)))
            (maxSpec (l.take (m + 1))) ((m + 1 : Nat) : Int) false) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have h3a := stepFnIter_chain hDisp
    (stepFnIter_one (stepFn_strict_apply (done := []) hlenap))
  have h3 := stepFnIter_chain h3a
    (stepFnIter_one (stepFn_strict_apply
      (done := [.int ((m + 1 : Nat) : Int) .int]) applyStrictOp_lessCmp_int))
  exact ⟨k₁ + (k₂ + 31), by omega,
    stepFnIter_chain h1 (stepFnIter_chain h2 h3)⟩

/-- **The minMax loop** (the framed layer's `mm_loop`, ported): from
the exit-test delivery of iteration `m`, the run reaches the ENTRY
terminal within `96·μ + 62` steps, at the pinned terminal state. -/
private theorem mh_loop (nv sv : Int) (n : Nat) (l : List Int)
    (hln : l.length = n) (hxs : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hn : n < 2 ^ 63) :
    ∀ μ m, 1 ≤ m → m ≤ n → μ = n - m → ∀ ch : Choices,
      ∃ k : Nat, k ≤ 96 * μ + 62 ∧
        stepFnIter k (mCmpState nv sv n l m)
          (.retV (.bool (decide
            (((m : Nat) : Int) < ((n : Nat) : Int)))) mCmpIfK) ch
          = .ok (.next .stop, mhFinal nv sv n l, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm1 hmn hμ ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · -- iterate
      rw [show (decide (((m : Nat) : Int) < ((n : Nat) : Int)))
          = true from decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨k₁, hk₁, hiter⟩ := mh_iter nv sv n l m hln hxs hn hm1 hlt ch
      obtain ⟨k₂, hk₂, hrest⟩ := ih (n - (m + 1)) (by omega) (m + 1)
        (by omega) (by omega) rfl ch
      exact ⟨k₁ + k₂, by omega, stepFnIter_chain hiter hrest⟩
    · -- exit: m = n
      have hmeq : m = n := by omega
      subst hmeq
      have hne : l ≠ [] := by
        intro hc
        rw [hc] at hln
        simp at hln
        omega
      rw [show (decide (((m : Nat) : Int) < ((m : Nat) : Int)))
          = false from decide_eq_false (by omega)]
      have hlo := minTake_range (m := m) hxs hm1 hne
      have hhi := maxTake_range (m := m) hxs hm1 hne
      have hX := mmh_exit_raw nv sv m l (minSpec (l.take m))
        (maxSpec (l.take m)) ((m : Nat) : Int) ch
      rw [unorm_of_range hlo.1 hlo.2, unorm_of_range hlo.1 hlo.2,
        unorm_of_range hlo.1 hlo.2,
        unorm_of_range hhi.1 hhi.2, unorm_of_range hhi.1 hhi.2,
        unorm_of_range hhi.1 hhi.2] at hX
      have htake : l.take m = l := by rw [← hln]; exact List.take_length
      rw [htake] at hX
      refine ⟨62, by omega, ?_⟩
      show stepFnIter 62
          (mState nv sv m l (minSpec (l.take m)) (maxSpec (l.take m))
            ((m : Nat) : Int) false)
          (.retV (.bool false) mCmpIfK) ch
        = .ok (.next .stop, mhFinal nv sv m l, ch)
      rw [htake]
      exact hX

/-! ### The end-to-end canonical run and the entry equation -/

/-- **The harness run, end to end**: from the entry seed the run
reaches the entry terminal within `145 + 149·n` steps, with the
family's min/max in the harness result cells. -/
private theorem mmh_runs (n seed : Nat) (h1 : 1 ≤ n) (hn : n < 2 ^ 63)
    (ch : Choices) :
    ∃ k : Nat, k ≤ 145 + 149 * n ∧
      stepFnIter k (mhSeedI (n : Int) (seed : Int)) mhc₀ ch
        = .ok (.next .stop,
            mhFinal (n : Int) (seed : Int) n (mmFamily n seed), ch) := by
  have hfam_len := mmFamily_length n seed
  have hfam_rng := mmFamily_range n seed
  have hfam_ne : mmFamily n seed ≠ [] := mmFamily_ne_nil h1
  have h0lt : 0 < (mmFamily n seed).length := by omega
  have hv0 := hfam_rng _ (getD_mem h0lt)
  -- entry A + the makeSlice apply + entry B
  have hA := mmh_entryA_raw (n : Int) (seed : Int) ch
  have hMS : stepFn (σMS (n : Int) (seed : Int))
      (.retV (.int (n : Int) .uint64)
        (.stmtOpK (.makeSlice (.int .uint64) false) 1
          [.addr (.base ⟨4⟩)] [] hEnvMS hkMS)) ch
      = .ok (.next hkMS, σMS' (n : Int) (seed : Int) n, ch) :=
    stepFn_stmtOp_apply (done := [.addr (.base ⟨4⟩)])
      (applyStmtOp_makeSlice_u64 (n : Int) (seed : Int) n ch)
  have hB := mmh_entryB_raw (n : Int) (seed : Int) n ch
  have h53 := stepFnIter_chain (stepFnIter_chain hA (stepFnIter_one hMS)) hB
  -- the first setup dispatch and the setup loop
  have hDA := sh_dispA_raw (n : Int) (seed : Int) n (List.replicate n 0) 0 ch
  have h78 := stepFnIter_chain h53 hDA
  have hloop := sh_loop n seed hn n 0 (by omega) ch
  rw [Int.natCast_zero, setupList_zero] at hloop
  have hsetup := stepFnIter_chain h78 hloop
  -- the setup exit into the minMax frame, the two s[0] reads
  have hEC := sh_exitC_raw (n : Int) (seed : Int) n (mmFamily n seed) ch
  have hget0 : (⟨(mmFamily n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + 0]?
      = some (.int ((mmFamily n seed).getD 0 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ h0lt]
  have hidx1 : stepFn (σM1 (n : Int) (seed : Int) n (mmFamily n seed))
      (.retV (.int 0 .int)
        (.strictK .indexGet [sliceH5 n] [] mEnvB mRhs1K)) ch
      = .ok (.retV (.int ((mmFamily n seed).getD 0 0) .uint64) mRhs1K,
          σM1 (n : Int) (seed : Int) n (mmFamily n seed), ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice (off := 0) (len := n) (cap := n) (i := 0)
        (lookup_σM1 _ _ _ _) (Nat.le_refl _) (by omega) hget0)
  have hC := mmh_entryC_raw (n : Int) (seed : Int) n (mmFamily n seed)
    ((mmFamily n seed).getD 0 0) ch
  have hidx2 : stepFn (σM1 (n : Int) (seed : Int) n (mmFamily n seed))
      (.retV (.int 0 .int)
        (.strictK .indexGet [sliceH5 n] [] mEnvB
          (mRhs2K ((mmFamily n seed).getD 0 0)))) ch
      = .ok (.retV (.int ((mmFamily n seed).getD 0 0) .uint64)
            (mRhs2K ((mmFamily n seed).getD 0 0)),
          σM1 (n : Int) (seed : Int) n (mmFamily n seed), ch) :=
    stepFn_strict_apply
      (applyStrictOp_indexGet_slice (off := 0) (len := n) (cap := n) (i := 0)
        (lookup_σM1 _ _ _ _) (Nat.le_refl _) (by omega) hget0)
  have hD := mmh_entryD_raw (n : Int) (seed : Int) n (mmFamily n seed)
    ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) ch
  rw [unorm_of_range hv0.1 hv0.2] at hD
  have hentry := stepFnIter_chain
    (stepFnIter_chain
      (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain hsetup hEC)
          (stepFnIter_one hidx1))
        hC)
      (stepFnIter_one hidx2))
    hD
  -- the first minMax dispatch and the exit test at m = 1
  have hMDA := mh_dispA_raw (n : Int) (seed : Int) n (mmFamily n seed)
    ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1 ch
  have hlenap : applyStrictOp
      (mState (n : Int) (seed : Int) n (mmFamily n seed)
        ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1 false)
      (.lengthOf (some (.slice (.int .uint64)))) [sliceH5 n]
      = .ok (.int ((n : Nat) : Int) .int,
          mState (n : Int) (seed : Int) n (mmFamily n seed)
            ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1
            false) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have hpre := stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hentry hMDA)
      (stepFnIter_one (stepFn_strict_apply (done := []) hlenap)))
    (stepFnIter_one (stepFn_strict_apply
      (done := [.int (1 : Int) .int]) applyStrictOp_lessCmp_int))
  -- the minMax loop from m = 1
  obtain ⟨k, hk, hloop2⟩ := mh_loop (n : Int) (seed : Int) n
    (mmFamily n seed) hfam_len hfam_rng hn (n - 1) 1 (Nat.le_refl 1)
    (by omega) rfl ch
  rw [Int.natCast_one] at hloop2
  rw [show mCmpState (n : Int) (seed : Int) n (mmFamily n seed) 1
      = mState (n : Int) (seed : Int) n (mmFamily n seed)
          ((mmFamily n seed).getD 0 0) ((mmFamily n seed).getD 0 0) 1
          false from by
    show mState (n : Int) (seed : Int) n (mmFamily n seed)
        (minSpec ((mmFamily n seed).take 1))
        (maxSpec ((mmFamily n seed).take 1)) ((1 : Nat) : Int) false = _
    rw [minSpec_take_one hfam_ne, maxSpec_take_one hfam_ne,
      Int.natCast_one]] at hloop2
  exact ⟨10 + 1 + 42 + 25 + 53 * n + 33 + 1 + 5 + 1 + 34 + 25 + 1 + 1 + k,
    by omega, stepFnIter_chain hpre hloop2⟩

/-- **The entry equation**: `runFunctionWithContextM` on the harness at
symbolic arguments IS `runConfig` from the prelude-built seed plus the
two-location readback — the prelude is fuel-independent and
definitional at the concrete shapes; the parameters land
once-normalized. -/
private theorem mmh_entry_eq (n seed : Nat) (fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
        minMaxLowered.funcs mmHarnessFunc
        #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
        minMaxLowered.methods ch
      = (do
          let (sF, _) ← runConfig fuel
            (mhSeedI (IntKind.normalize .uint64 (n : Int))
              (IntKind.normalize .uint64 (seed : Int)))
            mhc₀ ch
          return { values := (← loadMany sF [.base ⟨2⟩, .base ⟨3⟩]).toArray }) := by
  with_unfolding_all rfl

/-! ### The user-facing headline -/

/-- **THE HEADLINE** (harness ruling 2026-08-13, design note §11): *for
every `1 ≤ n < 2^63` and every `seed < 2^64`,
`minmax_harness(n, seed)` — the fixed three-phase Go harness whose
setup loop builds the input family `s[i] = (seed + i) mod 2^64` —
completes normally through the machine's native function entry, past
one fuel bound, at every nondeterminism-choice stream, and returns
exactly the pair `(minSpec, maxSpec)` of the family.*

The statement observes termination + the returned values only: no heap
readback, no seed/cell/frame vocabulary (the implicit framing property
is inherent in the empty-heap entry). INPUT-FAMILY HONESTY (module
docstring §"harness restatement"): the `(n, seed)` quantification is
the `mmFamily` FAMILY — deliberately wrapping at `2^64`, so min/max are
genuinely data-dependent when `seed + n` crosses the boundary — and is
honestly weaker than the ∀xs memory-quantified form kept beneath as
`minmax_framed`. `h1` is Go's own empty-slice panic boundary; `hn` is
Go's `int` domain for `len`; `hseed` is the argument's type domain. -/
theorem minmax_ok (n seed : Nat) (h1 : 1 ≤ n) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
          minMaxLowered.funcs mmHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          minMaxLowered.methods ch
        = .ok { values := #[.int (minSpec (mmFamily n seed)) .uint64,
                            .int (maxSpec (mmFamily n seed)) .uint64] } := by
  refine ⟨145 + 149 * n, fun fuel hfuel ch => ?_⟩
  rw [mmh_entry_eq n seed fuel ch,
    unorm_nat_of_lt (by omega : n < 2 ^ 64), unorm_nat_of_lt hseed]
  obtain ⟨k, hk, hrun⟩ := mmh_runs n seed h1 hn ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, runConfig_next_stop]
  rfl

/-- **The D1 run-conditioned twin of the harness headline**: ANY
successful completion of the harness entry, at any fuel and any choice
stream, returns exactly the family's `(minSpec, maxSpec)` pair —
derived from `minmax_ok` via the shared `harness_readout_of_total`
bridge (the `.ok`-equation headline already determines every
successful run; nothing is re-proven). -/
theorem minmax_readout (n seed : Nat) (h1 : 1 ≤ n) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
          minMaxLowered.funcs mmHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          minMaxLowered.methods ch
        = .ok r →
      r = { values := #[.int (minSpec (mmFamily n seed)) .uint64,
                        .int (maxSpec (mmFamily n seed)) .uint64] } :=
  GoLean.Surface.harness_readout_of_total (minmax_ok n seed h1 hn hseed)

end GoLean.Examples.MinMax
