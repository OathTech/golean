import GoLeanProofs.Examples.FibProgram
import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Loop
import GoLeanProofs.Laws.Init

/-!
# Verified example: iterative Fibonacci (verified-examples arc slice 1, 2026-08-12)

The exemplar of the arc's headline form (design note:
`docs/2026-08-12_example-spec-form.md`; charter:
`docs/2026-08-12_verified-examples-arc-charter.md`). The Go program is
the canonical corpus source `Corpus/coverage/exec/examples/fib/main.go`
(differentially green against `go run`, incl. the n=94 mod-2^64 wrap
row); `fibLowered` is its pinned frontend lowering.

The two user-facing statements:

* `fib_ok` — the PROPOSED HEADLINE: for every `n ≤ 93` (the largest
  argument whose Fibonacci number fits in uint64), the program
  completes normally — no panic, no stuck state, no error, at every
  sufficient fuel and every nondeterminism-choice stream — and returns
  exactly `fibSpec n`.
* `fib_wraps` — the FULL-DOMAIN companion: for every `n < 2^64` (every
  value of the Go argument type), every normal completion returns
  `fibSpec n % 2^64` — machine-integer honesty (FD-E3): what Go's
  uint64 arithmetic actually computes past the overflow boundary.

Scope honesty (the charter's two-questions separation): these theorems
are USABILITY evidence — the reasoning layer carrying a natural spec
through a real program — never machine-hardening evidence; the machine
itself is validated by the differential corpus and audited separately.

Foundation debt, recorded (see the design note §4): the termination
half of `fib_ok` is kernel-enumerated per seed (`n ≤ 93` is 94 checker
runs), because symbolic (∀-input) termination machinery does not exist
yet — which is also exactly why `fib_wraps` cannot be upgraded to a
full-domain TOTAL statement. Consumer: a future
termination-measure/loop-variant arc; the width arc's re-proof
inherits the same bound.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Iris

namespace GoLean.Examples.Fib

set_option maxRecDepth 1000000
-- Uniform simp sets across law variants (the golden-walk convention).
set_option linter.unusedSimpArgs false

/-! ## The mathematical reference -/

/-- **The specification function**: the Fibonacci sequence, defined the
way a mathematician would write it. This is the entire mathematical
content of the example's claim — the theorems below say the Go program
computes THIS function. -/
def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)

/-- Iterative pair form — proof-internal (a linear-time evaluator for
`fibSpec`, so facts like `fibSpec 93 < 2^64` are one cheap `decide`
instead of an exponential unfolding). Not part of any statement. -/
private def fibIter (n : Nat) : Nat × Nat :=
  n.rec (0, 1) (fun _ p => (p.2, p.1 + p.2))

private theorem fibIter_eq : ∀ n, fibIter n = (fibSpec n, fibSpec (n + 1))
  | 0 => rfl
  | n + 1 => by
    have ih := fibIter_eq n
    simp only [fibIter] at ih ⊢
    rw [ih]
    simp [fibSpec]

private theorem fibSpec_le_succ : ∀ n, fibSpec n ≤ fibSpec (n + 1)
  | 0 => by simp [fibSpec]
  | n + 1 => by
    show fibSpec (n + 1) ≤ fibSpec n + fibSpec (n + 1)
    omega

private theorem fibSpec_mono {m n : Nat} (h : m ≤ n) : fibSpec m ≤ fibSpec n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (fibSpec_le_succ _)

/-- `fibSpec 93` is the last Fibonacci number below `2^64` (the
overflow boundary the headline's domain condition encodes). -/
private theorem fibSpec_lt_of_le_93 {n : Nat} (h : n ≤ 93) :
    fibSpec n < 2 ^ 64 := by
  have h93 : fibSpec 93 < 2 ^ 64 := by
    have := fibIter_eq 93
    have hv : (fibIter 93).1 < 2 ^ 64 := by decide
    rw [this] at hv
    exact hv
  exact Nat.lt_of_le_of_lt (fibSpec_mono h) h93

/-! ## uint64 arithmetic (machine-integer honesty, FD-E3) -/

/-- The value the machine's uint64 cells carry for `fibSpec m`:
wrapped at the 64-bit boundary, as Go's arithmetic wraps it. -/
private def fibv (m : Nat) : Int := (fibSpec m % 2 ^ 64 : Nat)

private theorem unorm_nat (x : Nat) :
    IntKind.normalize .uint64 (x : Int) = ((x % 2 ^ 64 : Nat) : Int) := by
  simp [IntKind.normalize, IntKind.bits?, IntKind.signed]

private theorem unorm_nat_of_lt {x : Nat} (h : x < 2 ^ 64) :
    IntKind.normalize .uint64 (x : Int) = (x : Int) := by
  rw [unorm_nat, Nat.mod_eq_of_lt h]

private theorem unorm_fibv (m : Nat) :
    IntKind.normalize .uint64 (fibv m) = fibv m := by
  have h : fibSpec m % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  simpa [fibv] using unorm_nat_of_lt h

/-- The loop's arithmetic step, wrapped: uint64 addition of two wrapped
Fibonacci numbers is the next wrapped Fibonacci number. -/
private theorem unorm_fibv_add (m : Nat) :
    IntKind.normalize .uint64 (fibv m + fibv (m + 1)) = fibv (m + 2) := by
  have hcast : fibv m + fibv (m + 1)
      = ((fibSpec m % 2 ^ 64 + fibSpec (m + 1) % 2 ^ 64 : Nat) : Int) := by
    simp [fibv]
  rw [hcast, unorm_nat]
  have : (fibSpec m % 2 ^ 64 + fibSpec (m + 1) % 2 ^ 64) % 2 ^ 64
      = fibSpec (m + 2) % 2 ^ 64 := by
    show _ = (fibSpec m + fibSpec (m + 1)) % 2 ^ 64
    omega
  rw [this]
  rfl

/-! ## The program-side statement vocabulary -/

/-- The user-iteration block of the desugared loop: `a, b = b, a+b`. -/
abbrev fibIterBlock : Stmt :=
  .block
    #[]
    #[.seqn
        #[.assignMany
            #[.var "a", .var "b"]
            #[.var "b", .add (.var "a") (.var "b")]]]

/-- The frontend's `for`-desugar body: the `$forFirst` dispatch (skip
the post statement on the first pass; here the post is `i++`), the exit
test ending in `break`, the user block. -/
abbrev fibWhileBody : Stmt :=
  .block
    #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[])
        .breakStmt,
      fibIterBlock]

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl` — a lowering drift breaks it
loudly, after ci's staleness guard has already caught the term drift). -/
def fibFunc : Func :=
  { id := { key := "fib" },
    args := #[{ id := "n", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "a", typ := .int .uint64 },
            .assign (.var "a") (.intLit 0 .uint64),
            .initialization { id := "b", typ := .int .uint64 },
            .assign (.var "b") (.intLit 1 .uint64)],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) fibWhileBody]],
        .seqn
          #[.assign (.var "$res0") (.var "a"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? fibLowered.funcs ⟨"fib"⟩ = some fibFunc := rfl

/-- The harness cell the differential runner also reads: the caller's
target for the call's result. -/
def fibEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- The seeded initial state: the pinned program, one zeroed uint64
result cell. -/
def fibSeed : ExecState :=
  { types := fibLowered.typeDefs.toList, functions := fibLowered.funcs,
    methods := fibLowered.methods,
    heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)],
    nextAddr := 1 }

/-- The driver: `$callres = fib(n)` — the input enters as the call's
literal argument, which is where the ∀-quantifier binds. -/
def fibCall (n : Nat) : Stmt :=
  .call #[.var "$callres"] ⟨"fib"⟩ #[.intLit (n : Int) .uint64]

/-- The result cell's precondition/postcondition shapes. -/
def fibCell0 : HProp := .pointsTo 0 ⟨some (.int .uint64), .int 0 .uint64⟩
def fibCellV (v : Int) : HProp := .pointsTo 0 ⟨some (.int .uint64), .int v .uint64⟩

/-! ## Machine well-formedness of the seeded configuration, ∀-input

The golden pins discharge this per seed by `decide +kernel`; the fib
seed varies with `n` only through the literal inside the driver
statement, whose `locSup` is `0` regardless of `n`, so one symbolic
proof covers the whole family. -/

private theorem fibSeedWf (n : Nat) :
    MachineWf
      { functions := fibLowered.funcs,
        heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)],
        nextAddr := 1 }
      (.exec (fibCall n) fibEnv .stop) := by
  refine ⟨by decide, ?_, rfl⟩
  simp [ConfigWf, Config.locSup, Stmt.locSup, Expr.locSup, fibCall, fibEnv,
    LocalEnv.locSup, Cont.locSup, Assignee.locSup, Loc.locSup, Scope.locSup,
    assigneeListSup, exprListSup, Loc.rootBase]

/-! ## The WP walk -/

/-- A uint64 heap cell. -/
private abbrev u64cell (v : Int) : HeapCell := ⟨some (.int .uint64), .int v .uint64⟩
/-- A bool heap cell. -/
private abbrev boolcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩

/-- The standard between-laws modality dance of the hand walks
(`fupd`/later/credit), the credit dropped. Local shorthand only. -/
local macro "idance" : tactic =>
  `(tactic| (iapply fupd_intro; inext; iapply fupd_intro; iintro -))

section Walk
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The loop invariant** (at the desugared loop's head, i.e. before
the `$forFirst` dispatch): `m` user-iterations are complete, so the
pair cells hold the wrapped `fibSpec m`/`fibSpec (m+1)`, the counter
lags one behind except before the first iteration (the frontend's
`$forFirst` desugar increments at the head of the NEXT iteration), and
`m` never passed `n`. The condition value `d` is pinned `true` — the
desugared condition is the literal `true`; the loop exits only by
`break`. -/
private abbrev fibInv (n : Nat) (ffa ia aa ba na : Addr) : Bool → IProp GF :=
  fun d => iprop(∃ m : Nat, ⌜d = true ∧ m ≤ n⌝
    ∗ ffa.id ↦ boolcell (m == 0)
    ∗ ia.id ↦ u64cell ((m - 1 : Nat) : Int)
    ∗ aa.id ↦ u64cell (fibv m)
    ∗ ba.id ↦ u64cell (fibv (m + 1))
    ∗ na.id ↦ u64cell (n : Int))

/-- **The break postcondition**: at the `break` (the test `i < n` just
failed with `i = m = n`), the accumulator holds the wrapped
`fibSpec n`. Everything else is dropped (affine). -/
private abbrev fibQ (n : Nat) (aa : Addr) : IProp GF :=
  iprop(aa.id ↦ u64cell (fibv n))

/-- **One iteration's tail** — from the point both `$forFirst` branches
converge (dispatch done: the flag is `false`, the counter holds `m`):
run the exit test; on `m < n` run `a, b = b, a+b` and re-establish the
invariant at `m + 1`; on `m = n` break out establishing `fibQ`. The
two continuations arrive as the additive pair `wp_while_inv_break`
hands the body. -/
private theorem wp_fib_loop_tail {n m : Nat} (hn : n < 2 ^ 64) (hmn : m ≤ n)
    {ffa ia aa ba na : Addr} {env4 : LocalEnv} {kW : Cont}
    (hia : LocalEnv.lookup env4 "i" = some (.base ia))
    (hna : LocalEnv.lookup env4 "n" = some (.base na))
    (haa : LocalEnv.lookup env4 "a" = some (.base aa))
    (hba : LocalEnv.lookup env4 "b" = some (.base ba)) :
    ffa.id ↦ boolcell false
      ∗ ia.id ↦ u64cell (m : Int)
      ∗ aa.id ↦ u64cell (fibv m)
      ∗ ba.id ↦ u64cell (fibv (m + 1))
      ∗ na.id ↦ u64cell (n : Int)
      ∗ (((∃ d, fibInv n ffa ia aa ba na d) -∗
            WP (Config.next (.loop (.boolLit true) fibWhileBody env4 kW))
              @ s ; E {{ Φ }})
         ∧ (fibQ n aa -∗
            WP (Config.breaking (.loop (.boolLit true) fibWhileBody env4 kW))
              @ s ; E {{ Φ }}))
      ⊢ WP (Config.next (.seq
            [.seqn #[],
             .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[])
               .breakStmt,
             fibIterBlock]
            env4.pushScope
            (.loop (.boolLit true) fibWhileBody env4 kW)))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hff, Hi, Ha, Hb, Hn, Hks⟩
  iapply wp_seq_next
  idance
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.nil_append]
  idance
  iapply wp_seq_next
  idance
  -- the exit test `if i < n {} else { break }`
  iapply wp_if_start
  idance
  iapply (wp_eval_strict (op := .lessCmp) (e₁ := .var "i")
    (rest := [.var "n"]) rfl)
  idance
  iapply (wp_eval_var (a := ia) (cell := u64cell (m : Int)) (hres := by
    simp [LocalEnv.lookup, LocalEnv.pushScope, Scope.lookup, hia]))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  iapply wp_strict_shift
  idance
  iapply (wp_eval_var (a := na) (cell := u64cell (n : Int)) (hres := by
    simp [LocalEnv.lookup, LocalEnv.pushScope, Scope.lookup, hna]))
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply (wp_strict_apply_pure
    (out := .bool (decide ((m : Int) < (n : Int)))) (happly := by
      intro σ
      simp [applyStrictOp, valueLess, Bind.bind, Except.bind]))
  idance
  rcases Nat.lt_or_ge m n with hlt | hge
  · -- CONTINUE: m < n — run the body, re-enter at m + 1
    rw [show decide ((m : Int) < (n : Int)) = true from
      decide_eq_true (Int.ofNat_lt.mpr hlt)]
    iapply wp_if_bool
    idance
    rw [if_pos rfl]
    iapply wp_seqn
    simp only [List.toList_toArray, seqCont_splice, List.nil_append]
    idance
    iapply wp_seq_next
    idance
    -- the iteration block `{ a, b = b, a+b }`
    iapply wp_block_nil
    idance
    iapply wp_seq_next
    idance
    iapply wp_seqn
    simp only [List.toList_toArray, seqCont_splice, List.cons_append,
      List.nil_append]
    idance
    iapply wp_seq_next
    idance
    -- `a, b = b, a+b`: the multi-assign spine
    iapply (wp_assign_many_start (sh := .chain []) (e := .ref "a")
      (ops := []) (rest := [(.chain [], [.ref "b"])]) rfl rfl)
    idance
    iapply (wp_eval_ref (loc := .base aa) (hres := by
      simp [LocalEnv.lookup, LocalEnv.pushScope, Scope.lookup, haa]))
    idance
    iapply (wp_tgtop_next (r := .chain (.addr (.base aa)) [] []) rfl)
    idance
    iapply (wp_eval_ref (loc := .base ba) (hres := by
      simp [LocalEnv.lookup, LocalEnv.pushScope, Scope.lookup, hba]))
    idance
    iapply (wp_tgtop_rhs (r := .chain (.addr (.base ba)) [] []) rfl)
    idance
    iapply (wp_eval_var (a := ba) (cell := u64cell (fibv (m + 1)))
      (hres := by
        simp [LocalEnv.lookup, LocalEnv.pushScope, Scope.lookup, hba]))
    isplitl [Hb]
    · iexact Hb
    iintro Hb
    iapply wp_rhs_shift
    idance
    iapply (wp_eval_strict (op := .add) (e₁ := .var "a")
      (rest := [.var "b"]) rfl)
    idance
    iapply (wp_eval_var (a := aa) (cell := u64cell (fibv m)) (hres := by
      simp [LocalEnv.lookup, LocalEnv.pushScope, Scope.lookup, haa]))
    isplitl [Ha]
    · iexact Ha
    iintro Ha
    iapply wp_strict_shift
    idance
    iapply (wp_eval_var (a := ba) (cell := u64cell (fibv (m + 1)))
      (hres := by
        simp [LocalEnv.lookup, LocalEnv.pushScope, Scope.lookup, hba]))
    isplitl [Hb]
    · iexact Hb
    iintro Hb
    iapply (wp_strict_apply_pure (out := .int (fibv (m + 2)) .uint64)
      (happly := by
        intro σ
        have hcomp : IntKind.compatibleResult .uint64 .uint64
            = some .uint64 := rfl
        simp [applyStrictOp, intBinaryResult, valueAsIntValue, hcomp,
          unorm_fibv_add, Bind.bind, Except.bind]))
    idance
    iapply wp_rhs_stores_vals
    idance
    simp only [List.nil_append, List.reverse_cons, List.reverse_nil,
      List.singleton_append, List.cons_append]
    iapply (wp_assign_store (a := aa) (oldcell := u64cell (fibv m))
      (newcell := u64cell (fibv (m + 1)))
      (hstore := fun σ₁ _ht hlook => by
        have h := storeLoc_int_cell (kind := .uint64) hlook (fibv (m + 1))
        rwa [unorm_fibv] at h))
    isplitl [Ha]
    · iexact Ha
    iintro Ha
    iapply (wp_assign_store (a := ba) (oldcell := u64cell (fibv (m + 1)))
      (newcell := u64cell (fibv (m + 2)))
      (hstore := fun σ₁ _ht hlook => by
        have h := storeLoc_int_cell (kind := .uint64) hlook (fibv (m + 2))
        rwa [unorm_fibv] at h))
    isplitl [Hb]
    · iexact Hb
    iintro Hb
    iapply wp_stores_done_nil
    iapply wp_seq_done
    idance
    iapply wp_seq_done
    idance
    -- re-enter: the invariant at m + 1
    icases Hks with ⟨Hre, -⟩
    iapply Hre
    iexists true
    iexists (m + 1)
    isplitl []
    · ipureintro
      exact ⟨rfl, by omega⟩
    rw [show (((m + 1 : Nat) == 0) : Bool) = false from by simp,
      show (m + 1 - 1 : Nat) = m from by omega]
    isplitl [Hff]
    · iexact Hff
    isplitl [Hi]
    · iexact Hi
    isplitl [Ha]
    · iexact Ha
    isplitl [Hb]
    · iexact Hb
    · iexact Hn
  · -- BREAK: m = n — exit the loop with the accumulator
    have hmeq : m = n := Nat.le_antisymm hmn hge
    subst hmeq
    rw [show decide ((m : Int) < (m : Int)) = false from
      decide_eq_false (by omega)]
    iapply wp_if_bool
    idance
    rw [if_neg Bool.false_ne_true]
    iapply wp_break
    idance
    iapply wp_breaking_seq
    idance
    icases Hks with ⟨-, Hbrk⟩
    iapply Hbrk
    iexact Ha

/-- **The function-body walk**: from the frame environment (`n` and the
pinned `$res0` result cell), through the declarations, the desugared
loop (via `wp_while_inv_break` at the Fibonacci pair invariant), the
result assignment and the `return` — delivering the wrapped
`fibSpec n` at the returning continuation. -/
private theorem wp_fib_body {n : Nat} (hn : n < 2 ^ 64) {na ra : Addr}
    {k : Cont} :
    na.id ↦ u64cell (n : Int)
      ∗ ra.id ↦ u64cell 0
      ∗ (ra.id ↦ u64cell (fibv n) -∗
          WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec fibFunc.body
            [[("$res0", Loc.base ra), ("n", Loc.base na)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hres, Hcont⟩
  simp only [fibFunc]
  iapply wp_block_nil
  idance
  iapply wp_seq_next
  idance
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  idance
  iapply wp_seq_next
  idance
  -- var a uint64
  iapply wp_init_int
  iintro %aa Ha
  iapply wp_seq_next
  idance
  -- a = 0
  iapply (wp_assign_lit (a := aa) (n := 0) (kind := .uint64)
    (w := .int 0 .uint64)
    (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup]))
  isplitl [Ha]
  · iexact Ha
  iintro Ha
  rw [show IntKind.normalize .uint64 0 = 0 from by decide] at *
  iapply wp_seq_next
  idance
  -- var b uint64
  iapply wp_init_int
  iintro %ba Hb
  iapply wp_seq_next
  idance
  -- b = 1
  iapply (wp_assign_lit (a := ba) (n := 1) (kind := .uint64)
    (w := .int 0 .uint64)
    (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup]))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  rw [show IntKind.normalize .uint64 1 = 1 from by decide] at *
  iapply wp_seq_next
  idance
  -- the middle block: counter + desugared loop
  iapply wp_block_nil
  idance
  iapply wp_seq_next
  idance
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  idance
  iapply wp_seq_next
  idance
  -- var i uint64
  iapply wp_init_int
  iintro %ia Hi
  iapply wp_seq_next
  idance
  -- i = 0
  iapply (wp_assign_lit (a := ia) (n := 0) (kind := .uint64)
    (w := .int 0 .uint64)
    (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup]))
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  rw [show IntKind.normalize .uint64 0 = 0 from by decide] at *
  iapply wp_seq_next
  idance
  -- the $forFirst block
  iapply wp_block_nil
  idance
  iapply wp_seq_next
  idance
  -- var $forFirst bool
  iapply wp_init_bool
  iintro %ffa Hff
  iapply wp_seq_next
  idance
  -- $forFirst = true (the bool-assign spine)
  iapply (wp_assign_start (e := .ref "$forFirst") (sh := .chain [])
    (ops := []) rfl)
  idance
  iapply (wp_eval_ref (loc := .base ffa) (hres := by
    simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
      Scope.lookup]))
  idance
  iapply (wp_tgtop_rhs (r := .chain (.addr (.base ffa)) [] []) rfl)
  idance
  iapply wp_eval_boolLit
  idance
  iapply wp_rhs_stores_vals
  idance
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply (wp_assign_store (a := ffa) (oldcell := boolcell false)
    (newcell := boolcell true)
    (hstore := fun σ₁ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  isplitl [Hff]
  · iexact Hff
  iintro Hff
  iapply wp_stores_done_nil
  iapply wp_seq_next
  idance
  -- THE LOOP
  iapply (wp_while_inv_break
    (I := fibInv n ffa ia aa ba na)
    (Q := fibQ n aa)
    (Hcond := by
      intro d
      iintro ⟨HI, Hk⟩
      icases HI with ⟨%m, %hp, Hff, Hi, Ha, Hb, Hn⟩
      obtain ⟨rfl, hmn⟩ := hp
      iapply wp_eval_boolLit
      idance
      iapply Hk
      iexists m
      isplitl []
      · ipureintro
        exact ⟨rfl, hmn⟩
      isplitl [Hff]
      · iexact Hff
      isplitl [Hi]
      · iexact Hi
      isplitl [Ha]
      · iexact Ha
      isplitl [Hb]
      · iexact Hb
      · iexact Hn)
    (Hbody := by
      iintro ⟨HI, Hks⟩
      icases HI with ⟨%m, %hp, Hff, Hi, Ha, Hb, Hn⟩
      obtain ⟨-, hmn⟩ := hp
      iapply wp_block_nil
      idance
      iapply wp_seq_next
      idance
      -- the $forFirst dispatch
      iapply wp_if_start
      idance
      iapply (wp_eval_var (a := ffa) (cell := boolcell (m == 0))
        (hres := by
          simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
            Scope.lookup]))
      isplitl [Hff]
      · iexact Hff
      iintro Hff
      rcases m with - | m'
      · -- first iteration: unset the flag; the counter stays 0
        rw [show (((0 : Nat) == 0) : Bool) = true from rfl]
        iapply wp_if_bool
        idance
        rw [if_pos rfl]
        iapply (wp_assign_start (e := .ref "$forFirst") (sh := .chain [])
          (ops := []) rfl)
        idance
        iapply (wp_eval_ref (loc := .base ffa) (hres := by
          simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
            Scope.lookup]))
        idance
        iapply (wp_tgtop_rhs (r := .chain (.addr (.base ffa)) [] []) rfl)
        idance
        iapply wp_eval_boolLit
        idance
        iapply wp_rhs_stores_vals
        idance
        simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
        iapply (wp_assign_store (a := ffa) (oldcell := boolcell true)
          (newcell := boolcell false)
          (hstore := fun σ₁ _ht hlook => by
            simp [storeLoc, hlook, normalizeValueForTy,
              normalizeValueForTyFuel, typeResolutionFuel,
              Bind.bind, Except.bind]))
        isplitl [Hff]
        · iexact Hff
        iintro Hff
        iapply wp_stores_done_nil
        iapply (wp_fib_loop_tail (ffa := ffa) (ia := ia) (aa := aa)
          (ba := ba) (na := na) hn hmn
          (hia := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup])
          (hna := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup])
          (haa := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup])
          (hba := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup]))
        isplitl [Hff]
        · iexact Hff
        isplitl [Hi]
        · iexact Hi
        isplitl [Ha]
        · iexact Ha
        isplitl [Hb]
        · iexact Hb
        isplitl [Hn]
        · iexact Hn
        · iexact Hks
      · -- later iterations: the flag is already false; increment i
        rw [show (((m' + 1 : Nat) == 0) : Bool) = false from by simp,
          show (m' + 1 - 1 : Nat) = m' from by omega]
        iapply wp_if_bool
        idance
        rw [if_neg Bool.false_ne_true]
        iapply (wp_assign_start (e := .ref "i") (sh := .chain [])
          (ops := []) rfl)
        idance
        iapply (wp_eval_ref (loc := .base ia) (hres := by
          simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
            Scope.lookup]))
        idance
        iapply (wp_tgtop_rhs (r := .chain (.addr (.base ia)) [] []) rfl)
        idance
        iapply (wp_eval_strict (op := .add) (e₁ := .var "i")
          (rest := [.intLit 1 .uint64]) rfl)
        idance
        iapply (wp_eval_var (a := ia) (cell := u64cell (m' : Int))
          (hres := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup]))
        isplitl [Hi]
        · iexact Hi
        iintro Hi
        iapply wp_strict_shift
        idance
        iapply wp_eval_intLit
        idance
        rw [show IntKind.normalize .uint64 1 = 1 from by decide]
        iapply (wp_strict_apply_pure
          (out := .int ((m' + 1 : Nat) : Int) .uint64) (happly := by
            intro σ
            have hnorm : IntKind.normalize .uint64 ((m' : Int) + 1)
                = ((m' + 1 : Nat) : Int) := by
              rw [show ((m' : Int) + 1) = ((m' + 1 : Nat) : Int) from by omega]
              exact unorm_nat_of_lt (by omega)
            have hcomp : IntKind.compatibleResult .uint64 .uint64
                = some .uint64 := rfl
            simp [applyStrictOp, intBinaryResult, valueAsIntValue, hcomp,
              hnorm, Bind.bind, Except.bind]))
        idance
        iapply wp_rhs_stores_vals
        idance
        simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
        iapply (wp_assign_store (a := ia) (oldcell := u64cell (m' : Int))
          (newcell := u64cell ((m' + 1 : Nat) : Int))
          (hstore := fun σ₁ _ht hlook => by
            have h := storeLoc_int_cell (kind := .uint64) hlook
              ((m' + 1 : Nat) : Int)
            rwa [unorm_nat_of_lt (by omega)] at h))
        isplitl [Hi]
        · iexact Hi
        iintro Hi
        iapply wp_stores_done_nil
        iapply (wp_fib_loop_tail (ffa := ffa) (ia := ia) (aa := aa)
          (ba := ba) (na := na) hn hmn
          (hia := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup])
          (hna := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup])
          (haa := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup])
          (hba := by
            simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
              Scope.lookup]))
        isplitl [Hff]
        · iexact Hff
        isplitl [Hi]
        · iexact Hi
        isplitl [Ha]
        · iexact Ha
        isplitl [Hb]
        · iexact Hb
        isplitl [Hn]
        · iexact Hn
        · iexact Hks))
  isplitl [Hff Hi Ha Hb Hn]
  · -- the invariant holds on entry (m = 0)
    iexists true
    iexists 0
    isplitl []
    · ipureintro
      exact ⟨rfl, Nat.zero_le n⟩
    simp only [show (((0 : Nat) == 0) : Bool) = true from rfl,
      show ((0 - 1 : Nat) : Int) = (0 : Int) from rfl,
      show fibv 0 = 0 from rfl, show fibv (0 + 1) = 1 from rfl]
    isplitl [Hff]
    · iexact Hff
    isplitl [Hi]
    · iexact Hi
    isplitl [Ha]
    · iexact Ha
    isplitl [Hb]
    · iexact Hb
    · iexact Hn
  · -- the exit continuation
    iintro HIQ
    icases HIQ with (HIf | HQ)
    · -- the condition-exit disjunct is vacuous: the condition is `true`
      icases HIf with ⟨%m, %hp, -, -, -, -, -⟩
      exact absurd hp.1 (by decide)
    -- after the loop: drain the scopes, assign the result, return
    iapply wp_seq_done
    idance
    iapply wp_seq_done
    idance
    iapply wp_seq_next
    idance
    iapply wp_seqn
    simp only [List.toList_toArray, seqCont_splice, List.cons_append,
      List.nil_append, List.append_nil]
    idance
    iapply wp_seq_next
    idance
    -- $res0 = a
    iapply (wp_assign_start (e := .ref "$res0") (sh := .chain [])
      (ops := []) rfl)
    idance
    iapply (wp_eval_ref (loc := .base ra) (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup]))
    idance
    iapply (wp_tgtop_rhs (r := .chain (.addr (.base ra)) [] []) rfl)
    idance
    iapply (wp_eval_var (a := aa) (cell := u64cell (fibv n)) (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup]))
    isplitl [HQ]
    · iexact HQ
    iintro HQ
    iapply wp_rhs_stores_vals
    idance
    simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
    iapply (wp_assign_store (a := ra) (oldcell := u64cell 0)
      (newcell := u64cell (fibv n))
      (hstore := fun σ₁ _ht hlook => by
        have h := storeLoc_int_cell (kind := .uint64) hlook (fibv n)
        rwa [unorm_fibv] at h))
    isplitl [Hres]
    · iexact Hres
    iintro Hres
    iapply wp_stores_done_nil
    iapply wp_seq_next
    idance
    -- return
    iapply wp_return
    idance
    iapply wp_seq_return
    idance
    iapply Hcont $$ Hres

/-- **The driver walk, exit form**:
`{r ↦ 0} $callres = fib(n) {r ↦ fibv n}` as the WP entailment
`goSpec_of_wp` consumes. -/
theorem wp_fibCall (n : Nat) (hn : n < 2 ^ 64)
    (hprog : GoCoreGS.prog GF = fibLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) fibCell0
      ⊢ WP (Config.exec (fibCall n) fibEnv .stop)
          {{ _v, embed (fibCellV (fibv n)) }} := by
  simp only [fibCell0, fibCellV, embed, fibCall, fibEnv]
  iintro Hr
  iapply (wp_call_start (plans := [(.chain [], [.ref "$callres"])])
    rfl rfl)
  idance
  iapply wp_eval_intLit
  idance
  rw [unorm_nat_of_lt hn]
  iapply (wp_call_enter₁₁ (func := fibFunc)
    (w₀ := .int (n : Int) .uint64) (dv₀ := .int 0 .uint64)
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ _h1 h2 _h3 => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h2, hmeths,
        Bind.bind, Except.bind])
    (hnorm₀ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, unorm_nat_of_lt hn, Bind.bind, Except.bind])
    (hdef₀ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %na₀ %ra₀ ⟨Hn, Hres⟩
  iapply (wp_fib_body hn)
  isplitl [Hn]
  · iexact Hn
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  iapply (wp_frame_return_int (x := "$callres") (kind := .uint64)
    (tkind := .uint64) (m := fibv n) (w := .int 0 .uint64) (hres := rfl))
  isplitl [Hres]
  · iexact Hres
  isplitl [Hr]
  · iexact Hr
  iintro ⟨-, Hr⟩
  rw [unorm_fibv] at *
  iapply (wp_value' (v := ()))
  iexact Hr

end Walk

/-! ## The specification -/

/-- **The frame-closed surface judgment, ∀-input over the whole uint64
domain**: `{r ↦ 0} r = fib(n) {r ↦ fibSpec n % 2^64}` plus
interpreter-side safety. The per-program work is the WP walk
(`wp_fibCall`), one symbolic proof for every `n` — the loop is handled
by `wp_while_inv_break` with the Fibonacci pair invariant. -/
theorem fibGoSpec (n : Nat) (hn : n < 2 ^ 64) :
    GoSpec fibLowered.typeDefs.toList fibLowered.funcs fibLowered.methods
      fibEnv fibCell0 (fibCall n) (fibCellV (fibv n)) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_fibCall n hn hprog hmeths

/-! ## Seeded readout (the golden-pin composition, at the fib seed) -/

/-- The generic sequential readout at the fib seed (the
`goSpec_seeded_readout` shape, at this example's uint64 cell). -/
private theorem fib_seeded_readout {prog : Stmt} {v : Int}
    (hspec : GoSpec fibLowered.typeDefs.toList fibLowered.funcs
      fibLowered.methods fibEnv fibCell0 prog (fibCellV v))
    (hwf : MachineWf
      { functions := fibLowered.funcs,
        heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)],
        nextAddr := 1 }
      (.exec prog fibEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel fibEnv fibSeed ch prog = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int v .uint64) := by
  intro fuel ch σf ch' hrun
  have hsat : sat
      (heapletOf [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)])
      fibCell0 := rfl
  have hsplit := InitialSplit.noFrame (P := fibCell0)
    (hp := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]) (na := 1)
    (funcs := fibLowered.funcs) (env₀ := fibEnv) (prog := prog) hsat hwf
  have hres := hspec.1 _ 1 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsatQ⟩ := hres
  rw [show h = (∅ : Heaplet).insert 0 ⟨some (.int .uint64), .int v .uint64⟩
    from hsatQ] at hsub
  have hget := hsub 0 ⟨some (.int .uint64), .int v .uint64⟩ (by
    rw [heaplet_get?_eq, heaplet_insert_eq]
    exact LawfulPartialMap.get?_insert_eq rfl)
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hget
  exact loadLoc_base_of_lookup hget

/-! ## Termination on the headline domain (kernel-enumerated)

Foundation debt (design note §4): this is 94 per-seed checker runs in
one kernel evaluation — the bounded-domain price of not yet having
symbolic termination. -/

private theorem fib_allStreamsOk :
    ((List.range 94).all fun n =>
      allStreamsOk 6000 fibSeed (.exec (fibCall n) fibEnv .stop)) = true := by
  decide +kernel

/-- The program terminates from the seeded state — at every
nondeterminism-choice stream, past fuel 6000 — for every `n ≤ 93`. -/
theorem fibTerminates (n : Nat) (hn : n ≤ 93) :
    Terminates fibEnv fibSeed (fibCall n) := by
  have h1 : allStreamsOk 6000 fibSeed (.exec (fibCall n) fibEnv .stop)
      = true :=
    List.all_eq_true.mp fib_allStreamsOk n (List.mem_range.mpr (by omega))
  refine ⟨6000, fun fuel hfuel ch => ?_⟩
  obtain ⟨out, ch', hrun⟩ := execStmtLoop_ok_of_allStreamsOk h1 ch
  exact ⟨out, ch', execStmtLoop_mono 6000 fuel _ _ _ _ hfuel hrun⟩

/-! ## The user-facing statements -/

/-- **Full-domain companion (machine-integer honesty)**: for every
value `n` of the Go argument type `uint64`, every run of
`$callres = fib(n)` from the seeded state that completes normally
leaves `fibSpec n % 2^64` in the result cell — exactly what Go's
wrapping uint64 arithmetic computes, on the whole domain, past the
overflow boundary at `n = 94`. Genuinely ∀-input: one symbolic proof,
no enumeration. (Run-conditioned — the full-domain TOTAL form is the
recorded symbolic-termination debt, design note §4.) -/
theorem fib_wraps (n : Nat) (hn : n < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
        = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64) :=
  fib_seeded_readout (fibGoSpec n hn) (fibSeedWf n)

/-- **THE PROPOSED HEADLINE** (design note §2; slice-1 checkpoint
object): for every `n ≤ 93` — the largest argument whose Fibonacci
number fits in uint64 — execution of `$callres = fib(n)` from the
seeded state COMPLETES NORMALLY (no panic, no stuck state, no error;
past one fuel bound, at every nondeterminism-choice stream) and the
result cell holds EXACTLY `fibSpec n`.

Total correctness, read right off the executable interpreter: the
completion and the value in one statement, quantified over the input. -/
theorem fib_ok (n : Nat) (hn : n ≤ 93) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int (fibSpec n) .uint64) := by
  have hn64 : n < 2 ^ 64 := by
    have : (93 : Nat) < 2 ^ 64 := by decide
    omega
  have hfib : fibSpec n < 2 ^ 64 := fibSpec_lt_of_le_93 hn
  have hmod : ((fibSpec n % 2 ^ 64 : Nat) : Int) = (fibSpec n : Int) := by
    rw [Nat.mod_eq_of_lt hfib]
  have hsat : sat
      (heapletOf [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)])
      fibCell0 := rfl
  have hsplit := InitialSplit.noFrame (P := fibCell0)
    (hp := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]) (na := 1)
    (funcs := fibLowered.funcs) (env₀ := fibEnv) (prog := fibCall n)
    hsat (fibSeedWf n)
  have hnorm : TerminatesNormally fibEnv fibSeed (fibCall n) :=
    terminatesNormally_of_progressExec hsplit (fibGoSpec n hn64).2
      (fibTerminates n hn)
  obtain ⟨N, hN⟩ := hnorm
  refine ⟨N, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun⟩ := hN fuel hfuel ch
  have hread := fib_wraps n hn64 fuel ch σf ch' hrun
  rw [hmod] at hread
  exact ⟨σf, ch', hrun, hread⟩

/-! ## The D1 concurrent-carrier twins (standing convention) -/

/-- The triple on the concurrent carrier, via the conservation
transfer (sequential-degenerate lane — the program spawns nothing). -/
theorem fibGoSpecC (n : Nat) (hn : n < 2 ^ 64) :
    GoSpecC fibLowered.typeDefs.toList fibLowered.funcs fibLowered.methods
      fibEnv fibCell0 (fibCall n) (fibCellV (fibv n)) :=
  goSpecC_of_goSpec (fibGoSpec n hn)

/-- The full-domain readout on the concurrent carrier: every `.normal`
POOL completion of the seeded driver leaves `fibSpec n % 2^64` in the
result cell. -/
theorem fib_wrapsC (n : Nat) (hn : n < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
        = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64) := by
  intro fuel ch σf ch' hrun
  have hsat : sat
      (heapletOf [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)])
      fibCell0 := rfl
  have hsplit := InitialSplit.noFrame (P := fibCell0)
    (hp := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]) (na := 1)
    (funcs := fibLowered.funcs) (env₀ := fibEnv) (prog := fibCall n)
    hsat (fibSeedWf n)
  rcases (fibGoSpec n hn).2 _ _ _ _ hsplit fuel ch with ⟨σs, chs, hseq⟩ | hseq
  · have hpool := execProg_single_eq_execStmt hseq trivial
    have hrun' : execProg fuel fibEnv fibSeed ch (fibCall n)
        = .ok (.normal σf, ch') := hrun
    rw [show fibSeed
        = { types := fibLowered.typeDefs.toList,
            functions := fibLowered.funcs, methods := fibLowered.methods,
            heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)],
            nextAddr := 1 } from rfl] at hrun'
    rw [hrun'] at hpool
    injection hpool with hpair
    injection hpair with hout hch
    injection hout with hσ
    subst hσ
    subst hch
    exact fib_wraps n hn fuel ch σf ch' hseq
  · have hpool := execProg_single_eq_execStmt hseq trivial
    have hrun' : execProg fuel fibEnv fibSeed ch (fibCall n)
        = .ok (.normal σf, ch') := hrun
    rw [show fibSeed
        = { types := fibLowered.typeDefs.toList,
            functions := fibLowered.funcs, methods := fibLowered.methods,
            heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)],
            nextAddr := 1 } from rfl] at hrun'
    rw [hrun'] at hpool
    cases hpool

end GoLean.Examples.Fib
