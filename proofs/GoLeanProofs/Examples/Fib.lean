import GoLeanProofs.Examples.FibProgram
import GoLeanProofs.SurfaceExit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
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

The user-facing statements (THE HARNESS RULING, 2026-08-13 — design
note §11: the final user-facing form, stated through the machine's
native function entry `runFunctionWithContextM` on the three-phase Go
harness `fib_harness`; no cell/seed/env vocabulary appears in them):

* `fib_ok` — THE HEADLINE: for every `n ≤ 93` (the largest argument
  whose Fibonacci number fits in uint64), `fib_harness(n)` completes
  normally — no panic, no stuck state, no error, at every sufficient
  fuel and every nondeterminism-choice stream — and returns exactly
  `fibSpec n`.
* `fib_total` — FULL-DOMAIN total correctness: for every `n < 2^64`
  (every value of the Go argument type), `fib_harness(n)` completes
  normally and returns `fibSpec n % 2^64` — machine-integer honesty
  (FD-E3): what Go's uint64 arithmetic actually computes past the
  overflow boundary.

The proof-side supporting layer (kept per §11: the framed forms
`fib_framed`/`fib_total_framed`, the seeded forms
`fib_wraps_seeded`/`fib_total_seeded`, `fibGoSpec`, `fibTerminates`)
carries the harness headlines' derivations and the ∀-frame story.

EVERYTHING HERE IS SYMBOLIC IN `n` (checkpoint ruling 2026-08-12:
enumeration is banned as a proof method). The value half is the WP
walk through `wp_while_inv_break` with the Fibonacci pair invariant;
the completion half is the fuel-measure rule
(`FuelMeasure.completesIn_measure_loop`, its same-commit discharge
witness) instantiated at four `with_unfolding_all rfl` run segments —
the termination section below records the shape.

Scope honesty (the charter's two-questions separation): these theorems
are USABILITY evidence — the reasoning layer carrying a natural spec
through a real program — never machine-hardening evidence; the machine
itself is validated by the differential corpus and audited separately.
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

/-! ## Termination, symbolic (the fuel-measure route)

Checkpoint ruling 2026-08-12: enumeration is banned as a proof method —
the 94-seed kernel enumeration that first discharged this domain is
DELETED and replaced by `FuelMeasure.completesIn_measure_loop`, the
completion-side twin of `wp_while_inv_break` (see the module docstring
there for why this half deliberately has no Iris in it).

The instantiation: four run SEGMENTS, each a `with_unfolding_all rfl`
computation of the interpreter with the input symbolic (`rfl` because
every step is definitional once the sealed value-walk wrappers are
opened — the open subterms, `n` and the `fibSpec` values, are carried
as data and only the loop's exit test branches on them, which is
exactly where the segments split):

* entry (57 steps): seed → the loop head at `m = 0`;
* head → exit test (25 steps on the first pass, 29 after — the
  `$forFirst` desugar's two dispatch branches);
* test-true → head (27 steps): the pair update, re-establishing the
  head state at `m + 1` — the measure (`n - m`) strictly decreases;
* test-false → the `.normal` terminal (27 steps): break, result
  assignment, return, frame exit.

The measure rule then yields completion at fuel `56·n + 113` for EVERY
`n < 2^64` — the FULL Go domain, not an enumerable bound: the
per-iteration facts are one proof each, symbolic in both `n` and the
iteration count. -/

private def fibLoopEnv : LocalEnv :=
  [[("$forFirst", .base ⟨6⟩)], [("i", .base ⟨5⟩)],
   [("b", .base ⟨4⟩), ("a", .base ⟨3⟩)],
   [("$res0", .base ⟨2⟩), ("n", .base ⟨1⟩)]]

/-- The loop-head continuation (scope drains, the trailing
`$res0 = a; return`, the caller frame). -/
private def fibHeadCont : Cont :=
  .seq [] fibLoopEnv
    (.seq [] [[("i", .base ⟨5⟩)], [("b", .base ⟨4⟩), ("a", .base ⟨3⟩)],
              [("$res0", .base ⟨2⟩), ("n", .base ⟨1⟩)]]
      (.seq [.seqn #[.assign (.var "$res0") (.var "a"), .returnStmt]]
        [[("b", .base ⟨4⟩), ("a", .base ⟨3⟩)],
         [("$res0", .base ⟨2⟩), ("n", .base ⟨1⟩)]]
        (.frame [(.chain [], [.ref "$callres"])] [[("$callres", .base ⟨0⟩)]]
          [.base ⟨2⟩] [] .stop false)))

/-- The loop-head configuration — `completesIn_measure_loop`'s `chead`. -/
private def fibHeadConfig : Config :=
  .exec (.while (.boolLit true) fibWhileBody) fibLoopEnv fibHeadCont

/-- The exit test's delivery continuation (segment split point). -/
private def fibCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt fibLoopEnv.pushScope
    (.seq [fibIterBlock] fibLoopEnv.pushScope
      (.loop (.boolLit true) fibWhileBody fibLoopEnv fibHeadCont))

private def fibHeap (nv av bv iv : Int) (ffv : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell 0), (.base ⟨1⟩, u64cell nv), (.base ⟨2⟩, u64cell 0),
   (.base ⟨3⟩, u64cell av), (.base ⟨4⟩, u64cell bv),
   (.base ⟨5⟩, u64cell iv), (.base ⟨6⟩, boolcell ffv)]

private def fibState (h : Heap) : ExecState :=
  { types := fibLowered.typeDefs.toList, functions := fibLowered.funcs,
    methods := fibLowered.methods, heap := h, nextAddr := 7 }

/-- The loop-head state after `m` completed iterations: the pair holds
the wrapped `fibSpec m`/`fibSpec (m+1)`, the counter lags one
(saturating at the first pass), the flag marks the first pass. -/
private def fibHeadState (n m : Nat) : ExecState :=
  fibState (fibHeap (n : Int) (fibv m) (fibv (m + 1))
    ((m - 1 : Nat) : Int) (m == 0))

/-- The state at the exit test: flag down, counter caught up to `m`. -/
private def fibCmpState (n m : Nat) : ExecState :=
  fibState (fibHeap (n : Int) (fibv m) (fibv (m + 1)) ((m : Nat) : Int) false)

private theorem fib_entry_raw (n : Nat) (ch : Choices) :
    stepFnIter 57 fibSeed (.exec (fibCall n) fibEnv .stop) ch
      = .ok (fibHeadConfig,
          fibState (fibHeap
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (n : Int)))
            0 1 0 true), ch) := by
  with_unfolding_all rfl

/-- Entry segment, cleaned: seed → head at `m = 0`. -/
private theorem fib_entry (n : Nat) (hn : n < 2 ^ 64) (ch : Choices) :
    stepFnIter 57 fibSeed (.exec (fibCall n) fibEnv .stop) ch
      = .ok (fibHeadConfig, fibHeadState n 0, ch) := by
  rw [fib_entry_raw,
    show fibState (fibHeap
        (IntKind.normalize .uint64 (IntKind.normalize .uint64 (n : Int)))
        0 1 0 true) = fibHeadState n 0 from by
      simp only [fibHeadState, unorm_nat_of_lt hn,
        show fibv 0 = 0 from rfl, show fibv (0 + 1) = 1 from rfl,
        show ((0 - 1 : Nat) : Int) = 0 from rfl,
        show (((0 : Nat) == 0) : Bool) = true from rfl]]

/-- First-pass dispatch: head at `m = 0` → the exit test (the
`$forFirst` then-branch: unset the flag; the counter stays 0). -/
private theorem fib_segA0 (n : Nat) (ch : Choices) :
    stepFnIter 25 (fibHeadState n 0) fibHeadConfig ch
      = .ok (.retV (.bool (decide ((0 : Int) < (n : Int)))) fibCmpCont,
          fibCmpState n 0, ch) := by
  with_unfolding_all rfl

private theorem fib_segA1_raw (n m : Nat) (ch : Choices) :
    stepFnIter 29 (fibHeadState n (m + 1)) fibHeadConfig ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 ((m : Int) + 1))
              < (n : Int)))) fibCmpCont,
          fibState (fibHeap (n : Int) (fibv (m + 1)) (fibv (m + 2))
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64 ((m : Int) + 1))) false), ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch, cleaned: head at `m + 1` → the exit test (the
else-branch: increment the counter). -/
private theorem fib_segA1 (n m : Nat) (hm : m + 1 < 2 ^ 64) (ch : Choices) :
    stepFnIter 29 (fibHeadState n (m + 1)) fibHeadConfig ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            fibCmpCont,
          fibCmpState n (m + 1), ch) := by
  rw [fib_segA1_raw,
    show ((m : Int) + 1) = ((m + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt hm, unorm_nat_of_lt hm]
  rfl

private theorem fib_segBC_raw (n m : Nat) (ch : Choices) :
    stepFnIter 27 (fibCmpState n m) (.retV (.bool true) fibCmpCont) ch
      = .ok (fibHeadConfig,
          fibState (fibHeap (n : Int)
            (IntKind.normalize .uint64 (fibv (m + 1)))
            (IntKind.normalize .uint64 (IntKind.normalize .uint64
              (fibv m + fibv (m + 1))))
            ((m : Nat) : Int) false), ch) := by
  with_unfolding_all rfl

/-- Continue segment, cleaned: exit test true → head at `m + 1`
(`a, b = b, a+b`, wrapping — the measure decreases). -/
private theorem fib_segBC (n m : Nat) (ch : Choices) :
    stepFnIter 27 (fibCmpState n m) (.retV (.bool true) fibCmpCont) ch
      = .ok (fibHeadConfig, fibHeadState n (m + 1), ch) := by
  rw [fib_segBC_raw, unorm_fibv_add, unorm_fibv, unorm_fibv,
    show fibHeadState n (m + 1)
        = fibState (fibHeap (n : Int) (fibv (m + 1)) (fibv (m + 2))
            ((m : Nat) : Int) false) from by
      simp only [fibHeadState, show (m + 1 - 1 : Nat) = m from by omega,
        show (((m + 1 : Nat) == 0) : Bool) = false from by simp]]

/-- Break segment: exit test false → the `.normal` terminal (break,
`$res0 = a`, return, frame exit into the harness cell). -/
private theorem fib_segBE_raw (n m : Nat) (ch : Choices) :
    stepFnIter 27 (fibCmpState n m) (.retV (.bool false) fibCmpCont) ch
      = .ok (.next .stop,
          fibState [(.base ⟨0⟩, u64cell (IntKind.normalize .uint64
              (IntKind.normalize .uint64 (fibv m)))),
            (.base ⟨1⟩, u64cell (n : Int)),
            (.base ⟨2⟩, u64cell (IntKind.normalize .uint64 (fibv m))),
            (.base ⟨3⟩, u64cell (fibv m)),
            (.base ⟨4⟩, u64cell (fibv (m + 1))),
            (.base ⟨5⟩, u64cell ((m : Nat) : Int)),
            (.base ⟨6⟩, boolcell false)], ch) := by
  with_unfolding_all rfl

/-- One full iteration: head at `m` → head at `m + 1`, within 56
interpreter steps (52 on the first pass). -/
private theorem fib_iter (n m : Nat) (hn : n < 2 ^ 64) (hlt : m < n)
    (ch : Choices) :
    ∃ k, k ≤ 56 ∧ stepFnIter k (fibHeadState n m) fibHeadConfig ch
      = .ok (fibHeadConfig, fibHeadState n (m + 1), ch) := by
  match m, hlt with
  | 0, hlt =>
    refine ⟨25 + 27, by omega, ?_⟩
    have hA := fib_segA0 n ch
    rw [show (decide ((0 : Int) < (n : Int))) = true from
      decide_eq_true (by omega)] at hA
    exact stepFnIter_chain hA (fib_segBC n 0 ch)
  | m' + 1, hlt =>
    refine ⟨29 + 27, by omega, ?_⟩
    have hA := fib_segA1 n m' (by omega) ch
    rw [show (decide (((m' + 1 : Nat) : Int) < (n : Int))) = true from
      decide_eq_true (by omega)] at hA
    exact stepFnIter_chain hA (fib_segBC n (m' + 1) ch)

/-- The exit pass: head at `m = n` → completion, within 56 fuel. -/
private theorem fib_exit (n : Nat) (hn : n < 2 ^ 64) :
    CompletesIn 56 (fibHeadState n n) fibHeadConfig := by
  intro ch
  match n, hn with
  | 0, _ =>
    have hA := fib_segA0 0 ch
    rw [show (decide ((0 : Int) < ((0 : Nat) : Int))) = false from by decide]
      at hA
    have hchain0 := stepFnIter_chain hA (fib_segBE_raw 0 0 ch)
    obtain ⟨σf, hchain⟩ : ∃ σf, stepFnIter (25 + 27) (fibHeadState 0 0)
        fibHeadConfig ch = .ok (.next .stop, σf, ch) := ⟨_, hchain0⟩
    have hrun : execStmtLoop 56 (fibHeadState 0 0) fibHeadConfig ch
        = .ok (.normal σf, ch) := by
      rw [show (56 : Nat) = 25 + 27 + 4 from by omega,
        execStmtLoop_of_stepFnIter hchain 4, execStmtLoop_next_stop]
    exact ⟨_, _, hrun⟩
  | n' + 1, hn =>
    have hA := fib_segA1 (n' + 1) n' (by omega) ch
    rw [show (decide (((n' + 1 : Nat) : Int) < ((n' + 1 : Nat) : Int)))
        = false from decide_eq_false (by omega)] at hA
    have hchain0 := stepFnIter_chain hA (fib_segBE_raw (n' + 1) (n' + 1) ch)
    obtain ⟨σf, hchain⟩ : ∃ σf, stepFnIter (29 + 27)
        (fibHeadState (n' + 1) (n' + 1)) fibHeadConfig ch
        = .ok (.next .stop, σf, ch) := ⟨_, hchain0⟩
    have hrun : execStmtLoop 56 (fibHeadState (n' + 1) (n' + 1))
        fibHeadConfig ch = .ok (.normal σf, ch) := by
      rw [show (56 : Nat) = 29 + 27 + 0 from by omega,
        execStmtLoop_of_stepFnIter hchain 0, execStmtLoop_next_stop]
    exact ⟨_, _, hrun⟩

/-- The loop completes from the head at `m = 0` within `56·n + 56`
fuel — `completesIn_measure_loop` at the invariant "`m` iterations
done, `μ = n - m` remain". -/
private theorem fib_loop_completes (n : Nat) (hn : n < 2 ^ 64) :
    CompletesIn (56 * n + 56) (fibHeadState n 0) fibHeadConfig := by
  refine completesIn_measure_loop
    (S := fun μ σ => ∃ m, m + μ = n ∧ σ = fibHeadState n m)
    (hiter := ?_) (hexit := ?_) n (fibHeadState n 0) ⟨0, by omega, rfl⟩
  · intro μ σ hS ch
    obtain ⟨m, hm, rfl⟩ := hS
    obtain ⟨k, hk, hstep⟩ := fib_iter n m hn (by omega) ch
    exact ⟨k, fibHeadState n (m + 1), ch, μ, hk, Nat.le_refl _, hstep,
      m + 1, by omega, rfl⟩
  · intro σ hS
    obtain ⟨m, hm, rfl⟩ := hS
    have hmn : m = n := by omega
    subst hmn
    exact fib_exit m hn

/-- **The program terminates from the seeded state, for EVERY `n` in
the full uint64 domain** — at every nondeterminism-choice stream, past
fuel `56·n + 113`. Symbolic in `n` (the fuel-measure rule; no
enumeration anywhere). -/
theorem fibTerminates (n : Nat) (hn : n < 2 ^ 64) :
    Terminates fibEnv fibSeed (fibCall n) := by
  apply terminates_of_completesIn (N := 57 + (56 * n + 56))
  apply completesIn_comp (k₀ := 57)
  intro ch
  exact ⟨57, fibHeadConfig, fibHeadState n 0, ch, Nat.le_refl _,
    fib_entry n hn ch, fib_loop_completes n hn⟩

/-! ## The user-facing statements -/

/-- Proof-side supporting layer (§11): the run-conditioned seeded
readout, consumed by `fib_total_seeded` (and through it by
`fib_total_framed` and the harness headlines' derivation chain) — for
every `n < 2^64`, every normal completion of the seeded driver leaves
`fibSpec n % 2^64` in the result cell. Consumed, not a shell; the
user-facing statements are the harness pair `fib_ok`/`fib_total`
below. -/
theorem fib_wraps_seeded (n : Nat) (hn : n < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
        = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64) :=
  fib_seeded_readout (fibGoSpec n hn) (fibSeedWf n)

/-- Proof-side supporting layer (§11): full-domain TOTAL correctness
at the SEEDED driver (`$callres = fib(n)` from the canonical seed) —
consumed by `fib_total_framed` (its completion half transfers through
the executable frame theorem). Consumed, not a shell; the user-facing
statements are the harness pair `fib_ok`/`fib_total` below. The
completion half is the symbolic fuel-measure proof (`fibTerminates`);
nothing here is enumerated. -/
theorem fib_total_seeded (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64) := by
  have hsat : sat
      (heapletOf [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)])
      fibCell0 := rfl
  have hsplit := InitialSplit.noFrame (P := fibCell0)
    (hp := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]) (na := 1)
    (funcs := fibLowered.funcs) (env₀ := fibEnv) (prog := fibCall n)
    hsat (fibSeedWf n)
  have hnorm : TerminatesNormally fibEnv fibSeed (fibCall n) :=
    terminatesNormally_of_progressExec hsplit (fibGoSpec n hn).2
      (fibTerminates n hn)
  obtain ⟨N, hN⟩ := hnorm
  refine ⟨N, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun⟩ := hN fuel hfuel ch
  exact ⟨σf, ch', hrun, fib_wraps_seeded n hn fuel ch σf ch' hrun⟩

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
    exact fib_wraps_seeded n hn fuel ch σf ch' hseq
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

/-! ## The framed (memory-quantified) form — slice 2a (2026-08-13)

Form ruling (user, 2026-08-13): headlines unify to the
memory-quantified form — input data + an arbitrary disjoint frame, with
frame preservation VISIBLE in the statement. This is fib's retrofit:
the input stays a call argument (fib takes no memory input); what
changes is the frame story — *"touches nothing but the result cell"*
becomes part of the claim. The exact frame structure is under the
slice-2a checkpoint (design note §9); this theorem is the PROPOSAL
instantiated.

Scope honesty: run-conditioned over the framed seeds — the completion
half at an ARBITRARY framed seed needs ∀-admissible-state termination
(allocation addresses depend on `nextAddr`, so the canonical run's
segment computations do not transfer verbatim); that gap is priced in
the design note (§9c) and ruled on at the checkpoint. Completion at
the canonical seed is `fib_total_seeded`. -/

/-- fib's framed seed: the result cell plus an arbitrary frame `fr`,
allocator at `na`. -/
def fibSeedFr (fr : Heap) (na : Nat) : ExecState :=
  { types := fibLowered.typeDefs.toList, functions := fibLowered.funcs,
    methods := fibLowered.methods,
    heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
    nextAddr := na }

/-- **The memory-quantified fib claim (slice-2a proposal)**: for every
`n` in the uint64 domain, every frame `fr` — ANY other memory contents,
not mentioning the result cell — and every admissible allocator bound,
every normal completion of `$callres = fib(n)` from the framed seed
(1) delivers `fibSpec n % 2^64` in the result cell and
(2) PRESERVES THE FRAME: every cell of `fr` is still there, unchanged.
Cells the run allocates (the callee's frame) are fresh — they are
outside both the input and `fr` — and are deliberately not claimed. -/
theorem fib_framed (n : Nat) (hn : n < 2 ^ 64) (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := fibLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (fibCall n) fibEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel fibEnv (fibSeedFr fr na) ch (fibCall n)
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
          = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64)
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c := by
  intro fuel ch σf ch' hrun
  -- the admissible split: footprint = the result cell, frame = fr
  have hF0 : (heapletOf fr).get? 0 = none := by
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap]
    exact hfr
  have hsplit : InitialSplit fibCell0
      ((.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr) na
      ((∅ : Heaplet).insert 0 ⟨some (.int .uint64), .int 0 .uint64⟩)
      (heapletOf fr) fibLowered.funcs fibEnv (fibCall n) := {
    disj := by
      intro k
      by_cases hk : k = 0
      · subst hk
        exact .inr hF0
      · left
        rw [heaplet_get?_eq, heaplet_insert_eq]
        rw [LawfulPartialMap.get?_insert_ne (M := GoHeapF)
          (fun h => hk h.symm)]
        exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)
    cover := by
      intro k c
      rw [heaplet_get?_eq, heapletOf_eq_heapToMap, heapToMap_cons_base,
        heaplet_get?_eq, heaplet_insert_eq, heaplet_get?_eq,
        heapletOf_eq_heapToMap]
      by_cases hk : k = 0
      · subst hk
        rw [LawfulPartialMap.get?_insert_eq (M := GoHeapF) rfl,
          LawfulPartialMap.get?_insert_eq (M := GoHeapF) rfl]
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq, heapletOf_eq_heapToMap] at hF0
            rw [hF0] at h
            cases h
      · rw [LawfulPartialMap.get?_insert_ne (M := GoHeapF)
            (fun h => hk h.symm),
          LawfulPartialMap.get?_insert_ne (M := GoHeapF)
            (fun h => hk h.symm),
          LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)]
        constructor
        · exact fun h => .inr h
        · rintro (h | h)
          · cases h
          · exact h
    sat_pre := rfl
    wf := hwf }
  have hres := (fibGoSpec n hn).1 _ na _ (heapletOf fr) hsplit
    fuel ch σf ch' hrun
  obtain ⟨hQ, _hd, hQsub, hFsub, hsatQ⟩ := hres
  constructor
  · -- the readout, through the Q-footprint
    rw [show hQ = (∅ : Heaplet).insert 0
        ⟨some (.int .uint64), .int (fibv n) .uint64⟩ from hsatQ] at hQsub
    have hget := hQsub 0 ⟨some (.int .uint64), .int (fibv n) .uint64⟩ (by
      rw [heaplet_get?_eq, heaplet_insert_eq]
      exact LawfulPartialMap.get?_insert_eq rfl)
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hget
    exact loadLoc_base_of_lookup hget
  · -- frame preservation, pointwise
    intro a c hac
    have hFa : (heapletOf fr).get? a = some c := by
      rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap]
      exact hac
    have := hFsub a c hFa
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at this
    exact this

/-! ## The ∀-frame TOTAL form (slice 2b — the frame theorem consumed)

`fib_total_framed` = `fib_total_seeded`'s completion + the executable frame
theorem's completion transfer (`Frame.completesIn_ren` machinery via
`Frame.execStmtLoop_ren`, which also preserves the `.normal` tag) at
the seed simulation below. The canonical seed is TIGHT (dom = {0},
`na₀ = 1`) — exactly what `fr_avoid`'s seed discharge needs (build
handoff §3 finding 3: `MachineWf` enters only here, never through the
induction). -/

open GoLean.Frame

/-- The seed simulation: fib's canonical seed beside the framed seed,
through the uniform shift `[1, ∞) ≃ [na, ∞)`. -/
private theorem fibSeedFrameSim (n : Nat) (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := fibLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (fibCall n) fibEnv .stop)) :
    FrameSim (uniformShift 1 na) 1 na fr fibSeed (fibSeedFr fr na) := by
  have h1na : 1 ≤ na := by
    have hs := hwf.1
    simp only [StateWf, ExecState.locSup, Heap.locSup, Loc.locSup,
      Loc.rootBase, Nat.max_le] at hs
    omega
  have hfrsup : Heap.locSup fr ≤ na := by
    have hs := hwf.1
    simp only [StateWf, ExecState.locSup, Heap.locSup, Nat.max_le] at hs
    omega
  have hren0 : renameLoc (uniformShift 1 na) (.base ⟨0⟩) = .base ⟨0⟩ := by
    simp [renameLoc, uniformShift]
  refine ⟨uniformShift_spec h1na, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- next_eq: na = ρ 1
    simp [fibSeedFr, fibSeed, uniformShift]
  · -- alloc_reg
    exact Nat.le_refl 1
  · -- lookup_img
    intro l
    by_cases hl : l = .base ⟨0⟩
    · subst hl
      rw [hren0]
      simp [fibSeedFr, fibSeed, Heap.lookup, renameCell, renameValue]
    · have hcanon : Heap.lookup fibSeed.heap l = none := by
        have hne : ((.base ⟨0⟩ : Loc) == l) = false :=
          beq_false_of_ne (fun h => hl h.symm)
        simp [fibSeed, Heap.lookup, hne]
      rw [hcanon]
      have hne' : ((.base ⟨0⟩ : Loc) == renameLoc (uniformShift 1 na) l)
          = false := by
        refine beq_false_of_ne (fun hc => ?_)
        cases l with
        | base a =>
            simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at hc
            have : a.id = 0 := by
              by_cases ha : a.id < 1
              · omega
              · exfalso
                simp only [uniformShift, if_neg (by omega)] at hc
                omega
            exact hl (by cases a; simp_all)
        | field b tid f => simp [renameLoc] at hc
        | index b i => simp [renameLoc] at hc
      simp [fibSeedFr, Heap.lookup, hne']
  · -- frame_pres
    intro l c hl
    have hne : ((.base ⟨0⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hfr] at hl
      cases hl
    simp [fibSeedFr, Heap.lookup, hne]
    exact hl
  · -- fr_avoid
    intro a
    by_cases ha : a < 1
    · have : a = 0 := by omega
      subst this
      simpa [uniformShift] using hfr
    · cases hlk : Heap.lookup fr (.base ⟨uniformShift 1 na a⟩) with
      | none => rfl
      | some c =>
          exfalso
          have hkey := Heap.lookup_key_locSup hlk
          simp only [Loc.locSup, Loc.rootBase] at hkey
          simp only [uniformShift, if_neg ha] at hkey
          omega
  · -- bodies_inv
    exact renameBodies_id (fun x hx => uniformShift_low hx)
      (n := 1) (by decide)

/-- **The ∀-frame TOTAL fib claim (slice 2b)**: for every `n` in the
uint64 domain, every disjoint frame, and every admissible allocator
bound, execution from the FRAMED seed completes normally — past one
fuel bound, at every choice stream — with `fibSpec n % 2^64` in the
result cell and every frame cell preserved verbatim. `fib_total_seeded`'s
completion transfers through the executable frame theorem; nothing is
re-run at the framed placement. -/
theorem fib_total_framed (n : Nat) (hn : n < 2 ^ 64) (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := fibLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (fibCall n) fibEnv .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv (fibSeedFr fr na) ch (fibCall n)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64)
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c := by
  have hSF := fibSeedFrameSim n fr na hfr hwf
  have hcfg : renameConfig (uniformShift 1 na)
      (.exec (fibCall n) fibEnv .stop) = .exec (fibCall n) fibEnv .stop := by
    have hstmt : renameStmt (uniformShift 1 na) (fibCall n) = fibCall n :=
      Frame.renameStmt_id (n := 1) (fun x hx => Frame.uniformShift_low hx)
        _ (by
          simp [fibCall, Stmt.locSup, assigneeListSup, Assignee.locSup,
            exprListSup, Expr.locSup])
    have henv : renameEnv (uniformShift 1 na) fibEnv = fibEnv :=
      Frame.renameEnv_id (n := 1) (fun x hx => Frame.uniformShift_low hx)
        _ (by
          simp [fibEnv, LocalEnv.locSup, Scope.locSup, Loc.locSup,
            Loc.rootBase])
    simp [renameConfig, renameCont, hstmt, henv]
  obtain ⟨N, hN⟩ := fib_total_seeded n hn
  refine ⟨N, fun fuel hfuel ch => ?_⟩
  obtain ⟨σc, ch', hrun, hread⟩ := hN fuel hfuel ch
  have hrunL : execStmtLoop fuel fibSeed (.exec (fibCall n) fibEnv .stop) ch
      = .ok (.normal σc, ch') := hrun
  obtain ⟨outF, hrunF, hout⟩ := Frame.execStmtLoop_ren fuel hSF hrunL
  rw [hcfg] at hrunF
  cases outF with
  | normal σF =>
      obtain ⟨hSF', -⟩ := hout
      refine ⟨σF, ch', hrunF, ?_, ?_⟩
      · have hload := Frame.loadLoc_sim hSF' (.base ⟨0⟩)
        obtain ⟨vF, hvF, hrel⟩ := hload.ok_inv hread
        have hren0 : renameLoc (uniformShift 1 na) (.base ⟨0⟩)
            = .base ⟨0⟩ := by simp [renameLoc, uniformShift]
        rw [hren0] at hvF
        rw [hvF, hrel]
        simp [renameValue]
      · intro a c hac
        exact hSF'.frame_pres (.base ⟨a⟩) c hac
  | returned σF => exact hout.elim
  | broke σF => exact hout.elim
  | continued σF => exact hout.elim

/-! ## The harness restatement (THE HARNESS RULING, 2026-08-13 —
design note §11: the final user-facing form)

The user-facing pair `fib_ok`/`fib_total` states the three-phase Go
harness `fib_harness` (setup: empty; the call under test:
`r := fib(n)`; test: identity — the result IS the returned value)
through the machine's NATIVE function entry `runFunctionWithContextM`:
empty-heap state, arguments quantified at the call boundary,
termination + returned values observed, nothing else. No
cell/seed/env vocabulary appears in the statements (§11 ruling (2):
memory analysis happens IN GO, inside the verified footprint); the
implicit framing property is inherent in the empty-heap entry (§11
ruling (3)).

Proof route (the §5c segment technique, one call frame deeper):

* **the entry equation** (`fibH_entry_eq`) equates the machine entry
  to its post-prelude `runConfig` form by `with_unfolding_all rfl` —
  the prelude (size check, `bindParams`, `allocDecls`,
  `pinResultLocs`) is fuel-independent and definitional on the
  concrete-shape argument array;
* the canonical segments re-derive by `with_unfolding_all rfl` at the
  harness address layout (params from 0: `n`=0, `$res0`=1, `r`=2;
  fib's callee frame at 3–8 — the old seeded layout shifted by +2);
* one strong induction on the remaining measure `n - m` pins the
  exact terminal state, value included (value + completion from the
  same segments — no WP walk anywhere in the harness derivation);
* `runConfig_of_stepFnIter` + `runConfig_next_stop` fold the run, and
  the `loadMany` readback computes definitionally on the pinned
  terminal state. -/

/-- The harness `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def fibHarnessFunc : Func :=
  { id := { key := "fib_harness" },
    args := #[{ id := "n", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "r", typ := .int .uint64 },
            .call #[.var "r"] ⟨"fib"⟩ #[.var "n"]],
        .seqn
          #[.assign (.var "$res0") (.var "r"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
example : findFunctionIn? fibLowered.funcs ⟨"fib_harness"⟩
    = some fibHarnessFunc := rfl

/-- The machine entry's post-prelude state: exactly the two frame
cells the prelude allocates from the EMPTY heap — the `n` argument at
address 0 (normalized at its declared type), the `$res0` result cell
at 1. -/
private def fibHSeed (nv : Int) : ExecState :=
  { types := fibLowered.typeDefs.toList, functions := fibLowered.funcs,
    methods := fibLowered.methods,
    heap := [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell 0)],
    nextAddr := 2 }

/-- The post-prelude configuration: the harness body inside the
entry's barrier frame. -/
private def fibHC₀ : Config :=
  .exec fibHarnessFunc.body [[("$res0", .base ⟨1⟩), ("n", .base ⟨0⟩)]]
    (.frame [] [] [] [] .stop)

/-- **The entry equation** (the §11 glue, fib instance): the machine
entry IS its post-prelude `runConfig` form — the prelude is
fuel-independent and definitional on the concrete-shape argument
array, so the equation is a pure `with_unfolding_all rfl` at fully
symbolic `n`, `fuel` and `ch`. -/
private theorem fibH_entry_eq (n : Nat) (fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel fibLowered.typeDefs.toList
        fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
        fibLowered.methods ch
      = (do
          let (sF, _) ← runConfig fuel
            (fibHSeed (IntKind.normalize .uint64 (n : Int))) fibHC₀ ch
          return { values := (← loadMany sF [Loc.base ⟨1⟩]).toArray }) := by
  with_unfolding_all rfl

/-! ### The harness-layout machine configurations (probe-verified;
every raw segment below re-checks the transcription by `rfl`). -/

private def fibHRetEnv : LocalEnv :=
  [[("r", .base ⟨2⟩)], [("$res0", .base ⟨1⟩), ("n", .base ⟨0⟩)]]

private def fibHLoopEnv : LocalEnv :=
  [[("$forFirst", .base ⟨8⟩)], [("i", .base ⟨7⟩)],
   [("b", .base ⟨6⟩), ("a", .base ⟨5⟩)],
   [("$res0", .base ⟨4⟩), ("n", .base ⟨3⟩)]]

/-- The loop-head continuation: fib's scope drains and trailing
`$res0 = a; return`, fib's frame (targeting the harness local `r`),
then the harness's own `$res0 = r; return` inside the entry barrier. -/
private def fibHHeadCont : Cont :=
  .seq [] fibHLoopEnv
    (.seq [] [[("i", .base ⟨7⟩)], [("b", .base ⟨6⟩), ("a", .base ⟨5⟩)],
              [("$res0", .base ⟨4⟩), ("n", .base ⟨3⟩)]]
      (.seq [.seqn #[.assign (.var "$res0") (.var "a"), .returnStmt]]
        [[("b", .base ⟨6⟩), ("a", .base ⟨5⟩)],
         [("$res0", .base ⟨4⟩), ("n", .base ⟨3⟩)]]
        (.frame [(.chain [], [.ref "r"])] fibHRetEnv [.base ⟨4⟩] []
          (.seq [.seqn #[.assign (.var "$res0") (.var "r"), .returnStmt]]
            fibHRetEnv (.frame [] [] [] [] .stop)))))

/-- The loop-head configuration. -/
private def fibHHeadConfig : Config :=
  .exec (.while (.boolLit true) fibWhileBody) fibHLoopEnv fibHHeadCont

/-- The exit test's delivery continuation (segment split point). -/
private def fibHCmpCont : Cont :=
  .ifK (.seqn #[]) .breakStmt fibHLoopEnv.pushScope
    (.seq [fibIterBlock] fibHLoopEnv.pushScope
      (.loop (.boolLit true) fibWhileBody fibHLoopEnv fibHHeadCont))

/-- The in-loop heap at the harness layout: harness cells 0–2 (the
`n` argument, the still-zero `$res0`, the still-zero `r`), fib's
frame cells 3–8. -/
private def fibHHeap (nv av bv iv : Int) (ffv : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell 0),
   (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, u64cell nv),
   (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, u64cell av),
   (.base ⟨6⟩, u64cell bv), (.base ⟨7⟩, u64cell iv),
   (.base ⟨8⟩, boolcell ffv)]

private def fibHState (h : Heap) : ExecState :=
  { types := fibLowered.typeDefs.toList, functions := fibLowered.funcs,
    methods := fibLowered.methods, heap := h, nextAddr := 9 }

/-- The loop-head state after `m` completed iterations (the seeded
`fibHeadState`, shifted to the harness layout). -/
private def fibHHeadState (n m : Nat) : ExecState :=
  fibHState (fibHHeap (n : Int) (fibv m) (fibv (m + 1))
    ((m - 1 : Nat) : Int) (m == 0))

/-- The state at the exit test: flag down, counter caught up to `m`. -/
private def fibHCmpState (n m : Nat) : ExecState :=
  fibHState (fibHHeap (n : Int) (fibv m) (fibv (m + 1))
    ((m : Nat) : Int) false)

/-- The terminal state: `fibv n` delivered through fib's `$res0` (4),
the harness local `r` (2) and the harness result cell (1). -/
private def fibHEndState (n : Nat) : ExecState :=
  fibHState
    [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell (fibv n)),
     (.base ⟨2⟩, u64cell (fibv n)), (.base ⟨3⟩, u64cell (n : Int)),
     (.base ⟨4⟩, u64cell (fibv n)), (.base ⟨5⟩, u64cell (fibv n)),
     (.base ⟨6⟩, u64cell (fibv (n + 1))), (.base ⟨7⟩, u64cell (n : Int)),
     (.base ⟨8⟩, boolcell false)]

/-! ### Raw run segments (`with_unfolding_all rfl` at the harness
layout; same split points as the seeded module — the loop's exit test
is the only data-dependent branch). -/

private theorem fibH_entry_raw (n : Nat) (ch : Choices) :
    stepFnIter 63 (fibHSeed (n : Int)) fibHC₀ ch
      = .ok (fibHHeadConfig,
          fibHState
            [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell 0),
             (.base ⟨2⟩, u64cell 0),
             (.base ⟨3⟩, u64cell (IntKind.normalize .uint64 (n : Int))),
             (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, u64cell 0),
             (.base ⟨6⟩, u64cell 1), (.base ⟨7⟩, u64cell 0),
             (.base ⟨8⟩, boolcell true)], ch) := by
  with_unfolding_all rfl

/-- Entry, cleaned: post-prelude state → the loop head at `m = 0`
within 63 steps (the harness prologue `r := 0`, the call's frame
entry, fib's declarations). -/
private theorem fibH_entry (n : Nat) (hn : n < 2 ^ 64) (ch : Choices) :
    stepFnIter 63 (fibHSeed (n : Int)) fibHC₀ ch
      = .ok (fibHHeadConfig, fibHHeadState n 0, ch) := by
  rw [fibH_entry_raw, unorm_nat_of_lt hn]
  rfl

/-- First-pass dispatch: head at `m = 0` → the exit test. -/
private theorem fibH_segA0 (n : Nat) (ch : Choices) :
    stepFnIter 25 (fibHHeadState n 0) fibHHeadConfig ch
      = .ok (.retV (.bool (decide ((0 : Int) < (n : Int)))) fibHCmpCont,
          fibHCmpState n 0, ch) := by
  with_unfolding_all rfl

private theorem fibH_segA1_raw (n m : Nat) (ch : Choices) :
    stepFnIter 29 (fibHHeadState n (m + 1)) fibHHeadConfig ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 ((m : Int) + 1))
              < (n : Int)))) fibHCmpCont,
          fibHState (fibHHeap (n : Int) (fibv (m + 1)) (fibv (m + 2))
            (IntKind.normalize .uint64
              (IntKind.normalize .uint64 ((m : Int) + 1))) false), ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch, cleaned: head at `m + 1` → the exit test. -/
private theorem fibH_segA1 (n m : Nat) (hm : m + 1 < 2 ^ 64) (ch : Choices) :
    stepFnIter 29 (fibHHeadState n (m + 1)) fibHHeadConfig ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int) < (n : Int))))
            fibHCmpCont,
          fibHCmpState n (m + 1), ch) := by
  rw [fibH_segA1_raw,
    show ((m : Int) + 1) = ((m + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt hm, unorm_nat_of_lt hm]
  rfl

private theorem fibH_segBC_raw (n m : Nat) (ch : Choices) :
    stepFnIter 27 (fibHCmpState n m) (.retV (.bool true) fibHCmpCont) ch
      = .ok (fibHHeadConfig,
          fibHState (fibHHeap (n : Int)
            (IntKind.normalize .uint64 (fibv (m + 1)))
            (IntKind.normalize .uint64 (IntKind.normalize .uint64
              (fibv m + fibv (m + 1))))
            ((m : Nat) : Int) false), ch) := by
  with_unfolding_all rfl

/-- Continue segment, cleaned: exit test true → head at `m + 1`. -/
private theorem fibH_segBC (n m : Nat) (ch : Choices) :
    stepFnIter 27 (fibHCmpState n m) (.retV (.bool true) fibHCmpCont) ch
      = .ok (fibHHeadConfig, fibHHeadState n (m + 1), ch) := by
  rw [fibH_segBC_raw, unorm_fibv_add, unorm_fibv, unorm_fibv,
    show fibHHeadState n (m + 1)
        = fibHState (fibHHeap (n : Int) (fibv (m + 1)) (fibv (m + 2))
            ((m : Nat) : Int) false) from by
      simp only [fibHHeadState, show (m + 1 - 1 : Nat) = m from by omega,
        show (((m + 1 : Nat) == 0) : Bool) = false from by simp]]

private theorem fibH_segBE_raw (n m : Nat) (ch : Choices) :
    stepFnIter 41 (fibHCmpState n m) (.retV (.bool false) fibHCmpCont) ch
      = .ok (.next .stop,
          fibHState
            [(.base ⟨0⟩, u64cell (n : Int)),
             (.base ⟨1⟩, u64cell (IntKind.normalize .uint64
               (IntKind.normalize .uint64 (IntKind.normalize .uint64
                 (fibv m))))),
             (.base ⟨2⟩, u64cell (IntKind.normalize .uint64
               (IntKind.normalize .uint64 (fibv m)))),
             (.base ⟨3⟩, u64cell (n : Int)),
             (.base ⟨4⟩, u64cell (IntKind.normalize .uint64 (fibv m))),
             (.base ⟨5⟩, u64cell (fibv m)),
             (.base ⟨6⟩, u64cell (fibv (m + 1))),
             (.base ⟨7⟩, u64cell ((m : Nat) : Int)),
             (.base ⟨8⟩, boolcell false)], ch) := by
  with_unfolding_all rfl

/-- Exit segment, cleaned at `m = n`: break, fib's `$res0 = a` and
`return`, fib's frame exit into `r`, the harness's `$res0 = r` and
`return`, the barrier exit — the driver terminal, terminal state
pinned. -/
private theorem fibH_segBE (n : Nat) (ch : Choices) :
    stepFnIter 41 (fibHCmpState n n) (.retV (.bool false) fibHCmpCont) ch
      = .ok (.next .stop, fibHEndState n, ch) := by
  rw [fibH_segBE_raw, unorm_fibv, unorm_fibv, unorm_fibv]
  rfl

/-! ### The loop induction (value + completion from one strong
induction on the remaining measure `n - m`) -/

/-- **The loop**: from the exit-test delivery of iteration `m`, the
run reaches the driver terminal — with the exact terminal state
pinned — within `56·μ + 41` steps, `μ = n - m` the remaining
measure. -/
private theorem fibH_loop (n : Nat) (hn : n < 2 ^ 64) :
    ∀ μ m : Nat, m + μ = n →
    ∀ ch : Choices, ∃ k : Nat, k ≤ 56 * μ + 41 ∧
      stepFnIter k (fibHCmpState n m)
        (.retV (.bool (decide ((m : Int) < (n : Int)))) fibHCmpCont) ch
        = .ok (.next .stop, fibHEndState n, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hm ch
    rcases Nat.lt_or_ge m n with hlt | hge
    · -- iterate: one pair update + the next dispatch, then recurse
      rw [show (decide ((m : Int) < (n : Int))) = true from
        decide_eq_true (Int.ofNat_lt.mpr hlt)]
      obtain ⟨k, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1) (by omega) ch
      refine ⟨27 + 29 + k, by omega, ?_⟩
      exact stepFnIter_chain
        (stepFnIter_chain (fibH_segBC n m ch)
          (fibH_segA1 n m (by omega) ch)) hrun
    · -- exit: m = n
      have hmn : m = n := by omega
      subst hmn
      rw [show (decide ((m : Int) < (m : Int))) = false from
        decide_eq_false (by omega)]
      exact ⟨41, by omega, fibH_segBE m ch⟩

/-- **The canonical run, end to end**: from the post-prelude state the
harness completes at the driver terminal within `129 + 56·n` steps,
terminal state pinned. -/
private theorem fibH_runs (n : Nat) (hn : n < 2 ^ 64) (ch : Choices) :
    ∃ k : Nat, k ≤ 129 + 56 * n ∧
      stepFnIter k (fibHSeed (n : Int)) fibHC₀ ch
        = .ok (.next .stop, fibHEndState n, ch) := by
  have hE := fibH_entry n hn ch
  have hA0 := fibH_segA0 n ch
  obtain ⟨k, hk, hrun⟩ := fibH_loop n hn n 0 (by omega) ch
  rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hrun
  exact ⟨63 + 25 + k, by omega,
    stepFnIter_chain (stepFnIter_chain hE hA0) hrun⟩

/-! ### The user-facing statements (§11) -/

/-- **FULL-DOMAIN TOTAL CORRECTNESS, harness form (§11)**: for EVERY
value `n` of the Go argument type `uint64`, running the three-phase Go
harness `fib_harness(n)` through the machine's native function entry —
empty-heap state, `n` at the call boundary — completes normally past
one fuel bound, at every nondeterminism-choice stream, and RETURNS
exactly `fibSpec n % 2^64`: what Go's wrapping uint64 arithmetic
computes, on the whole domain, past the overflow boundary at
`n = 94`. Termination + returned values are the only observables; the
implicit framing property is inherent in the empty-heap entry. -/
theorem fib_total (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } := by
  refine ⟨129 + 56 * n, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, hk, hrun⟩ := fibH_runs n hn ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [fibH_entry_eq, unorm_nat_of_lt hn, hfold, runConfig_next_stop]
  with_unfolding_all rfl

/-- **THE HEADLINE (§11 harness form)**: for every `n ≤ 93` — the
largest argument whose Fibonacci number fits in uint64 —
`fib_harness(n)` (setup: empty; call under test: `r := fib(n)`; test:
identity) completes normally — no panic, no stuck state, no error;
past one fuel bound, at every nondeterminism-choice stream — and
RETURNS exactly `fibSpec n`.

Total correctness read at the machine's own function-entry boundary:
quantification is over instantiated `GoValue` arguments (the machine's
native mechanism — no AST splicing, no program families); the
statement observes termination + returned values only, with no heap
readback and no frame clause (the empty-heap entry makes the framing
property implicit). -/
theorem fib_ok (n : Nat) (hn : n ≤ 93) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok { values := #[.int (fibSpec n) .uint64] } := by
  have hn64 : n < 2 ^ 64 := by
    have : (93 : Nat) < 2 ^ 64 := by decide
    omega
  have hfib : fibSpec n < 2 ^ 64 := fibSpec_lt_of_le_93 hn
  have hmod : ((fibSpec n % 2 ^ 64 : Nat) : Int) = ((fibSpec n : Nat) : Int) := by
    rw [Nat.mod_eq_of_lt hfib]
  obtain ⟨N, hN⟩ := fib_total n hn64
  refine ⟨N, fun fuel hfuel ch => ?_⟩
  rw [hN fuel hfuel ch, hmod]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry, at any fuel and any choice stream, returns exactly
`fibSpec n % 2^64` — derived from `fib_total` via
`harness_readout_of_total` (the total headline already determines
every completion; nothing is re-proven). -/
theorem fib_readout (n : Nat) (hn : n < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok r →
      r = { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } :=
  harness_readout_of_total (fib_total n hn)

end GoLean.Examples.Fib

