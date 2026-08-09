import GoLeanProofs.Surface

/-!
# A Gobra contract fragment, given meaning over GoCore (spike)

A deep embedding of the smallest useful fragment of Gobra's assertion
language — integer expressions and boolean assertions over function
parameters and named results — with its meaning defined ONCE, in Lean,
over golean's semantics (the prior-art lesson from HOL-Boogie/Why3:
discharging obligations in an ITP buys nothing unless the obligation's
meaning is itself defined in the ITP against a semantics of the source).

The elaboration target is the Surface layer (`GoFuncSpec`), never Iris —
per the statement-TCB doctrine, a Gobra contract compiles to the
Iris-free statement language.

ADEQUACY DIVERGENCES, deliberately surfaced rather than hidden. The list
was corrected by a pre-merge audit against Gobra's own sources — one
claimed divergence was not one, and it was masking a real one:

1. **Unbounded vs machine ints** (REAL): Gobra's default `int` is
   mathematical (`checkOverflows` defaults false,
   `deps/gobra/.../Config.scala`); GoCore's is machine width.
   `contractStatement` therefore takes an explicit `adequacyGuard`
   confining the quantifier to the range where the two agree — the guard
   is spec content, visible in the statement.
2. **Division convention** (NOT a divergence — claim retracted): Gobra
   already reconciles this. Every Go `int` division is routed through a
   custom `goIntDiv`
   (`deps/gobra/src/main/scala/viper/gobra/translator/encodings/IntEncoding.scala`),
   defined as `(0 <= l ? l \ r : -((-l) \ r))` — exact Go
   truncation-toward-zero, with an in-source comment saying Viper's
   default does not match Go. Audit-checked numerically: `go run`,
   `GExpr.eval` (`Int.tdiv`) and `goIntDiv` agree on all six sign
   combinations. So this fragment agrees with BOTH, and the earlier
   "spike surfaced two divergences on the first example" was one.
3. **Divide-by-zero well-definedness** (REAL, and the one #2 was
   masking): `goIntDiv` carries `requires r != 0`, so Gobra imposes a
   well-definedness proof obligation on every `/` in a contract.
   `GExpr.eval` instead gives `Int.tdiv x 0 = 0` silently, so a contract
   Gobra REJECTS as ill-defined becomes a quietly-false assertion here —
   another route into the vacuity `GobraContract.scopedBy` closes for
   names. NOT yet fixed: `GExpr.eval` should fail closed on a zero
   divisor (an `Option`/`Except` result), which is a real reshape of the
   evaluator and its `Decidable` instances.
-/

namespace GobraCompat

open GoLean GoLean.GoCore GoLean.Surface

/-- Environments give integer values to contract names (parameters and
named results). -/
def GEnv := String → Int

/-- Integer expressions of the fragment. -/
inductive GExpr where
  | lit (v : Int)
  | evar (name : String)
  | add (a b : GExpr)
  | sub (a b : GExpr)
  | mul (a b : GExpr)
  | div (a b : GExpr)
deriving Repr, DecidableEq

/-- Go semantics for `/` (truncation toward zero), matching GoCore. -/
def GExpr.eval (env : GEnv) : GExpr → Int
  | .lit v => v
  | .evar n => env n
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .div a b => Int.tdiv (a.eval env) (b.eval env)

/-- Boolean assertions of the fragment (heap-free: no `acc`, no
predicates — those are the recorded stage-2/3 constructs, mapping to
`HProp.pointsTo`/named `HProp`s respectively). -/
inductive GAssertion where
  | le (a b : GExpr)
  | lt (a b : GExpr)
  | eq (a b : GExpr)
  | conj (p q : GAssertion)
  | impl (p q : GAssertion)
deriving Repr, DecidableEq

/-- The names a `GExpr` reads. -/
def GExpr.vars : GExpr → List String
  | .lit _ => []
  | .evar n => [n]
  | .add a b | .sub a b | .mul a b | .div a b => a.vars ++ b.vars

/-- The names a `GAssertion` reads. -/
def GAssertion.vars : GAssertion → List String
  | .le a b | .lt a b | .eq a b => a.vars ++ b.vars
  | .conj p q | .impl p q => p.vars ++ q.vars

/-- Every name the contract reads, across all clauses. -/
def GobraContractVars (requires ensures loopInvariants : List GAssertion) : List String :=
  (requires ++ ensures ++ loopInvariants).flatMap GAssertion.vars

def GAssertion.holds (env : GEnv) : GAssertion → Prop
  | .le a b => a.eval env ≤ b.eval env
  | .lt a b => a.eval env < b.eval env
  | .eq a b => a.eval env = b.eval env
  | .conj p q => p.holds env ∧ q.holds env
  | .impl p q => p.holds env → q.holds env

def GAssertion.decideHolds (env : GEnv) : (a : GAssertion) → Decidable (a.holds env)
  | .le a b => inferInstanceAs (Decidable (a.eval env ≤ b.eval env))
  | .lt a b => inferInstanceAs (Decidable (a.eval env < b.eval env))
  | .eq a b => inferInstanceAs (Decidable (a.eval env = b.eval env))
  | .conj p q => @instDecidableAnd _ _ (p.decideHolds env) (q.decideHolds env)
  | .impl p q =>
    match p.decideHolds env, q.decideHolds env with
    | _, .isTrue hq => .isTrue fun _ => hq
    | .isFalse hp, _ => .isTrue fun h => absurd h hp
    | .isTrue hp, .isFalse hq => .isFalse fun h => hq (h hp)

instance (env : GEnv) (a : GAssertion) : Decidable (a.holds env) :=
  a.decideHolds env

/-- A function contract in the fragment: the `requires`/`ensures`
clauses plus whether `decreases` (a termination claim) is present. Loop
invariants ride along for the proof phase — they are exactly the input
`go_walk`'s `wp_while_inv` needs a human (or an annotation) to supply. -/
structure GobraContract where
  requires : List GAssertion
  ensures : List GAssertion
  loopInvariants : List GAssertion
  terminates : Bool
deriving Repr, DecidableEq

/-- The names the contract's STATEMENT content reads — `requires` and
`ensures` only.

`loopInvariants` are deliberately excluded: they are proof inputs, and
they legitimately mention loop-LOCAL variables (`sum`'s invariants speak
about `i`, which is neither a parameter nor a result). Scoping them
against `{argName, resName}` would reject the flagship example — caught
by checking the fix rather than the bug: the first version of this
returned `false` for `sumContract` itself. Their scope is the loop's
local environment, which this fragment does not model; nothing checks
them today, and that is an open gap, not a closed one. -/
def GobraContract.specVars (ct : GobraContract) : List String :=
  GobraContractVars ct.requires ct.ensures []

/-- The names the PRECONDITION reads. Scoped separately from `ensures`
because it is evaluated in a different environment — see `scopedFor`. -/
def GobraContract.preVars (ct : GobraContract) : List String :=
  GobraContractVars ct.requires [] []

/-- The names the POSTCONDITION reads. -/
def GobraContract.postVars (ct : GobraContract) : List String :=
  GobraContractVars [] ct.ensures []

/-- Every name this contract reads anywhere, invariants included. Not
used by the statement — see `specVars`. -/
def GobraContract.vars (ct : GobraContract) : List String :=
  GobraContractVars ct.requires ct.ensures ct.loopInvariants

/-- **The scope check** — every name the contract reads is one the
environment actually binds.

Without this, `GEnv`'s totality silently approximates: `env1` maps every
unbound name to `0`, so `requires 0 < b` for an unbound `b` becomes
`0 < 0`, the precondition is unsatisfiable, and the elaborated contract
statement is provable BY ABSURDITY without ever mentioning the program.
That is not hypothetical — a pre-merge audit proved exactly that theorem
in three tactic lines for an ordinary two-argument contract, and reached
it again through `nil` (an identifier, silently worth 0) and through a
division by an unbound name. Any of a second parameter, a typo, or a
non-integer identifier triggers it.

`contractStatement` therefore carries this as a CONJUNCT, not a premise:
out of scope makes the statement FALSE (unprovable), never vacuously
true.

**THE SCOPES DIFFER PER CLAUSE KIND, and getting that wrong left the hole
open once already.** `requires` is evaluated in `env1 argName n`, which
binds ONLY the parameter; `ensures` in `envRes … resName r`, which binds
both. A first version of this check whitelisted `[argName, resName]`
uniformly, so `requires 0 < sum` — the RESULT named in a precondition —
passed the gate and was still read as `0 < 0`. A delta-review discharged
`ensures 0 == 1` under exactly that contract, sorry-free, in three tactic
lines with the gate green. Hence two checks, not one. -/
def GobraContract.scopedFor (ct : GobraContract) (argName resName : String) : Bool :=
  ct.preVars.all (· == argName) &&
  ct.postVars.all (fun v => v == argName || v == resName)

def preHolds (ct : GobraContract) (env : GEnv) : Prop :=
  ∀ a ∈ ct.requires, a.holds env

def postHolds (ct : GobraContract) (env : GEnv) : Prop :=
  ∀ a ∈ ct.ensures, a.holds env

instance (ct : GobraContract) (env : GEnv) : Decidable (preHolds ct env) :=
  inferInstanceAs (Decidable (∀ a ∈ ct.requires, a.holds env))

instance (ct : GobraContract) (env : GEnv) : Decidable (postHolds ct env) :=
  inferInstanceAs (Decidable (∀ a ∈ ct.ensures, a.holds env))

/-- The single-parameter environment. -/
def env1 (argName : String) (n : Int) : GEnv := fun x => if x = argName then n else 0

/-- Extend an environment with the named result. -/
def envRes (env : GEnv) (resName : String) (r : Int) : GEnv :=
  fun x => if x = resName then r else env x

/-- The TOTAL analogue of `GoFuncSpec` — identical but for `GoSpecT`,
which adds `Terminates` from every admissible initial state.

LAYERING NOTE: this is general infrastructure (the missing dual of
`GoFuncSpec`) living temporarily in a target-specific package, to keep
`compat/`'s isolation contract intact — nothing in the root build
references `compat/`, and a spike should not push definitions into
`proofs/`. If the Gobra lane matures past a spike this belongs beside
`GoFuncSpec` in `GoLeanProofs.Surface`, and the duplication is a
coordination-point slice, not a permanent home. -/
def GoFuncSpecT (types : TypeEnv) (funcs : Array Func)
    (methods : Array MethodInfo) (fid : FuncId)
    (kind : IntKind) (args : Array Expr) (P : HProp) (Q : Int → HProp) : Prop :=
  ∀ (ra : Nat) (w : GoValue),
    GoSpecT types funcs methods [[("$callres", Loc.base ⟨ra⟩)]]
      (.sep (.pointsTo ra ⟨some (.int kind), w⟩) P)
      (.call #[.var "$callres"] fid args)
      (.ex fun (n : Int) =>
        .sep (.pointsTo ra ⟨some (.int kind), .int n kind⟩) (Q n))

/-- `GoFuncSpecT` is a HAND-WRITTEN dual of `Surface.GoFuncSpec`, so
nothing keeps the two in sync if `proofs/` moves. This pins the direction
that matters: the total judgment really is a STRENGTHENING, not a
differently-shaped statement that merely resembles one (delta-review F6,
which verified the shape but noted nothing held it). If
`Surface.GoFuncSpec` or `GoSpecT` changes shape, this stops compiling. -/
theorem goFuncSpecT_imp_goFuncSpec {types : TypeEnv} {funcs : Array Func}
    {methods : Array MethodInfo} {fid : FuncId} {kind : IntKind}
    {args : Array Expr} {P : HProp} {Q : Int → HProp} :
    GoFuncSpecT types funcs methods fid kind args P Q →
    GoFuncSpec types funcs methods fid kind args P Q := by
  intro h ra w; exact ⟨(h ra w).1, (h ra w).2.1⟩

/-- **The elaboration** (v1 fragment: unary `int → int` functions,
matching `GoFuncSpec`'s v1 shape): the Gobra contract of `fid` means —
every name the contract reads is in scope, AND for every argument in the
adequacy-guarded range satisfying `requires`, calling `fid(n)` from any
admissible heap, with any frame, ends only in states whose result
satisfies `ensures`. Pre/post are pure, so they enter through the `P`/`Q`
slots as `HProp.pure`.

TWO THINGS THIS DELIBERATELY GETS RIGHT, both from the pre-merge audit:

**Scope is a conjunct, not a premise** (`scopedFor`), and it is checked
PER CLAUSE KIND — `requires` against the parameter alone, `ensures`
against parameter and result — because those are the environments they
are evaluated in. A contract reading anything else makes this statement
FALSE. As a premise it would have made it vacuously TRUE, which is the
bug being fixed — see `GobraContract.scopedFor`, including the
uniform-whitelist version that left half the hole open.

**`decreases` is honoured, not dropped**: when `ct.terminates` the
elaboration is `GoFuncSpecT` (triple + safety + termination). In Gobra
`decreases` is what upgrades partial correctness to total
(`deps/gobra/docs/tutorial.md`). Previously `terminates` was parsed,
round-trip-checked and then never read, so a contract with `decreases`
deleted elaborated to a definitionally EQUAL Prop — the audit demonstrated
that with `rfl`. Discharging the old statement would not have discharged
the contract, which is the dangerous direction.

CAVEAT, precise rather than flattering (delta-review F2): `parseContract`
folds EVERY `decreases` clause — function-level and loop-level alike —
into the one `terminates` flag, discarding the measure, because a flat
list of clause texts carries no nesting. So a function with no
function-level `decreases` but a measured LOOP elaborates to the total
judgment too. That was inert before this change and is load-bearing now.
It errs OVER-strong (proving more discharges the contract; it cannot
under-claim), which is why it is a caveat and not a defect — but the
mapping is not clause-by-clause, and fixing it needs a clause structure
that records nesting. `sum` itself is unaffected: it carries a
function-level `decreases`.

`loopInvariants` are deliberately NOT statement content: they are proof
INPUTS (the invariant `go_walk`'s `wp_while_inv` needs), not part of what
the contract means, and they range over loop-LOCAL names this fragment
does not model. Nothing checks their scope — see `specVars`. -/
def contractStatement (types : TypeEnv) (funcs : Array Func)
    (methods : Array MethodInfo) (fid : FuncId) (kind : IntKind)
    (argName resName : String) (ct : GobraContract)
    (adequacyGuard : Int → Prop) : Prop :=
  ct.scopedFor argName resName = true ∧
  ∀ n : Int, adequacyGuard n →
    preHolds ct (env1 argName n) →
    (if ct.terminates then GoFuncSpecT else GoFuncSpec)
      types funcs methods fid kind #[.intLit n kind]
      (.pure True)
      (fun r => .pure (postHolds ct (envRes (env1 argName n) resName r)))

end GobraCompat
