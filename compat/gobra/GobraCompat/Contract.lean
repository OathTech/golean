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

Two ADEQUACY DIVERGENCES are deliberately surfaced (not hidden) by this
fragment, both discovered on the very first example:
1. **Unbounded vs machine ints**: Gobra's default `int` is mathematical
   (overflow checking is opt-in via `--overflow`); GoCore's is machine
   width. `contractStatement` therefore takes an explicit
   `adequacyGuard` confining the quantifier to the range where the two
   agree — the guard is spec content, visible in the statement.
2. **Division convention**: Go truncates toward zero; Viper's `div` is
   SMT-LIB-style. This fragment fixes Go's semantics (`Int.tdiv`,
   matching GoCore); a full pipeline must reconcile per construct.
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
deriving Repr

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
deriving Repr

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
deriving Repr

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

/-- **The elaboration** (v1 fragment: unary `int → int` functions,
matching `GoFuncSpec`'s v1 shape): the Gobra contract of `fid` means —
for every argument in the adequacy-guarded range satisfying `requires`,
calling `fid(n)` from any admissible heap, with any frame, terminates
only in states whose result satisfies `ensures`. Pre/post are pure, so
they enter through `GoFuncSpec`'s `P`/`Q` slots as `HProp.pure`. -/
def contractStatement (types : TypeEnv) (funcs : Array Func)
    (methods : Array MethodInfo) (fid : FuncId) (kind : IntKind)
    (argName resName : String) (ct : GobraContract)
    (adequacyGuard : Int → Prop) : Prop :=
  ∀ n : Int, adequacyGuard n →
    preHolds ct (env1 argName n) →
    GoFuncSpec types funcs methods fid kind #[.intLit n kind]
      (.pure True)
      (fun r => .pure (postHolds ct (envRes (env1 argName n) resName r)))

end GobraCompat
