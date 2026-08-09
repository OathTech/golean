import GobraCompat.Parser

/-!
# Parser tests

`#guard` rather than `by decide +kernel`: these run in the evaluator, so they
are cheap, they fail this package's `lake build` if they regress, and they add
no axiom to anything. Note the honest scope of that: **no repo gate builds
`compat/`** — not `scripts/ci`, not the workflow (the isolation contract cuts
both ways), so these run only when a human builds this package. The kernel-checked claim stays where it
earns its keep — `Sum.lean`'s round trip, which proves the transcribed contract
IS the parse of the verbatim annotation text.

Written after the parser shipped with a single round-trip test and a fuel bug
that made that test FALSE (`requires 0 <= n` → "out of fuel"), which no test
could catch because the round trip was the only test and it was never evaluated.
The first section below is that exact regression. Every case here is one the
suite previously could not see.
-/

namespace GobraCompat
namespace ParserTest

open GobraCompat.Parser

private def parsesTo (s : String) (c : SpecClause) : Bool :=
  match parseClause s with
  | .ok c' => c' == c
  | .error _ => false

private def rejects (s : String) : Bool :=
  match parseClause s with
  | .ok _ => false
  | .error _ => true

/-! ## Regression: the fuel bug (shortest clause of each kind)

The bound must not scale with token count alone. Each of these is at or near
the minimum token count for its form — exactly where the old `|toks| + 1`
died. -/

#guard parsesTo "requires 0 <= n" (.requiresC (.le (.lit 0) (.evar "n")))
#guard parsesTo "ensures 0 <= n"  (.ensuresC (.le (.lit 0) (.evar "n")))
#guard parsesTo "invariant 0 < n" (.invariantC (.lt (.lit 0) (.evar "n")))
#guard parsesTo "requires n == n" (.requiresC (.eq (.evar "n") (.evar "n")))
#guard parsesTo "decreases" (.decreasesC none)
#guard parsesTo "decreases n" (.decreasesC (some (.evar "n")))

/-! ## The six clauses of `testdata/sum/main.go`, individually

`Sum.lean`'s round trip checks these as a set; here they are pinned one at a
time, so a regression names the clause that broke. -/

#guard parsesTo "ensures  sum == n * (n+1) / 2"
  (.ensuresC (.eq (.evar "sum")
    (.div (.mul (.evar "n") (.add (.evar "n") (.lit 1))) (.lit 2))))
#guard parsesTo "invariant 0 <= i && i <= n + 1"
  (.invariantC (.conj (.le (.lit 0) (.evar "i"))
                      (.le (.evar "i") (.add (.evar "n") (.lit 1)))))
#guard parsesTo "invariant sum == i * (i-1) / 2"
  (.invariantC (.eq (.evar "sum")
    (.div (.mul (.evar "i") (.sub (.evar "i") (.lit 1))) (.lit 2))))
#guard parsesTo "decreases n - i" (.decreasesC (some (.sub (.evar "n") (.evar "i"))))

/-! ## Precedence and associativity

Nothing pinned these before: a parser that got them backwards would still
round-trip if the transcription were wrong in the same direction. -/

-- `*` binds tighter than `+`
#guard parsesTo "requires 1 + 2 * 3 <= n"
  (.requiresC (.le (.add (.lit 1) (.mul (.lit 2) (.lit 3))) (.evar "n")))
-- `/` binds tighter than `-`
#guard parsesTo "requires 1 - 6 / 3 <= n"
  (.requiresC (.le (.sub (.lit 1) (.div (.lit 6) (.lit 3))) (.evar "n")))
-- `-` is LEFT-associative: (n - i) - 1, not n - (i - 1)
#guard parsesTo "requires n - i - 1 <= n"
  (.requiresC (.le (.sub (.sub (.evar "n") (.evar "i")) (.lit 1)) (.evar "n")))
-- `/` is LEFT-associative: (n / i) / 2
#guard parsesTo "requires n / i / 2 <= n"
  (.requiresC (.le (.div (.div (.evar "n") (.evar "i")) (.lit 2)) (.evar "n")))
-- parens override precedence
#guard parsesTo "requires (1 + 2) * 3 <= n"
  (.requiresC (.le (.mul (.add (.lit 1) (.lit 2)) (.lit 3)) (.evar "n")))
-- `==>` is RIGHT-associative: a ==> (b ==> c)
#guard parsesTo "requires 0 <= n ==> 0 < n ==> n == n"
  (.requiresC (.impl (.le (.lit 0) (.evar "n"))
    (.impl (.lt (.lit 0) (.evar "n")) (.eq (.evar "n") (.evar "n")))))
-- `&&` is RIGHT-associative, and binds tighter than `==>`
#guard parsesTo "requires 0 <= n && 0 < n && n == n"
  (.requiresC (.conj (.le (.lit 0) (.evar "n"))
    (.conj (.lt (.lit 0) (.evar "n")) (.eq (.evar "n") (.evar "n")))))
#guard parsesTo "requires 0 <= n && 0 < n ==> n == n"
  (.requiresC (.impl (.conj (.le (.lit 0) (.evar "n")) (.lt (.lit 0) (.evar "n")))
    (.eq (.evar "n") (.evar "n"))))

/-! ## Fuel stress

These are the cases that would exhaust a bound that undercounts DEPTH. Nesting
costs descents without consuming many tokens, which is precisely the shape the
original bound got wrong. -/

#guard parsesTo "requires ((((0)))) <= n" (.requiresC (.le (.lit 0) (.evar "n")))
#guard parsesTo "requires ((((((((0)))))))) <= n" (.requiresC (.le (.lit 0) (.evar "n")))
#guard parsesTo "requires 0 <= ((((((((n))))))))" (.requiresC (.le (.lit 0) (.evar "n")))
-- deep nesting on BOTH sides of the comparison at once
#guard parsesTo "requires (((0))) <= (((n)))" (.requiresC (.le (.lit 0) (.evar "n")))
-- a long chain of connectives, each re-descending from `conj`
#guard parsesTo "requires 0 < n && 0 < n && 0 < n && 0 < n && 0 < n"
  (.requiresC (.conj (.lt (.lit 0) (.evar "n"))
    (.conj (.lt (.lit 0) (.evar "n"))
      (.conj (.lt (.lit 0) (.evar "n"))
        (.conj (.lt (.lit 0) (.evar "n")) (.lt (.lit 0) (.evar "n")))))))

/-! ## Tokenizer edges -/

-- longest match: `<=` not `<` then `=`; `==>` not `==` then `>`
#guard parsesTo "requires 0 <= n" (.requiresC (.le (.lit 0) (.evar "n")))
#guard parsesTo "requires 0 < n"  (.requiresC (.lt (.lit 0) (.evar "n")))
-- multi-digit literals (digitsToNat's fold)
#guard parsesTo "requires 1234 <= n" (.requiresC (.le (.lit 1234) (.evar "n")))
#guard parsesTo "requires 0 <= 90210" (.requiresC (.le (.lit 0) (.lit 90210)))
-- identifiers with digits and underscores
#guard parsesTo "requires 0 <= n_1" (.requiresC (.le (.lit 0) (.evar "n_1")))
#guard parsesTo "requires 0 <= _x2" (.requiresC (.le (.lit 0) (.evar "_x2")))
-- whitespace insensitivity, including tabs and none at all
#guard parsesTo "requires   0   <=   n" (.requiresC (.le (.lit 0) (.evar "n")))
#guard parsesTo "requires\t0\t<=\tn" (.requiresC (.le (.lit 0) (.evar "n")))
#guard parsesTo "requires 0<=n" (.requiresC (.le (.lit 0) (.evar "n")))

/-! ## Fail-closed: malformed input must be REJECTED, never silently accepted

A parser that accepts junk would let a wrong contract round-trip. -/

#guard rejects ""                          -- empty clause
#guard rejects "requires"                  -- keyword with no assertion
#guard rejects "bogus 0 <= n"              -- unknown clause keyword
#guard rejects "0 <= n"                    -- no keyword at all
#guard rejects "requires 0 <= n extra"     -- trailing tokens
#guard rejects "requires 0 <="             -- truncated comparison
#guard rejects "requires <= n"             -- missing left operand
#guard rejects "requires 0 n"              -- missing comparison operator
#guard rejects "requires (0 <= n"          -- unbalanced open paren
#guard rejects "requires 0 <= n)"          -- unbalanced close paren
#guard rejects "requires 0 = n"            -- lone '=' (tokenizer)
#guard rejects "requires 0 & n"            -- lone '&' (tokenizer)
#guard rejects "requires 0 <= n %"         -- unexpected character
#guard rejects "requires 0 <= n &&"        -- dangling connective
#guard rejects "requires 0 <= n ==>"       -- dangling implication
#guard rejects "decreases n - "            -- dangling operator in a measure

/-! ## Unsupported Gobra constructs must fail CLOSED, and be pinned

These all behaved correctly already; nothing PINNED them, and the
limitation list omitted most of them. A pre-merge audit measured that `>`
alone accounts for 20 clauses in Gobra's regression corpus, and that the
next two functions in `sum`'s own tutorial file are unrepresentable. If
any of these ever starts parsing, it must be because someone implemented
it deliberately — not because a tokenizer change let it through with the
wrong meaning. -/

#guard rejects "requires n > 0"                    -- `>` (the commonest gap)
#guard rejects "requires n >= 0"                   -- `>=`
#guard rejects "requires n != 0"                   -- `!=`
#guard rejects "requires 0 <= n || n < 0"          -- `||`
#guard rejects "requires !(0 <= n)"                -- `!`
#guard rejects "requires 0 <= n % 2"               -- `%`
#guard rejects "requires -1 <= n"                  -- unary minus
#guard rejects "requires true"                     -- boolean literal
#guard rejects "preserves 0 <= n"                  -- `preserves` clause
#guard rejects "requires acc(x)"                   -- permissions
#guard rejects "ensures old(n) == n"               -- `old()`
#guard rejects "requires forall i int :: 0 <= i"   -- quantifiers
#guard rejects "requires isEven(n)"                -- pure-function call
#guard rejects "requires len(s) == 0"              -- `len`
#guard rejects "decreases n, i"                    -- tuple measure
#guard rejects "decreases n if 0 <= n"             -- conditional measure
-- Viper's `_` measure means "ASSUME termination" — an unsound escape
-- hatch. It must not be read as an ordinary measure named "_".
#guard rejects "decreases _"

/-! ## Scope: the vacuity guard, both directions

`requires` is evaluated in an environment binding ONLY the parameter;
`ensures` binds parameter and result. Pinning both, because a uniform
`[argName, resName]` whitelist passed `requires 0 < sum` and left the
statement provable by absurdity — a delta-review discharged
`ensures 0 == 1` under it. -/

private def ctOf (req ens : List GAssertion) : GobraContract :=
  { requires := req, ensures := ens, loopInvariants := [], terminates := true }

-- the real contract is in scope
-- the RESULT named in a PRECONDITION is out of scope (the delta-review hole)
#guard !(ctOf [.lt (.lit 0) (.evar "sum")] []).scopedFor "n" "sum"
-- the result named in a postcondition is fine
#guard (ctOf [] [.lt (.lit 0) (.evar "sum")]).scopedFor "n" "sum"
-- the parameter is in scope in both
#guard (ctOf [.lt (.lit 0) (.evar "n")] [.lt (.lit 0) (.evar "n")]).scopedFor "n" "sum"
-- an unbound second parameter is out of scope in both (the original hole)
#guard !(ctOf [.lt (.lit 0) (.evar "b")] []).scopedFor "n" "sum"
#guard !(ctOf [] [.lt (.lit 0) (.evar "b")]).scopedFor "n" "sum"
-- loop invariants are NOT scoped (they name loop-locals like `i`)
#guard ({ requires := [], ensures := [], terminates := true,
          loopInvariants := [.lt (.lit 0) (.evar "i")] } : GobraContract).scopedFor "n" "sum"

/-! ## `_` is the Viper wildcard, never a variable -/

#guard rejects "decreases (_)"        -- parenthesised
#guard rejects "decreases _ + 1"      -- inside an expression
#guard rejects "requires 0 <= _"      -- in an assertion
#guard parsesTo "decreases _x" (.decreasesC (some (.evar "_x")))  -- NOT the wildcard

/-! ## The derived bound itself -/

-- fuelFor is computed from the input, not a constant
#guard fuelFor [] == 6
#guard fuelFor [.ident "n"] == 12
#guard fuelFor [.ident "n", .le, .int 0] == 24
-- and it is strictly generous: the deepest clause above uses far less than it
-- is given, which is what makes over-supply free
#guard (match tokenize "requires ((((((((0)))))))) <= n" with
        | .ok toks => fuelFor toks > toks.length
        | .error _ => false)

end ParserTest
end GobraCompat
