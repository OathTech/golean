import Lean

/-!
# `stmt_of%` — a kept theorem's statement, as the kernel holds it (the comparator contract)

[AGENT lane gate/comparator-1023] 2026-10-23, release-readiness row 43 ([USER]-ruled 2026-10-23).

`lake comparator` judges a SOLUTION module against a CHALLENGE module by SYNTACTIC equality of
each named theorem's type (`Lake/Check/Compare.lean`, `compareAt`: the two `ConstantVal`s must be
`==`), so the solution side must present every kept theorem under the challenge's name with the
kept theorem's OWN type — not a hand copy that is merely definitionally equal. `stmt_of% c` is
that type: the elaborated type of the constant `c`, read from the environment. The one
normalisation: the `Prefix`/`Finish` laws of `GoLean/GoCore/Prefix.lean` are stated as
`theorem <name> : <name>_stmt` over a `def <name>_stmt : Prop` (`ExecutionStatement.lean`), and a
challenge that named `<name>_stmt` would pin nothing (both exports would read the same
definition); so a type that IS a constant whose name ends in `_stmt` is replaced by that
definition's value — the spelled-out proposition — and the challenge spells it out too.

Used only by the generated `GoLean/Contract/Solution.lean`. A theorem with universe parameters is
refused by name (none of the kept surface has one; the alias form would need level binders).
-/

namespace GoLean.Contract

open Lean Elab Term Meta

/-- The type of the theorem `c` as the environment holds it; a type that is a bare constant
named `*_stmt` is replaced by that definition's value (`ExecutionStatement.lean`'s
statement-as-definition idiom). -/
elab "stmt_of% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo n
  unless info.levelParams.isEmpty do
    throwError "stmt_of%: {n} has universe parameters {info.levelParams}; the alias form has none"
  unless info matches .thmInfo _ do
    throwError "stmt_of%: {n} is not a theorem"
  let ty := info.type
  if let .const h _ := ty then
    if h.toString.endsWith "_stmt" then
      let some v := (← getConstInfo h).value? |
        throwError "stmt_of%: the statement constant {h} has no value to unfold"
      return v
  return ty

end GoLean.Contract
