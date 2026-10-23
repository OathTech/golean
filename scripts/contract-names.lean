/-
scripts/contract-names.lean — the KEPT SURFACE of the comparator contract, enumerated from the
built environment (lane gate/comparator-1023, 2026-10-23; release-readiness row 43,
[USER]-ruled 2026-10-23). Run from the checkout root, after `lake build GoLean`:

    lake env lean scripts/contract-names.lean

Prints one line per kept theorem — `KEPT<TAB><family><TAB><full name><TAB><module>` — in a
fixed family order, names sorted within a family, and nothing else on stdout. scripts/gen-contract
turns the list into `comparator.json` and `GoLean/Contract/Solution.lean`. Every family is read
from the ENVIRONMENT, not from text, so a lemma that gains or loses the `stepFn_eqns` attribute,
or a theorem added to or removed from `InitDriverFacts.lean`, changes the list (and
`scripts/gen-contract --check` then names the drift). The families, as ruled:

  prefix      `Prefix`/`Finish`'s laws kept for the customer: prefix_comp, prefix_split,
              run_ok_iff, run_panic_iff, replay_coverage (`Prefix.lean`; `replays` is a
              DEFINITION, reached by replay_coverage's statement, not a theorem — see the note in
              Contract/Challenge.lean).
  enterFrame  `enterFrame_declared` (`Machine.lean`).
  consumeAt   every theorem `…Choices.consumeAt*` — the `consumeAt_*` and `consumeAtE_*` laws of
              `State.lean` and `Machine.lean` (the customer's G9 list names both spellings).
  eqns        every lemma carrying `@[stepFn_eqns]` — the simp set's own member list
              (`EquationsAttr.lean`, `Equations.lean`).
  g11         every public theorem of `GoLean/GoCore/InitDriverFacts.lean` (the G11 family:
              `runInitConfig_*`, `runPkgInitM_*`, `prefix_det`/`prefix_det_le`, the
              `*_of_prefix_silent` converses, the one-step helpers), minus the toolchain's
              realized equation lemmas (`*.eq_N`, `*.eq_def`) that happen to be minted there.
  pool        the output-fold bridge: execProgLoopOut_snd (`Multi.lean`), execProgLoopOut_single,
              execProgLoopOut_single_prefix, seqOut_of_prefix (`PoolProjection.lean`),
              execProgLoopOut_eq_execProgLoop, execProgLoopOut_acc (`PoolFacts.lean`).

Fails closed (a Lean error, exit 1) when a named theorem is missing, is not a theorem, carries
universe parameters, lies outside the `GoLean` namespace, or when a family is empty.
-/
import GoLean
import Lean

namespace ContractNames
open Lean

/-- The toolchain's realized names (`eq_1`, `eq_def`, `proof_1`, `match_1`…) and auxiliary names. -/
def isReservedSuffix (n : Name) : Bool :=
  match n with
  | .str _ s => s == "eq_def" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
      || s.startsWith "proof_" || s.startsWith "match_"
  | _ => true

/-- The public theorems the module `m` declares, sorted by name. -/
def moduleTheorems (env : Environment) (m : Name) : Array Name := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if !isPrivateName n && !n.isInternal && !isReservedSuffix n then
        if let some idx := env.getModuleIdxFor? n then
          if env.header.moduleNames[idx.toNat]! == m then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

/-- Every theorem whose name is `….Choices.consumeAt…` — outside the contract's own alias
namespace `GoLean.Contract` (the generated Solution is in the `GoLean` library, so its aliases
are in this environment too; an alias is never a kept theorem). -/
def consumeAtTheorems (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if let .str (.str _ "Choices") s := n then
        if s.startsWith "consumeAt" && !(`GoLean.Contract).isPrefixOf n then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

def check (env : Environment) (family : String) (n : Name) : Except String Unit := do
  let some ci := env.find? n | throw s!"{family}: {n} is not in the environment"
  unless ci matches .thmInfo _ do throw s!"{family}: {n} is not a theorem"
  unless ci.levelParams.isEmpty do throw s!"{family}: {n} has universe parameters {ci.levelParams}"
  unless (`GoLean).isPrefixOf n do throw s!"{family}: {n} is outside the GoLean namespace"
  if (`GoLean.Contract).isPrefixOf n then throw s!"{family}: {n} is a contract alias, not a kept theorem"
  if (`GoLean.Contract).isPrefixOf (moduleOf env n) then throw s!"{family}: {n} is declared in a contract module"

end ContractNames

open ContractNames in
#eval show Lean.Elab.TermElabM Unit from do
  let env ← Lean.getEnv
  let some ext ← Lean.Meta.getSimpExtension? `stepFn_eqns
    | throwError "contract-names: the stepFn_eqns simp attribute is not registered"
  let thms ← ext.getTheorems
  let mut tagged : Array Lean.Name := #[]
  for o in thms.lemmaNames.toList do
    if let .decl n _ _ := o then tagged := tagged.push n
  let eqns := tagged.qsort (fun a b => a.toString < b.toString)
  let families : Array (String × Array Lean.Name) := #[
    ("prefix", #[`GoLean.GoCore.ExecutionStatement.prefix_comp, `GoLean.GoCore.ExecutionStatement.prefix_split,
      `GoLean.GoCore.ExecutionStatement.run_ok_iff, `GoLean.GoCore.ExecutionStatement.run_panic_iff,
      `GoLean.GoCore.ExecutionStatement.replay_coverage]),
    ("enterFrame", #[`GoLean.GoCore.Machine.enterFrame_declared]),
    ("consumeAt", consumeAtTheorems env),
    ("eqns", eqns),
    ("g11", moduleTheorems env `GoLean.GoCore.InitDriverFacts),
    ("pool", #[`GoLean.GoCore.Machine.execProgLoopOut_snd, `GoLean.GoCore.Machine.execProgLoopOut_single,
      `GoLean.GoCore.Machine.execProgLoopOut_single_prefix, `GoLean.GoCore.Machine.seqOut_of_prefix,
      `GoLean.GoCore.Machine.execProgLoopOut_eq_execProgLoop, `GoLean.GoCore.Machine.execProgLoopOut_acc])]
  let mut seen : Std.HashSet Lean.Name := {}
  for (family, names) in families do
    if names.isEmpty then throwError "contract-names: the family {family} is empty"
    for n in names do
      if let .error e := check env family n then throwError "contract-names: {e}"
      if seen.contains n then throwError "contract-names: {n} is listed twice"
      seen := seen.insert n
      IO.println s!"KEPT\t{family}\t{n}\t{moduleOf env n}"
