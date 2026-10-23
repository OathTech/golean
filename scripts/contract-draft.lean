/-
scripts/contract-draft.lean — a DRAFT of the comparator challenge's statements, printed from the
built environment (lane gate/comparator-1023, 2026-10-23; release-readiness row 43). Run from the
checkout root through scripts/contract-challenge-draft (it adds the header and runs this file):

    lake env lean scripts/contract-draft.lean > draft.lean

For every alias in comparator.json's `theorem_names` (`GoLean.Contract.<rest>` ↦ the kept theorem
`GoLean.<rest>`) this prints `theorem GoLean.Contract.<rest> : <statement> := sorry`, the statement
being the kept theorem's type as the kernel holds it (a `*_stmt` constant unfolded, as `stmt_of%`
does), printed by the delaborator and then CHECKED: the printed command is elaborated here, in
the challenge's own scope (the same `open`s, the same declaration shape), and the declared type
must be `==` the kept theorem's type — the comparator's own test. A statement whose default
print mints a fresh matcher (`match`/`do` in a statement: the matcher cache is per module) is
reprinted with `pp.match false`, naming the original's matcher constants; a statement that still
does not round-trip is printed with a `-- CONTRACT DRAFT: …` marker and this script exits 1 —
that statement is spelled by hand in Contract/Challenge.lean (today: one, `applyStmtOp_print`,
whose `.ok (s, ch, [], [])` elaborates through the expected type where the printed `Except.ok`
does not).

THIS IS A DRAFT TOOL, NOT THE CONTRACT. The tracked Contract/Challenge.lean is the frozen
statement set, updated DELIBERATELY with a changelog row; regenerating it from main makes the
comparator compare main with main. Use the draft to see what a deliberate update would say.
-/
import GoLean
import Lean

set_option warn.sorry false

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

namespace ContractDraft
open Lean

def readAliases : IO (Array Name) := do
  let text ← IO.FS.readFile "comparator.json"
  let json ← IO.ofExcept (Json.parse text)
  let names ← IO.ofExcept (json.getObjVal? "theorem_names")
  let arr ← IO.ofExcept names.getArr?
  arr.mapM fun j => do
    let s ← IO.ofExcept j.getStr?
    unless s.startsWith "GoLean.Contract." do
      throw <| IO.userError s!"contract-draft: '{s}' is not a GoLean.Contract.* alias"
    return s.toName

def originalOf (alias : Name) : Name :=
  let rest := alias.replacePrefix `GoLean.Contract .anonymous
  `GoLean ++ rest

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!.toString
  | none => "?"

def statementOf (env : Environment) (n : Name) : Except String Lean.Expr := do
  let some info := env.find? n | throw s!"{n} is not in the environment"
  unless info matches .thmInfo _ do throw s!"{n} is not a theorem"
  unless info.levelParams.isEmpty do throw s!"{n} has universe parameters"
  if let .const h _ := info.type then
    if h.toString.endsWith "_stmt" then
      let some hi := env.find? h | throw s!"{h} missing"
      let some v := hi.value? | throw s!"{h} has no value"
      return v
  return info.type

def indent (s : String) (by_ : String) : String :=
  "\n".intercalate (s.splitOn "\n" |>.map (by_ ++ ·))

def ppOptions (base : Options) (matchOff : Bool) : Options :=
  let o := base.setBool `pp.proofs true |>.setBool `pp.deepTerms true
    |>.set `pp.maxSteps (10000000 : Nat) |>.setBool `pp.funBinderTypes true
  if matchOff then o.setBool `pp.match false else o

end ContractDraft

open ContractDraft in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let aliases ← readAliases
  let env0 ← Lean.getEnv
  let mut failures : Array Lean.Name := #[]
  let mut viaMatcher : Array Lean.Name := #[]
  let mut lastModule := ""
  for alias in aliases do
    let orig := originalOf alias
    let ty ← match statementOf env0 orig with
      | .ok t => pure t
      | .error e => throwError "contract-draft: {e}"
    let m := moduleOf env0 orig
    if m != lastModule then
      IO.println s!"\n/-! ## {m} -/"
      lastModule := m
    let mut emitted := false
    let mut note := ""
    for (matchOff, parens) in [(false, false), (false, true), (true, false), (true, true)] do
      if emitted then continue
      let opts := ppOptions (← Lean.getOptions) matchOff
      let fmt ← Lean.Elab.Command.liftTermElabM do
        Lean.withOptions (fun _ => opts) do Lean.Meta.ppExpr ty
      let printed := fmt.pretty 100
      -- Parenthesised when the bare form does not parse: a statement ending in a `do` block
      -- would read the theorem's `:=` as a reassignment inside the block.
      let body := if parens then s!"({(indent printed "     ").drop 5})" else printed
      let text := s!"theorem {alias} :\n{indent body "    "}\n    := sorry"
      match Lean.Parser.runParserCategory env0 `command text with
      | .error e => IO.eprintln s!"contract-draft: {orig}: the printed statement does not parse{if parens then " (parenthesised)" else ""} ({e})"
      | .ok stx =>
        let saved ← get
        modify fun st => { st with messages := {} }
        Lean.Elab.Command.elabCommand stx
        let msgs := (← get).messages
        let declared := ((← Lean.getEnv).find? alias).map (·.type)
        set saved
        if msgs.hasErrors then
          let firstErr ← match msgs.toList.find? (·.severity == .error) with
            | some msg => msg.data.toString
            | none => pure "?"
          IO.eprintln s!"contract-draft: {orig}: the printed statement does not elaborate{if matchOff then " (pp.match off)" else ""}{if parens then " (parenthesised)" else ""}: {firstErr}"
        else if declared == some ty then
          if matchOff then
            viaMatcher := viaMatcher.push orig
            note := "-- Stated through the original's matcher constants (`pp.match false`): a `match` in a\n-- statement mints a matcher per module, so the challenge names the kept theorem's own.\n"
          IO.println s!"\n/-- `{orig}` ({m}) -/\n{note}{text}"
          emitted := true
        else
          IO.eprintln s!"contract-draft: {orig}: the printed statement elaborates to a DIFFERENT expression{if matchOff then " (pp.match off)" else ""}{if parens then " (parenthesised)" else ""}"
    unless emitted do
      failures := failures.push orig
      let opts := ppOptions (← Lean.getOptions) false
      let fmt ← Lean.Elab.Command.liftTermElabM do Lean.withOptions (fun _ => opts) do Lean.Meta.ppExpr ty
      IO.println s!"\n/-- `{orig}` ({m}) -/\n-- CONTRACT DRAFT: the printed form below does NOT re-elaborate to the kept theorem's statement;\n-- spell it by hand (see the hand-spelled entries in Contract/Challenge.lean).\ntheorem {alias} :\n{indent (fmt.pretty 100) "    "}\n    := sorry"
  IO.eprintln s!"contract-draft: {aliases.size} statements; {viaMatcher.size} through matcher constants {viaMatcher}; {failures.size} not round-tripping {failures}"
  unless failures.isEmpty do
    throwError "contract-draft: {failures.size} statement(s) need hand spelling: {failures}"
