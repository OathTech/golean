import GoLeanProofs
import Audit

/-!
# WpVeneerClosure — the A-TRIP proof-side closure check (the mature half)

Plan of record: `docs/2026-08-28_iris-corpus-plan.md` §2d (the veneer ban)
and §6.3 (unit A-TRIP, form 2). Unit log: `docs/a-trip-log.md`.
Scope config (shared with `scripts/wp-veneer-lint`):
`scripts/wp-lint-scope.txt` — the boundary definition, the directive
reference, and the split-file convention live there.

THREAT MODEL (scope statement, [USER]-calibrated at the fix round,
2026-08-28): this gate catches an HONEST AUTHOR under schedule pressure
taking an innocent-looking shortcut — a proof that touches the
executable machine directly, a decide on a machine prop, a helper
module nobody classified. It is NOT a fortress against a deliberate
evader; we are the gate's only authors. Per the standing
gates-are-speedbumps rule (2026-08-11): THIS GATE IS DONE — no further
evasion iterations, no arms race; future changes to it are
simplifications or deletions.

LINEAGE: the project's own Audit statement-closure walker
(`proofs/Audit.lean`, the statement-TCB gate), re-aimed from STATEMENT
closures at PROOF-TERM closures. The statement gate's own license is
"Proofs may use anything" — proofs are deleted with Iris, so statements
are all it polices. This check is the other half: for the WP tier the
proof ROUTE is chartered too (§2d: tier-3 proofs reach the machine only
through the Laws/lifting/adequacy layer), and neither cost profiles nor
negative twins can police it at corpus scale.

MECHANIZATION. For every THEOREM declared in a `police` or
`boundary-sentences` module (thmInfo only — deliberate, see the honest
limits below):

- **`police` theorems**: (a) statement precheck — the transitive closure
  of the TYPE must not reach an executable-machine constant (V-STMT:
  first-order machine sentences live in `boundary-sentences` export
  modules per the split-file convention, or on the `exempt` list);
  (b) the proof-term walk — the transitive closure of the VALUE, with
  the classification below (V-PROOF on a machine constant reached).
- **`boundary-sentences` theorems** (R2): the statement is LICENSED to
  be a first-order machine sentence (no type walk); the VALUE is walked
  with police rules under exactly two licenses: (i) constants written
  in the theorem's own TYPE expression are statement vocabulary, exempt
  from the forbidden check; (ii) constants from the `GoLean` core
  package are name-checked but not recursed (the statement legitimately
  embeds the drivers, and unfolding them here would flag every honest
  adequacy application). Documented residual: a proof grinding strictly
  within its own statement's written vocabulary is not distinguishable
  by constant reachability — the lint's unfold bans and review cover
  that corner; the expected sentence proof is a two-line
  goSpec_of_wp/adequacy application.

THE CLASSIFICATION (fix F1 — every reached constant's module is
POSITIVELY classified; nothing is silently skipped):
  - the constant is an executable-machine name (`stepFn` / `stepFnIter`
    / `execStmt` / `execStmtLoop` / `allStreamsOk` / `allStreamsOkPool`,
    whole namespaces so equation lemmas and match auxiliaries are
    covered) → VIOLATION (V-STMT/V-PROOF by walk);
  - declared in a `boundary` module: a THEOREM stops the walk (the
    sanctioned crossing — its statement and proof are the boundary
    layer's business); a DEF/other is RECURSED, type and value (fix F3:
    a def is kernel-transparent — stopping at boundary defs was the
    audited rfl-reduction/TC-decide gap);
  - declared in a `boundary-sentences` module: a THEOREM stops (its own
    proof is policed separately, its statement is licensed); other
    kinds recurse;
  - declared in a `police` module or anywhere in our tree (module root
    exactly `GoLean` or `GoLeanProofs`) → recurse into its type AND its
    value (theorem values included — the re-aim);
  - declared in an ENUMERATED upstream package (module root exactly
    `Iris`/`Std`/`Init`/`Lean`/`Qq`/`Batteries`) → stop: upstream
    cannot depend on our machine;
  - anything else → V-CLASS VIOLATION naming the module (fail closed —
    fix F1: the old name-prefix filter silently skipped the repo's own
    non-GoLean-rooted modules, e.g. a helper module nobody enrolled).

KERNEL DECISIONS, honestly (fix R3 — the earlier blanket claim was
overbroad): a `decide`/`Decidable.decide` closure is caught by this
walk exactly when the decided proposition's constants include the
forbidden six or reach them under the classification above — e.g. a
decide over `allStreamsOk`, or over a Bool wrapper def whose value the
walk unfolds. A kernel certificate over the SANCTIONED SIDE-CONDITION
VOCABULARY is NOT a veneer and passes by construction: concrete-seed
well-formedness checks on the kernel-reducible checker vocabulary —
`GoLean.GoCore.Machine.MachineWf`, `normalizeValueForTy`,
`applyStrictOp`, `dynamicDispatch?` — are sanctioned discharges
(Surface.lean:127-129: "at concrete seeds it is discharged by `decide`
(the checker is kernel-reducible)"). Deciding a WELL-FORMEDNESS side
condition is not deciding a RUN.

HONEST LIMITS: (1) thmInfo-only scope — a proof packaged as a `def` in
a policed module is not walked at its own name (it IS walked wherever a
theorem uses it). House style never packages proofs as defs; adding
def-seeding machinery for a shape we never write is the gate cruft the
2026-08-11 rule deletes. (2) The completeness (police-root) and count
(F6) checks live in the text lint; this checker verifies existence and
classification only.

FAIL-CLOSED, everywhere: missing/unparseable config, an EMPTY
police+sentences set, a scope-listed file absent from disk, a policed
module absent from the loaded environment (scope rot), an `exempt` name
that does not resolve, a forbidden-root rename (existence anchors,
mirroring the Audit gate), an unresolvable constant, an exhausted walk
budget, and ZERO scope theorems all FAIL — whitelist nothing silently.

Invocation (ci step "WP veneer proof-closure check", after the proofs
build so oleans are hot):
    cd proofs && lake env lean ../scripts/WpVeneerClosure.lean
`GOLEAN_WP_SCOPE` overrides the config path — for the fire drills only
(`docs/a-trip-log.md`); ci always runs the default.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  -- ---- the forbidden set: the executable machine --------------------
  let forbiddenRoots : List Name :=
    [`GoLean.GoCore.Machine.stepFn,
     `GoLean.GoCore.Machine.stepFnIter,
     `GoLean.GoCore.Machine.execStmt,
     `GoLean.GoCore.Machine.execStmtLoop,
     `GoLean.GoCore.Machine.allStreamsOk,
     `GoLean.GoCore.Machine.allStreamsOkPool]
  for r in forbiddenRoots do
    let some _ := env.find? r
      | throwError "wp-veneer-closure: forbidden root {r} is MISSING \
          (machine entry point renamed without re-pointing the gate?)"
  let isForbidden : Name → Bool := fun n =>
    forbiddenRoots.any (fun r => r == n || r.isPrefixOf n)
  -- The enumerated upstream packages (fix F1: POSITIVE allowlist by
  -- exact root component — never a string prefix).
  let upstreamRoots : List Name := [`Iris, `Std, `Init, `Lean, `Qq, `Batteries]
  let ourRoots : List Name := [`GoLean, `GoLeanProofs]
  -- ---- config -------------------------------------------------------
  let scopePath := (← IO.getEnv "GOLEAN_WP_SCOPE").getD "../scripts/wp-lint-scope.txt"
  let rootDir := (← IO.getEnv "GOLEAN_WP_ROOT").getD ".."
  unless (← System.FilePath.pathExists scopePath) do
    throwError "wp-veneer-closure: scope config '{scopePath}' missing (fail closed)"
  let cfg ← IO.FS.readFile scopePath
  let dottedName (s : String) : Name :=
    (s.splitOn ".").foldl (fun n c => Name.mkStr n c) Name.anonymous
  let pathToModule (p : String) : Name :=
    -- "proofs/GoLeanProofs/Laws/Assign.lean" → `GoLeanProofs.Laws.Assign
    let comps := (p.replace "/" ".").splitOn "."
    let comps := match comps with
      | "proofs" :: rest => rest
      | c => c
    let comps := if comps.getLast? == some "lean" then comps.dropLast else comps
    comps.foldl (fun n c => Name.mkStr n c) Name.anonymous
  let mut policePaths : Array String := #[]
  let mut boundaryPaths : Array String := #[]
  let mut sentencePaths : Array String := #[]
  let mut exempts : Array Name := #[]
  let mut lineno : Nat := 0
  for raw in cfg.splitOn "\n" do
    lineno := lineno + 1
    let toks := ((raw.splitOn "#").headD "").splitOn " "
      |>.filter (fun t => t ≠ "" && t ≠ "\t")
    if toks.isEmpty then continue
    match toks with
    | ["police", p] => policePaths := policePaths.push p
    | ["boundary", p] => boundaryPaths := boundaryPaths.push p
    | ["boundary-kernel-ok", p, _count] => boundaryPaths := boundaryPaths.push p
    | ["boundary-sentences", p] => sentencePaths := sentencePaths.push p
    | ["police-root", d] =>
      -- Completeness is the text lint's check (it runs first in ci);
      -- here only the fail-closed existence of the root.
      unless (← (System.FilePath.mk rootDir / d).isDir) do
        throwError "wp-veneer-closure: {scopePath}:{lineno}: police-root '{d}' missing (fail closed)"
    | ["exempt-file", p] =>
      unless (← System.FilePath.pathExists (System.FilePath.mk rootDir / p)) do
        throwError "wp-veneer-closure: {scopePath}:{lineno}: exempt-file '{p}' missing on disk (fail closed)"
    | "exempt" :: n :: _ => exempts := exempts.push (dottedName n)
    | _ =>
      throwError "wp-veneer-closure: {scopePath}:{lineno}: unparseable entry '{raw}' (fail closed)"
  if policePaths.isEmpty && sentencePaths.isEmpty then
    throwError "wp-veneer-closure: scope config lists NO police/boundary-sentences \
      files — an empty tripwire scope is a misconfiguration, never a pass (fail closed)"
  for p in policePaths ++ boundaryPaths ++ sentencePaths do
    unless (← System.FilePath.pathExists (System.FilePath.mk rootDir / p)) do
      throwError "wp-veneer-closure: scope-listed file '{p}' missing on disk (fail closed)"
  for x in exempts do
    let some _ := env.find? x
      | throwError "wp-veneer-closure: exempt name {x} does not resolve (fail closed)"
  -- ---- module resolution -------------------------------------------
  let mods := env.header.moduleNames
  let findModIdx (m : Name) : Option Nat := mods.findIdx? (· == m)
  let mut policeIdxs : Std.HashMap Nat Name := {}
  for p in policePaths do
    let m := pathToModule p
    match findModIdx m with
    | some i => policeIdxs := policeIdxs.insert i m
    | none =>
      throwError "wp-veneer-closure: policed module {m} ('{p}') is NOT in the \
        loaded environment — a policed file must be built into the audited \
        import closure (fail closed; import it from the GoLeanProofs root)"
  let mut sentenceIdxs : Std.HashMap Nat Name := {}
  for p in sentencePaths do
    let m := pathToModule p
    match findModIdx m with
    | some i => sentenceIdxs := sentenceIdxs.insert i m
    | none =>
      throwError "wp-veneer-closure: sentence-export module {m} ('{p}') is NOT in \
        the loaded environment (fail closed; import it from the GoLeanProofs root)"
  let mut boundaryIdxs : Std.HashMap Nat Name := {}
  for p in boundaryPaths do
    let m := pathToModule p
    match findModIdx m with
    | some i => boundaryIdxs := boundaryIdxs.insert i m
    | none =>
      -- A boundary module absent from the env cannot be reached by any
      -- policed proof either — a note, not a failure (its FILE
      -- existence was already enforced above).
      IO.println s!"wp-veneer-closure: note — boundary module {m} not loaded \
        (no policed proof can reach it; file exists, nothing to whitelist)"
  -- ---- collect scope theorems (thmInfo only — docstring HONEST LIMITS)
  let mut scopeThms : Array (Name × ConstantInfo × Bool) := #[]  -- (name, info, isSentence)
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if ci matches ConstantInfo.thmInfo _ then
        unless exempts.contains n do
          if policeIdxs.contains idx.toNat then
            scopeThms := scopeThms.push (n, ci, false)
          else if sentenceIdxs.contains idx.toNat then
            scopeThms := scopeThms.push (n, ci, true)
  if scopeThms.isEmpty then
    throwError "wp-veneer-closure: ZERO theorems in the policed scope — \
      a tripwire with nothing under it is a misconfiguration (fail closed)"
  scopeThms := scopeThms.qsort (fun a b => a.1.toString < b.1.toString)
  -- ---- the walk -----------------------------------------------------
  -- Pure chain reconstruction (no mut capture): parent pointers → the
  -- dependency path from the scope theorem to the flagged constant.
  let mkChain (parent : Std.HashMap Name Name) (t c : Name) : String := Id.run do
    let mut chain := s!"{c}"
    let mut cur := c
    for _ in [0:100000] do
      match parent.get? cur with
      | some p =>
        chain := s!"{p} → " ++ chain
        cur := p
        if p == t then break
      | none => break
    return chain
  let mut violations : Array String := #[]
  let mut lines : Array String := #[]
  for (t, tinfo, isSentence) in scopeThms do
    let (tyStmt, tval) := match tinfo with
      | .thmInfo v => (v.type, v.value)
      | _ => (default, default)   -- unreachable: filtered to thmInfo above
    -- Sentence license (i): the constants WRITTEN in the theorem's own
    -- type expression (no recursion) are statement vocabulary.
    let stmtVocab : NameSet :=
      if isSentence then tyStmt.getUsedConstants.foldl (·.insert ·) {} else {}
    -- Police theorems: type walk (V-STMT) then value walk (V-PROOF).
    -- Sentence theorems: value walk only.
    let seeds : List (String × Expr) :=
      if isSentence then [("V-PROOF", tval)]
      else [("V-STMT", tyStmt), ("V-PROOF", tval)]
    let mut sizes : Array Nat := #[]
    for (tag, seed) in seeds do
      let mut queue : Array Name := seed.getUsedConstants
      let mut parent : Std.HashMap Name Name := {}
      for c in queue do
        parent := parent.insert c t
      let mut visited : NameSet := {}
      let mut exhausted := true
      for _ in [0:5000000] do
        if queue.isEmpty then
          exhausted := false
          break
        let c := queue.back!
        queue := queue.pop
        if visited.contains c then
          continue
        visited := visited.insert c
        if isForbidden c then
          unless isSentence && stmtVocab.contains c do
            if tag == "V-STMT" then
              violations := violations.push
                s!"  {t} [V-STMT]: STATEMENT reaches machine constant {c} — a \
                  first-order machine sentence lives in a boundary-sentences \
                  export module (split-file convention, scripts/wp-lint-scope.txt) \
                  or on the exempt list, never in a policed corpus module\
                  \n    chain: {mkChain parent t c}"
            else
              violations := violations.push
                s!"  {t} [V-PROOF]: proof term reaches machine constant {c} \
                  OUTSIDE the Laws/lifting/adequacy boundary — the VENEER \
                  (plan §2d); route through the boundary layer\
                  \n    chain: {mkChain parent t c}"
          continue
        match env.getModuleIdxFor? c with
        | some idx =>
          let mroot := mods[idx.toNat]!.getRoot
          if boundaryIdxs.contains idx.toNat || sentenceIdxs.contains idx.toNat then
            -- F3: theorems stop (the sanctioned crossing / a separately
            -- policed licensed sentence); defs and everything else are
            -- kernel-transparent and recurse.
            if (env.find? c).any (· matches ConstantInfo.thmInfo _) then
              continue
            else
              pure ()
          else if policeIdxs.contains idx.toNat then
            pure ()  -- recurse: a policed module's helpers are walked
          else if ourRoots.contains mroot then
            -- Sentence license (ii): GoCore constants are name-checked
            -- (the forbidden test above) but not recursed.
            if isSentence && mroot == `GoLean then
              continue
            else
              pure ()  -- recurse through our own tree
          else if upstreamRoots.contains mroot then
            continue  -- enumerated upstream cannot depend on our machine
          else
            -- F1: an unclassified module is a violation, never a skip.
            violations := violations.push
              s!"  {t} [V-CLASS]: reaches constant {c} from UNCLASSIFIED module \
                {mods[idx.toNat]!} — classify the module in \
                scripts/wp-lint-scope.txt or remove the dependency (fail closed)\
                \n    chain: {mkChain parent t c}"
            continue
        | none => pure ()  -- declared in the current file: recurse
        let some ci := env.find? c
          | throwError "wp-veneer-closure: {c} (reached from {t}) not found (fail closed)"
        let mut next : Array Name := ci.type.getUsedConstants
        -- EXHAUSTIVE over ConstantInfo, no wildcard (fail-closed, the
        -- Audit walker's own rule) — and unlike the statement gate,
        -- THEOREM VALUES ARE WALKED: that is the re-aim.
        match ci with
        | .defnInfo v => next := next ++ v.value.getUsedConstants
        | .opaqueInfo v => next := next ++ v.value.getUsedConstants
        | .thmInfo v => next := next ++ v.value.getUsedConstants
        | .inductInfo v => next := next ++ v.ctors.toArray
        | .axiomInfo _ => pure ()  -- no value (the axiom sweep owns axioms)
        | .ctorInfo _ => pure ()   -- no value; type already walked
        | .recInfo _ => pure ()    -- no value; type already walked
        | .quotInfo _ => pure ()   -- primitive; type already walked
        for n in next do
          unless visited.contains n do
            if !(parent.contains n) then
              parent := parent.insert n c
            queue := queue.push n
      if exhausted then
        throwError "wp-veneer-closure: walk budget exhausted at {t} ({tag}) — \
          raise the bound deliberately, never silently"
      sizes := sizes.push visited.size
    lines := lines.push (if isSentence then
        s!"  {t} [sentence]: {sizes[0]!} proof constants walked"
      else
        s!"  {t}: {sizes[0]!} statement / {sizes[1]!} proof constants walked")
  if violations.isEmpty then
    IO.println s!"wp-veneer-closure: {scopeThms.size} policed theorem(s) across \
      {policeIdxs.size + sentenceIdxs.size} module(s), all proof terms reach the \
      machine only through the {boundaryIdxs.size} boundary module(s); \
      {exempts.size} exempt"
    for l in lines do
      IO.println l
  else
    throwError "wp-veneer-closure FAILED — the veneer tripwire \
      (docs/2026-08-28_iris-corpus-plan.md §2d; scope: scripts/wp-lint-scope.txt):\n\
      {String.intercalate "\n" violations.toList}"
