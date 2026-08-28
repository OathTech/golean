import GoLeanProofs
import Audit

/-!
# WpVeneerClosure — the A-TRIP proof-side closure check (the mature half)

Plan of record: `docs/2026-08-28_iris-corpus-plan.md` §2d (the veneer ban)
and §6.3 (unit A-TRIP, form 2). Unit log: `docs/a-trip-log.md`.
Scope config (shared with `scripts/wp-veneer-lint`):
`scripts/wp-lint-scope.txt` — the boundary definition lives there.

LINEAGE: the project's own Audit statement-closure walker
(`proofs/Audit.lean`, the statement-TCB gate), re-aimed from STATEMENT
closures at PROOF-TERM closures. The statement gate's own license is
"Proofs may use anything" — proofs are deleted with Iris, so statements
are all it polices. This check is the other half: for the WP tier the
proof ROUTE is chartered too (§2d: tier-3 proofs reach the machine only
through the Laws/lifting/adequacy layer), and neither cost profiles nor
negative twins can police it at corpus scale (kernel grinding is a cost
INLIER on 15-60-line programs; a veneer proves a twin as easily as the
positive).

MECHANIZATION. For every theorem DECLARED in a `police`-listed module:

- **statement precheck**: walk the transitive closure of its TYPE (same
  recursion as the value walk below). If it reaches an
  executable-machine constant, the theorem is not a WP-tier sentence —
  first-order machine sentences live in `boundary`-listed export
  modules (or on the config's `exempt` carve-out list with provenance,
  plan §6.3's declared-carve-out clause), never in policed corpus
  modules. Reported as V-STMT, with the reach chain.
- **proof-term walk**: walk the transitive closure of its VALUE (the
  proof term). Recursion rules, per reached constant `c`:
  - `c` is an executable-machine constant (`stepFn` / `stepFnIter` /
    `execStmt` / `execStmtLoop` / `allStreamsOk` / `allStreamsOkPool`,
    each with its whole namespace so equation lemmas, match auxiliaries
    and `.eq_def`-class names are covered) → **VENEER VIOLATION**
    (V-PROOF), reported with the dependency chain. A kernel decision on
    a machine proposition (`decide`/`Decidable.decide` closures) is
    caught by the same rule: the decided proposition's instance carries
    the machine constants into the term.
  - `c` originates in a `boundary`-listed module → STOP, no recursion:
    reaching the machine through the Laws/lifting/adequacy layer is
    exactly the sanctioned route.
  - `c` originates outside our tree (module root not `GoLean*`:
    Iris/Std/Init/Lean) → STOP: upstream cannot depend on our machine.
  - otherwise (any other `GoLean*` constant, incl. other policed
    modules) → recurse into its type AND — the re-aim — its VALUE for
    definitions, opaques and THEOREMS alike: a helper lemma's proof
    grinding the machine is the veneer this check exists to catch.

FAIL-CLOSED, everywhere: missing/unparseable config, an EMPTY police
list, a policed file absent from disk, a policed module absent from the
loaded environment (listed but never built into the audited closure —
scope rot), an `exempt` name that does not resolve, a forbidden-root
rename (existence anchors, mirroring the Audit gate), an unresolvable
constant, an exhausted walk budget, and ZERO scope theorems (a tripwire
with nothing under it) all FAIL — whitelist nothing silently.

Invocation (ci step "WP veneer proof-closure check", after the proofs
build so oleans are hot):
    cd proofs && lake env lean ../scripts/WpVeneerClosure.lean
`GOLEAN_WP_SCOPE` overrides the config path — for the tripwire's own
fire drill only (`docs/a-trip-log.md`); ci always runs the default.
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
  -- Existence anchors (the rename-hole guard, mirrored from the Audit
  -- gate): a moved/renamed machine entry point must break HERE, never
  -- silently leave the check checking nothing.
  for r in forbiddenRoots do
    let some _ := env.find? r
      | throwError "wp-veneer-closure: forbidden root {r} is MISSING \
          (machine entry point renamed without re-pointing the gate?)"
  let isForbidden : Name → Bool := fun n =>
    forbiddenRoots.any (fun r => r == n || r.isPrefixOf n)
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
    | ["boundary-kernel-ok", p] => boundaryPaths := boundaryPaths.push p
    | ["police-dir", d] | ["boundary-dir", d] =>
      let isPolice := toks.headD "" == "police-dir"
      let dir : System.FilePath := System.FilePath.mk rootDir / d
      unless (← dir.isDir) do
        throwError "wp-veneer-closure: {scopePath}:{lineno}: dir '{d}' missing (fail closed)"
      let files ← dir.walkDir
      let leans := (files.filter (fun f => f.extension == some "lean")).qsort
        (fun a b => a.toString < b.toString)
      if leans.isEmpty then
        throwError "wp-veneer-closure: {scopePath}:{lineno}: dir '{d}' has no .lean files (fail closed)"
      for f in leans do
        -- back to a repo-relative path (strip the rootDir prefix)
        let rel := f.toString.replace (rootDir ++ "/") ""
        if isPolice then policePaths := policePaths.push rel
        else boundaryPaths := boundaryPaths.push rel
    | "exempt" :: n :: _ => exempts := exempts.push (dottedName n)
    | _ =>
      throwError "wp-veneer-closure: {scopePath}:{lineno}: unparseable entry '{raw}' (fail closed)"
  if policePaths.isEmpty then
    throwError "wp-veneer-closure: scope config lists NO police files — \
      an empty tripwire scope is a misconfiguration, never a pass (fail closed)"
  -- Files must exist on disk (config rot is loud).
  for p in policePaths ++ boundaryPaths do
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
  let mut boundaryIdxs : Std.HashMap Nat Name := {}
  for p in boundaryPaths do
    let m := pathToModule p
    match findModIdx m with
    | some i => boundaryIdxs := boundaryIdxs.insert i m
    | none =>
      -- A boundary module absent from the env cannot be reached by any
      -- policed proof either — a note, not a failure (its FILE existence
      -- was already enforced above).
      IO.println s!"wp-veneer-closure: note — boundary module {m} not loaded \
        (no policed proof can reach it; file exists, nothing to whitelist)"
  let isGoLean : Name → Bool := fun m => m.getRoot.toString.startsWith "GoLean"
  -- ---- collect scope theorems --------------------------------------
  let mut scopeThms : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if policeIdxs.contains idx.toNat then
        if ci matches ConstantInfo.thmInfo _ then
          unless exempts.contains n do
            scopeThms := scopeThms.push (n, ci)
  if scopeThms.isEmpty then
    throwError "wp-veneer-closure: ZERO theorems in the policed scope — \
      a tripwire with nothing under it is a misconfiguration (fail closed)"
  scopeThms := scopeThms.qsort (fun a b => a.1.toString < b.1.toString)
  -- ---- the walk -----------------------------------------------------
  let mut violations : Array String := #[]
  let mut lines : Array String := #[]
  for (t, tinfo) in scopeThms do
    -- Two walks per theorem: the TYPE (statement precheck) and the VALUE
    -- (the proof term — the re-aim). Same recursion, different seed and
    -- different report tag.
    let seeds : List (String × Expr) :=
      match tinfo with
      | .thmInfo v => [("V-STMT", v.type), ("V-PROOF", v.value)]
      | _ => []   -- unreachable: filtered to thmInfo above
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
          let mut chain := s!"{c}"
          let mut cur := c
          for _ in [0:100000] do
            match parent.get? cur with
            | some p =>
              chain := s!"{p} → " ++ chain
              cur := p
              if p == t then break
            | none => break
          if tag == "V-STMT" then
            violations := violations.push
              s!"  {t} [V-STMT]: STATEMENT reaches machine constant {c} — a \
                first-order machine sentence does not live in a policed corpus \
                module; move it to a boundary-listed export module or the \
                exempt list (with provenance)\n    chain: {chain}"
          else
            violations := violations.push
              s!"  {t} [V-PROOF]: proof term reaches machine constant {c} \
                OUTSIDE the Laws/lifting/adequacy boundary — the VENEER \
                (plan §2d); route through the boundary layer\n    chain: {chain}"
          continue
        match env.getModuleIdxFor? c with
        | some idx =>
          if boundaryIdxs.contains idx.toNat then
            continue  -- the sanctioned crossing: stop, do not recurse
          -- A POLICED module always recurses, whatever its name root —
          -- found live at the fire drill: the upstream filter below
          -- silently skipped a policed scratch module's own helper
          -- lemmas because its module name was not GoLean-rooted.
          unless policeIdxs.contains idx.toNat do
            unless isGoLean mods[idx.toNat]! do
              continue  -- upstream (Iris/Std/Init/Lean) cannot reach our machine
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
    lines := lines.push s!"  {t}: {sizes[0]!} statement / {sizes[1]!} proof constants walked"
  if violations.isEmpty then
    IO.println s!"wp-veneer-closure: {scopeThms.size} policed theorem(s) across \
      {policeIdxs.size} module(s), all proof terms reach the machine only \
      through the {boundaryIdxs.size} boundary module(s); {exempts.size} exempt"
    for l in lines do
      IO.println l
  else
    throwError "wp-veneer-closure FAILED — the veneer tripwire \
      (docs/2026-08-28_iris-corpus-plan.md §2d; scope: scripts/wp-lint-scope.txt):\n\
      {String.intercalate "\n" violations.toList}"
