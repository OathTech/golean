import Lean
import GoLeanProofsCorpus

/-!
# In-build epistemic gate for the VALIDATION CORPUS

The corpus split (A4-U25 slice 0, 2026-08-26; the OOM incident's
correction (a)) moved the literal-mode corpus out of the default build —
see `GoLeanProofsCorpus.lean`'s header for the census, the AMENDED
placement criterion (arc-4 landing fix round: witnesses of LIVE laws
are live; the Ring/Round* chains and their pin modules
`Audit/{Ring,RoundMa,RoundVote,RoundMar,RoundVr,RoundIndWitness}`
moved back to the default `Audit` target), and the landmark build
discipline. This file is the corpus's `Audit.lean`: it re-runs the
exhaustive axiom sweep over the corpus closure — now exactly the
handler-equation validation chains — so a `sorry`/`native_decide`/new
postulate anywhere in a corpus module fails the CORPUS build exactly
as it would have failed the default build before the split. Build
with:

    scripts/capped lake build AuditCorpus

and RECORD the run in the tracked `docs/corpus-landmark-record.md`
(fix-round F7; `artifacts/` is gitignored and is not a record).

Coverage split, stated honestly: the per-gate `Audit` target does not
see these modules; their sweep runs at landmark corpus builds only.
`scripts/ci`'s proofs-file coverage step pins every corpus file to THIS
root's import closure and prints a visible deferred-sweep note — a file
in neither closure fails the gate, so nothing can silently drop out of
both sweeps.
-/

namespace GoLean.Iris.AuditCorpus

/-! ## Exhaustive axiom sweep over the corpus closure

Verbatim mechanism from `Audit.lean`'s sweep (its docstring is the
mechanism's record; keep the two blocks in sync on any deliberate
change): walks every constant declared in any module whose name root
starts with `GoLean` in THIS build's environment — which here includes
the whole corpus plus the live modules it imports — and fails the build
on any axiom outside the classical trio. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot.toString.startsWith "GoLean")
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut bad : Array (Name × Name) := #[]
  let mut audited := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true
    unless ours do continue
    let axs ← collectAxioms n
    audited := audited + 1
    for ax in axs do
      unless allowed.contains ax do
        bad := bad.push (n, ax)
  if bad.isEmpty then
    IO.println s!"corpus audit sweep: {audited} declarations across the corpus closure, all axiom-clean"
  else
    let lines := bad.qsort (fun a b => a.1.toString < b.1.toString)
      |>.map (fun (n, ax) => s!"  {n} depends on {ax}")
    throwError "corpus audit sweep FAILED — declarations with disallowed axioms \
      (a `sorry`, `native_decide`, or new postulate?):\n{String.intercalate "\n" lines.toList}"

end GoLean.Iris.AuditCorpus
