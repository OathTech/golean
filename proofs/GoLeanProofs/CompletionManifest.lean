import Lean

/-!
# THE COMPLETION MANIFEST (channel-logic S1, gen-5 restructure)

**The reviewed record of every run-conditioned export in the proofs
package.** After four review generations of per-shape gate rules each
falling to a new escape (rounds 1-4; gen-5 found the pairing key's
(types, funcs, methods) axis), the gate was RESTRUCTURED per the §14
design: the checker in `Audit.lean` only ENUMERATES — it computes,
for every in-scope constant whose type-closure reaches the
triple/spec carriers (concurrent `GoTripleC`/`GoSpecC` AND sequential
`GoTriple`/`GoSpec`), a descriptor carrying the constant's kind,
class, the FULL key tuple of every carrier application (types, funcs,
methods, env₀, prog — every argument that determines the run), and
the mechanically-matched completion pin with the pin's own full
(env₀, seed, prog) tuple. THIS FILE is the record those descriptors
must match, line for line, with a REVIEWED disposition per line. The
build fails on ANY drift (a new export, a changed statement, a lost
pin, a stale line) until a human-reviewed manifest line lands in the
same commit — exactly the tracked-baseline re-pin discipline
(CLAUDE.md: re-pin only on a deliberate, explained change, in the
same commit, with the reason).

**Dispositions** (validated mechanically where possible):
- `paired-exact` — the checker found a completion pin whose
  (env₀, prog) equals the export's; the pin's full seed tuple is IN
  THE DESCRIPTOR, so a seed-vs-(types,funcs,methods) mismatch is
  visible to the reviewer on this very line (the gen-5 escape class
  becomes reviewable drift; no rule anticipates it).
- `paired-with-stated-delta: <reason>` — completion/readout content
  exists but not as a mechanically-matched pin; the reason states
  where and why (the legacy designated sequential statement-forms).
- `fixture: <unpaired|wrapper|open>` — a tracked attacker shape; the
  checker verifies the computed class matches and no pin pairs it.
- `allowlisted: <reason>` — a genuine ∀-program lemma (method, not an
  export).
- `UNRESOLVED` — fails the build, always.

**Recorded limits, ALL of them** (the gen-5 honesty sweep):
- `paired-exact`'s mechanical floor is (env₀, prog) equality; the
  agreement of the pin's SEED with the export's (types, funcs,
  methods) — and with its precondition — is REVIEWED via the visible
  tuples, not machine-verified. Pre-side vacuity (`.pure False` and
  friends) remains the witness discipline's job (the D1 readout pair
  discharges `InitialSplit` at the pin's own seed; slice note §10).
- The dispositions themselves are reviewed prose, not proofs.
- `_private`-rooted declarations are out of scope by recorded design
  (not exports; the checker asserts the tracked private fixture is
  skipped).
- Constants declared in `Audit.lean` itself have no module index and
  are asserted ABSENT (the same-module blind spot, checked empty).
- WATCHED SURFACE: `compat/gobra` imports `GoLeanProofs.Surface` but
  is outside Audit's import closure — zero triple-carrying constants
  there today (gen-5 census); any future one is invisible to this
  gate and must be brought into a checked closure when it appears.

Editing rule: NEVER edit a descriptor to silence drift without
reviewing the constant it describes; the descriptor is the checker's
output, the disposition is yours.
-/

namespace GoLean.Iris.Audit

/-- One reviewed line of the completion manifest. -/
structure CMEntry where
  name : String
  descriptor : String
  disposition : String

/-- The record (module docstring for the discipline). -/
def completionManifest : List CMEntry := [
  .mk
    "GoLean.ImportedGoose.SemanticsBlock.explicitBlockSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#16859322597341794376;f=GoLean.GoCore.Program.funcs GoLean.Impor…#6068810076907422297;m=GoLean.GoCore.Program.methods GoLean.Imp…#10991627578968518344;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsBlock.explicitBlockDriver)|pin=GoLean.ImportedGoose.SemanticsBlock.explicitBlockTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#14669134493272714158;p=GoLean.ImportedGoose.SemanticsBlock.explicitBlockDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsBlock.explicitBlockSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#16859322597341794376;f=GoLean.GoCore.Program.funcs GoLean.Impor…#6068810076907422297;m=GoLean.GoCore.Program.methods GoLean.Imp…#10991627578968518344;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsBlock.explicitBlockDriver)|pin=GoLean.ImportedGoose.SemanticsBlock.explicitBlockTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#14669134493272714158;p=GoLean.ImportedGoose.SemanticsBlock.explicitBlockDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNew.nilDefaultSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#15760683273242116113;f=GoLean.GoCore.Program.funcs GoLean.Impor…#10110136080688851922;m=GoLean.GoCore.Program.methods GoLean.Imp…#18261098105118961241;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNew.nilDefaultDriver)|pin=GoLean.ImportedGoose.SemanticsNew.nilDefaultTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11798514820773606993;p=GoLean.ImportedGoose.SemanticsNew.nilDefaultDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNew.nilDefaultSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#15760683273242116113;f=GoLean.GoCore.Program.funcs GoLean.Impor…#10110136080688851922;m=GoLean.GoCore.Program.methods GoLean.Imp…#18261098105118961241;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNew.nilDefaultDriver)|pin=GoLean.ImportedGoose.SemanticsNew.nilDefaultTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11798514820773606993;p=GoLean.ImportedGoose.SemanticsNew.nilDefaultDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNew.nilValSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#15760683273242116113;f=GoLean.GoCore.Program.funcs GoLean.Impor…#10110136080688851922;m=GoLean.GoCore.Program.methods GoLean.Imp…#18261098105118961241;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNew.nilValDriver)|pin=GoLean.ImportedGoose.SemanticsNew.nilValTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11798514820773606993;p=GoLean.ImportedGoose.SemanticsNew.nilValDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNew.nilValSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#15760683273242116113;f=GoLean.GoCore.Program.funcs GoLean.Impor…#10110136080688851922;m=GoLean.GoCore.Program.methods GoLean.Imp…#18261098105118961241;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNew.nilValDriver)|pin=GoLean.ImportedGoose.SemanticsNew.nilValTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11798514820773606993;p=GoLean.ImportedGoose.SemanticsNew.nilValDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compareNilDriver)|pin=GoLean.ImportedGoose.SemanticsNil.compareNilToNilTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compareNilDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compareNilDriver)|pin=GoLean.ImportedGoose.SemanticsNil.compareNilToNilTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compareNilDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.comparePointerToNilSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.comparePointerDriver)|pin=GoLean.ImportedGoose.SemanticsNil.comparePointerToNilTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.comparePointerDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.comparePointerToNilSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.comparePointerDriver)|pin=GoLean.ImportedGoose.SemanticsNil.comparePointerToNilTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.comparePointerDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedDefaultToNilSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compar…#13408442873981934101)|pin=GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedDefaultToNilTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compar…#13408442873981934101"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedDefaultToNilSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compar…#13408442873981934101)|pin=GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedDefaultToNilTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compar…#13408442873981934101"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedToNilSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compareWrappedDriver)|pin=GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedToNilTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compareWrappedDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedToNilSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compareWrappedDriver)|pin=GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedToNilTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compareWrappedDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.compareSliceToNilSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compareSliceDriver)|pin=GoLean.ImportedGoose.SemanticsNil.compareSliceToNilTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compareSliceDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsNil.compareSliceToNilSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#4783555598420755177;f=GoLean.GoCore.Program.funcs GoLean.Impor…#14111632067245656467;m=GoLean.GoCore.Program.methods GoLean.Imp…#3895226998457038215;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsNil.compareSliceDriver)|pin=GoLean.ImportedGoose.SemanticsNil.compareSliceToNilTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#10490241543998168049;p=GoLean.ImportedGoose.SemanticsNil.compareSliceDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsVars.anonymousAssignSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#13137992289110606965;f=GoLean.GoCore.Program.funcs GoLean.Impor…#12616850344304691683;m=GoLean.GoCore.Program.methods GoLean.Imp…#450570852092575914;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsVars.anonymousAssignDriver)|pin=GoLean.ImportedGoose.SemanticsVars.anonymousAssignTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11964841771666852942;p=GoLean.ImportedGoose.SemanticsVars.anonymousAssignDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsVars.anonymousAssignSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#13137992289110606965;f=GoLean.GoCore.Program.funcs GoLean.Impor…#12616850344304691683;m=GoLean.GoCore.Program.methods GoLean.Imp…#450570852092575914;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsVars.anonymousAssignDriver)|pin=GoLean.ImportedGoose.SemanticsVars.anonymousAssignTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11964841771666852942;p=GoLean.ImportedGoose.SemanticsVars.anonymousAssignDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsVars.pointerAssignmentSpec"
    "k=thm|c=app|GoSpec(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#13137992289110606965;f=GoLean.GoCore.Program.funcs GoLean.Impor…#12616850344304691683;m=GoLean.GoCore.Program.methods GoLean.Imp…#450570852092575914;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsVars.pointerAssignmentDriver)|pin=GoLean.ImportedGoose.SemanticsVars.pointerAssignmentTerminatesNormally|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11964841771666852942;p=GoLean.ImportedGoose.SemanticsVars.pointerAssignmentDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.SemanticsVars.pointerAssignmentSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#13137992289110606965;f=GoLean.GoCore.Program.funcs GoLean.Impor…#12616850344304691683;m=GoLean.GoCore.Program.methods GoLean.Imp…#450570852092575914;e=GoLean.ImportedGoose.importedEnv;p=GoLean.ImportedGoose.SemanticsVars.pointerAssignmentDriver)|pin=GoLean.ImportedGoose.SemanticsVars.pointerAssignmentTerminatesNormallyC|pinkey=e=GoLean.ImportedGoose.importedEnv;s=GoLean.ImportedGoose.importedSeed GoLean…#11964841771666852942;p=GoLean.ImportedGoose.SemanticsVars.pointerAssignmentDriver"
    "paired-exact",
  .mk
    "GoLean.ImportedGoose.goSpec_seeded_readout"
    "k=thm|c=open"
    "allowlisted: generic seeded-kit lemma (∀-program, carrier in hypothesis position); its instances are the per-row exports, each dispositioned here",
  .mk
    "GoLean.ImportedGoose.goSpec_seeded_readoutC"
    "k=thm|c=open"
    "allowlisted: generic seeded-kit lemma (∀-program, carrier in hypothesis position); instances dispositioned here",
  .mk
    "GoLean.ImportedGoose.goSpec_seeded_terminatesNormallyC"
    "k=thm|c=open"
    "allowlisted: generic seeded-kit PIN DERIVER (∀-program); the pins it produces are the named per-row *TerminatesNormallyC theorems",
  .mk
    "GoLean.ImportedGoose.goSpec_seeded_totalReadout"
    "k=thm|c=open"
    "allowlisted: generic seeded-kit lemma (∀-program, carrier in hypothesis position); instances dispositioned here",
  .mk
    "GoLean.Iris.chanCloseTripleC"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=GoLean.Iris.closeEnv;p=GoLean.Iris.chanCloseProg)|pin=GoLean.Iris.chanCloseTerminatesNormallyC|pinkey=e=GoLean.Iris.closeEnv;s=GoLean.Iris.closeSeed;p=GoLean.Iris.chanCloseProg"
    "paired-exact",
  .mk
    "GoLean.Iris.chanRendezvousTripleC"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#9050443339215725655;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=GoLean.Iris.rdvEnv;p=GoLean.Iris.chanRendezvousProg)|pin=GoLean.Iris.chanRendezvousTerminatesNormallyC|pinkey=e=GoLean.Iris.rdvEnv;s=GoLean.Iris.rdvSeed;p=GoLean.Iris.chanRendezvousProg"
    "paired-exact",
  .mk
    "GoLean.Iris.deadlockRecvTripleC"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=GoLean.Iris.deadlockRecvEnv;p=GoLean.Iris.deadlockRecvProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Iris.goSpec_of_wp"
    "k=thm|c=open"
    "allowlisted: the sequential WP exit (∀-program transfer; method, not an export)",
  .mk
    "GoLean.Iris.goTripleC_of_wpD"
    "k=thm|c=open"
    "allowlisted: the D-Language exit (∀-program; method — its instances are the channel-logic exports)",
  .mk
    "GoLean.Iris.goTriple_of_wp"
    "k=thm|c=open"
    "allowlisted: the sequential triple-half WP exit (∀-program; method)",
  .mk
    "GoLean.Iris.spawnNoopTripleC"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16166456824834555192;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Iris.spawnNoopProg)|pin=GoLean.Iris.spawnNoopTerminatesNormallyC|pinkey=e=List.nil.{0} GoLean.GoCore.Scope;s=GoLean.Iris.spawnNoopSeed;p=GoLean.Iris.spawnNoopProg"
    "paired-exact",
  .mk
    "GoLean.Surface.ZzStructWrappedTriple.casesOn"
    "k=def|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzStructProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.ZzStructWrappedTriple.mk._flat_ctor"
    "k=def|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzStructProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.ZzStructWrappedTriple.recOn"
    "k=def|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzStructProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.ZzStructWrappedTriple.triple"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzStructProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface._fixtureUnderscoreTriple"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzUnderscoreProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.committedIndexAllConfigs"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated ∀-config family statement; per-seed completion content: the TotalPins designated family at its seeds; the ∀-config quantifier itself carries NO completion claim — recorded honest gap, predates the doctrine",
  .mk
    "GoLean.Surface.fixtureDecoyTriple"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzDecoyProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureDefTriple"
    "k=def|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzFixtureProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureDefTriple.eq_realExport"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzSuffixProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureDefTriple.namespaceChildProbe"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzChildProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureEnvMismatchTriple"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.goldenDriver)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureGuardedTriple"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzGuardedProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureOpaqueEdge"
    "k=thm|c=wrapper"
    "fixture: wrapper",
  .mk
    "GoLean.Surface.fixtureOpaqueTriple"
    "k=opaque|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzOpaqueProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureOpenProgTriple"
    "k=thm|c=open"
    "fixture: open",
  .mk
    "GoLean.Surface.fixtureOutOfSpecsTriple"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzOutOfSpecsProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureSelfPin"
    "k=thm|c=app|GoTripleC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzSelfPinProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureSpecCUnpinned"
    "k=thm|c=app|GoSpecC(t=List.nil.{0} (Prod.{0, 0} GoLean.TypeId …#14726585989525536044;f=List.toArray.{0} GoLean.GoCore.Func (Lis…#16868649788984744378;m=List.toArray.{0} GoLean.GoCore.MethodInf…#9691153597751718427;e=List.nil.{0} GoLean.GoCore.Scope;p=GoLean.Surface.zzFixtureProg)|pin=-|pinkey=-"
    "fixture: unpaired",
  .mk
    "GoLean.Surface.fixtureStructWrapped"
    "k=thm|c=wrapper"
    "fixture: wrapper",
  .mk
    "GoLean.Surface.fixtureWrappedTriple"
    "k=thm|c=wrapper"
    "fixture: wrapper",
  .mk
    "GoLean.Surface.goSpecC_of_goSpec"
    "k=thm|c=open"
    "allowlisted: the sequential→pool conservation transfer (∀-program; method)",
  .mk
    "GoLean.Surface.goSpecT_terminates_and_post"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: kit lemma about the GoSpecT composite, whose own content carries the termination half; method-adjacent, reviewed at gen-5",
  .mk
    "GoLean.Surface.goSpec_of_triple_progressRel"
    "k=thm|c=open"
    "allowlisted: generic assembly lemma (triple ∧ progress → spec; ∀-program; method)",
  .mk
    "GoLean.Surface.goldenFuncSpec"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form; completion content: goldenTerminatesNormally (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.goldenSpec"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form (def-wrapper type, statement-TCB architecture); completion content: goldenTerminatesNormally + goldenTotalReadout (TotalPins); predates the completion-pin doctrine, reviewed at gen-5 manifest creation",
  .mk
    "GoLean.Surface.goldenSpecC"
    "k=thm|c=app|GoSpecC(t=Array.toList.{0} (Prod.{0, 0} GoLean.Typ…#13362422619442653803;f=GoLean.GoCore.Program.funcs GoLean.Iris.…#8094514145150069613;m=GoLean.GoCore.Program.methods GoLean.Iri…#8238353381965989613;e=GoLean.Surface.outEnv;p=GoLean.Surface.goldenDriver)|pin=GoLean.Surface.goldenTerminatesNormallyC|pinkey=e=GoLean.Surface.outEnv;s=GoLean.Surface.goldenOut;p=GoLean.Surface.goldenDriver"
    "paired-exact",
  .mk
    "GoLean.Surface.goldenTriple"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form (triple half of goldenSpec); completion content: goldenTerminatesNormally (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.quorumAckedIndexFuncSpec2"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated GoFuncSpec2 statement-form with designated readout twin quorumAckedIndexReturnsTwelveTrue; NO seeded completion pin exists for its callsite driver — recorded honest gap, predates the doctrine",
  .mk
    "GoLean.Surface.quorumOneKnownFuncSpec"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form; completion content: quorumOneKnownTerminatesNormally + quorumOneKnownTotalReadout (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.quorumOneKnownMeetsSpec"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form; completion content: quorumOneKnownTerminatesNormally (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.quorumOneKnownNotEleven"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated unconditional NEGATIVE readout twin (not itself a completion claim); the family's completion content: quorumOneKnownTerminatesNormally (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.quorumThreeAllFuncSpec"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form; completion content: quorumThreeAllTerminatesNormally + quorumThreeAllTotalReadout (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.quorumThreeAllMeetsSpec"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form; completion content: quorumThreeAllTerminatesNormally (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.quorumThreeAllNotTwelve"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated unconditional NEGATIVE readout twin; the family's completion content: quorumThreeAllTerminatesNormally (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.recoverFuncSpec"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated sequential statement-form; completion content: recoverTerminatesNormally + recoverTotalReadout (TotalPins); reviewed at gen-5",
  .mk
    "GoLean.Surface.summitStatement_holds"
    "k=thm|c=wrapper"
    "paired-with-stated-delta: designated summit composite over the quorum family; completion content included via the family's TotalPins twins; reviewed at gen-5"
]

end GoLean.Iris.Audit
