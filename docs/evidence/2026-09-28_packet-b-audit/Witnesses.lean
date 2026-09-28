-- producer: scripts/capped lake env lean .tmp/Witnesses.lean (this file copied from .tmp/; output in witnesses-out.txt)
import GoLean
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

def ctx0 : ProgramCtx := ProgramCtx.ofTables #[] #[]
def arrStore : Store := { heap := #[.value (.array 0 .int) (.array #[])] }
def badLoc : Loc := .index (.base ⟨0⟩) 5

def shape {α : Type} : Except Stop (Config × α) → String
  | .ok (.panicking _ _, _) => "ok panicking (Go panic as a CONFIGURATION, unwinds)"
  | .ok _ => "ok (other)"
  | .error (.terminal (.panic m)) => s!"ERROR panic terminal: {m}"
  | .error (.terminal (.fatal m)) => s!"error fatal: {m}"
  | .error (.terminal t) => s!"error terminal (other)"
  | .error (.refusal (.internal m)) => s!"error refusal internal: {m}"
  | .error (.refusal (.stuck m)) => s!"error refusal stuck: {m}"
  | .error (.refusal (.unsupported m)) => s!"error refusal unsupported: {m}"
  | .error .fuelOut => "error fuelOut"

-- W1: integer divide by zero at the strict apply: Go panic arrives as .ok (.panicking ..)
#eval shape (stepFn ctx0 {} (.retV (.int 0 .int) (.strictK .div [.int 1 .int] [] [] .stop)) [])
-- W2: the stray-panic lane's S6 witness: a refusal, not a panic terminal
#eval shape (stepFn ctx0 arrStore (.evalE (.var "x") [[("x", badLoc)]] .stop) [])
-- W3: the abort configuration: the ONLY place the panic terminal is raised
#eval shape (stepFn ctx0 {} (.panicking [panicEntry "boom"] .stop) [])
-- W4: sync misuse (unlock of unlocked mutex): fatal
#eval shape (stepFn ctx0 { heap := #[.value (.sync .mutex) (.syncData (.mutex false))] }
  (.retV (.addr (.base ⟨0⟩)) (.syncStK .unlock [] [] [] .stop)) [])
-- (no W5 eval: the sequential stepFn refuses a `go` spawn by source, StepFn.lean:807/:814)
-- W6: .next .stop: refused (why NoRefusal excludes zero-cost endpoints)
#eval shape (stepFn ctx0 {} (.next .stop) [])

-- the theorem applied to W1's configuration (abort? = none) -- no panic terminal for any tape
example (ch : Choices) (t : String) :
    stepFn ctx0 {} (.retV (.int 0 .int) (.strictK .div [.int 1 .int] [] [] .stop)) ch
      ≠ .error (.terminal (.panic t)) := stepFn_no_stray_panic rfl

-- a WRITTEN-OUT pin (BridgeSet header convention) is checked against the _stmt body by delta:
example : ∀ (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices),
    Prefix ctx 0 s c ch [] s c ch := @prefix_refl
