import GoLean.NativeToIR
import GoLeanProofs.FastEval.Transfer

/-!
# `fastreplay` — the verified fast replay driver (campaign Arc 2, unit P2R)

Compiled driver that runs a wire program's body on the VERIFIED fast
evaluator (`stepFast`, trie heap) instead of iterating `stepFn`, and
carries the verdict to the interpreter-level equation by the pinned
transfer theorem (`FastEval/Transfer.lean`, `fastRun_transfer_eqb`).
Built for the p2 differential replay (`tools/raftsubject/tracereplay.py
--engine fast`), where `stepFn`'s list heap makes the compiled
interpreter superlinear per step (measured wall ≈ fuel^2.5 on
`probe_and_replicate`; unit P2R log entry).

What a `status: ok` line from this driver MEANS, exactly: every premise
of `fastRun_transfer_eqb` was checked by compiled evaluation —
1. `runProgramSetupM fuel program name #[] [] = .ok (c₀, s₃, locs, ch₁)`
   (the SLOW setup, run directly — the init phase is short, measured
   1,373 steps on the p2 workload);
2. `ExecState.eqb (γF (absState s₃)) s₃ = true` (the γ-anchor — the
   untrusted `absState` conversion is never trusted, only checked);
3. `iterF stepFast steps σF₀ c₀ ch₁ = .ok (.next .stop, σF', ch')`
   with `steps ≤ fuel` — evaluated DIRECTLY, as one whole-run `iterF`
   call at the step count discovered by the chunked loop (audit fix
   round, 2026-08-25: the chunked `runLoop`/`stepUpTo` discovery pass
   is UNTRUSTED machinery for progress emission, the durable record,
   and finding `steps`; nothing downstream reads its final state —
   premise 4's `σF'`/`ch'` come from this direct evaluation, which is
   literally the theorem's premise expression);
4. `loadManyF σF' locs = .ok vs`.
So `runProgramM fuel program name #[] [] = .ok { values := vs }` — the
model verdict — holds by the theorem, whose axioms Audit pins.

WHICH whole-program semantics an ok verdict certifies (audit fix
round, 2026-08-25 — the original claim here was wrong):
`runProgramM` is the SEQUENTIAL entry (`runProgramSetupM` then
`runConfig`). The machine tier this driver replaced (`golean
native-json-run`, still reachable as `tracereplay.py --engine slow`)
computes `runProgramPoolIntsM` — the THREAD-POOL entry
(`runProgramSetupM` then `execProgLoop`). These are DIFFERENT
functions and no bridge lemma between them exists in the repo. Why no
divergence is reachable on the accepted class: every construct on
which the entries could differ — goroutine spawn (`.goStmt` /
`.goCalleeK` / `.goArgsK`), channel ops, select — is refused
fail-closed by `stepFast` (`FastEval/Step.lean`), so any run this
driver accepts is spawn-free and single-threaded under either entry.
That is an ARGUMENT, not a theorem; the bridge lemma (`runProgramM =
runProgramPoolIntsM` on the spawn-free accepted class) is queued in
the campaign arc-2 log as a named follow-on. Until it lands, an ok
verdict certifies the sequential entry, exactly.

Fail-closed: any stub arm of `stepFast` (`fastEval-stub:` /
`fastEval-WIRE:`), anchor mismatch, or non-`.ok` outcome prints an
explicit error observation with the exact step index and exits 1.
Progress + durable record: one JSONL line per chunk to `--record`
(flushed per line), so a killed run shows exactly where it stood —
the mid-job-failure principle; no opaque runs.
-/

namespace GoLean.FastReplay

open Lean GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.FastEval

private def schema : String := "golean-observation-v1"

/-- Mirror of the CLI's `goValueJson` for the observation shapes the
replay harness reads; every OTHER shape refuses loudly (fail closed)
rather than approximating the CLI's full rendering. -/
private def valueJson : GoValue → Except String Json
  | .unit => .ok (Json.mkObj [("tag", Json.str "unit")])
  | .bool value => .ok (Json.mkObj [("tag", Json.str "bool"), ("value", Lean.toJson value)])
  | .int value kind =>
      .ok (Json.mkObj [("tag", Json.str "int"), ("kind", Json.str kind.name),
                       ("value", Lean.toJson value)])
  | .string value =>
      .ok (Json.mkObj [("tag", Json.str "string"), ("bytes", Lean.toJson value.byteNats)])
  | .nil => .ok (Json.mkObj [("tag", Json.str "nil")])
  | other => .error s!"fastreplay: unsupported observation value shape: {repr other}"

private def errorJson (error : GoError) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("schema", Json.str schema),
               ("status", Json.str error.status),
               ("message", Json.str error.message)] ++ extra)

private def cliErrorJson (message : String) : Json :=
  Json.mkObj [("schema", Json.str schema), ("status", Json.str "error"),
              ("message", Json.str message)]

structure Args where
  input : Option String := none
  functionName : Option String := none
  fuel : Nat := 100000000
  chunk : Nat := 250000
  record : Option String := none

private def parseArgs : List String → Args → Except String Args
  | [], args => .ok args
  | "--input" :: path :: rest, args => parseArgs rest { args with input := some path }
  | "--function" :: name :: rest, args => parseArgs rest { args with functionName := some name }
  | "--fuel" :: value :: rest, args =>
      match value.toNat? with
      | some fuel => parseArgs rest { args with fuel }
      | none => .error s!"--fuel: expected a natural number, got {value}"
  | "--chunk" :: value :: rest, args =>
      match value.toNat? with
      | some chunk =>
          if chunk == 0 then .error "--chunk: must be positive"
          else parseArgs rest { args with chunk }
      | none => .error s!"--chunk: expected a natural number, got {value}"
  | "--record" :: path :: rest, args => parseArgs rest { args with record := some path }
  | flag :: _, _ => .error s!"fastreplay: unknown or incomplete option: {flag}"

/-- One durable progress/record line (flushed immediately). -/
private def emitRecord (recOut : Option IO.FS.Handle) (obj : List (String × Json)) : IO Unit := do
  if let some h := recOut then
    h.putStrLn (Json.mkObj obj).compress
    h.flush

/-- The outcome of the chunked fast body run. -/
private inductive RunOutcome where
  /-- Terminal `.next .stop` reached after exactly `steps` fast steps. -/
  | done (steps : Nat) (σF : ExecStateF) (ch : Choices)
  /-- A fast step failed (stub arm, genuine error, …) at 0-based step index. -/
  | failed (atStep : Nat) (error : GoError)
  /-- The `--fuel` budget ran out before the terminal. -/
  | fuelOut (steps : Nat)

/-- Single-step to the exact terminal/failure point inside one chunk
(entered only when a whole-chunk `iterF` refuses — a chunk that crosses
the terminal steps INTO `.next .stop`, which `stepFast` rejects). -/
private def stepUpTo : Nat → Nat → ExecStateF → Config → Choices → RunOutcome
  | 0, used, _, c, _ =>
      match c with
      | .next .stop => .fuelOut used  -- unreachable from the chunk path; honest fallback
      | _ => .failed used (.internal "fastreplay: chunk refinement exhausted without reproducing the refusal")
  | n + 1, used, σF, c, ch =>
      match c with
      | .next .stop => .done used σF ch
      | _ =>
          match stepFast σF c ch with
          | .ok (c', σF', ch') => stepUpTo n (used + 1) σF' c' ch'
          | .error e => .failed used e

/-- The chunked DISCOVERY loop — UNTRUSTED machinery (audit fix round,
2026-08-25): it finds the terminal step count, emits progress, and
writes the durable record. Its final state feeds NOTHING downstream;
`main` re-establishes premise 3 by one direct whole-run `iterF` at the
discovered count (so no lemma about this loop is load-bearing).
`budget` is the REMAINING fuel. Total: `budget` strictly decreases
(each chunk is ≥ 1 step). -/
private def runLoop (recOut : Option IO.FS.Handle) (t0 : Nat) (chunk : Nat) :
    Nat → Nat → ExecStateF → Config → Choices → IO RunOutcome
  | budget, used, σF, c, ch => do
    match c with
    | .next .stop => return .done used σF ch
    | _ =>
      if _hb : budget = 0 then
        return .fuelOut used
      else
        let n := max 1 (min chunk budget)
        match iterF stepFast n σF c ch with
        | .ok (c', σF', ch') => do
            let now ← IO.monoMsNow
            let line := [("stage", Json.str "fast-progress"),
                         ("steps", Lean.toJson (used + n)),
                         ("nextAddr", Lean.toJson σF'.nextAddr),
                         ("elapsedMs", Lean.toJson (now - t0))]
            emitRecord recOut line
            IO.eprintln (Json.mkObj line).compress
            runLoop recOut t0 chunk (budget - n) (used + n) σF' c' ch'
        | .error _ =>
            -- The chunk refused: either it stepped past the terminal or a
            -- real refusal sits inside. Re-walk this chunk one step at a
            -- time from its start to land on the exact point.
            return stepUpTo n used σF c ch
  termination_by budget => budget
  decreasing_by omega

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv {} with
  | .error err => IO.eprintln err; return 2
  | .ok args =>
    match args.input, args.functionName with
    | some input, some functionName => do
      let contents ← IO.FS.readFile input
      let recOut ← args.record.mapM (fun p => do
        if let some d := (System.FilePath.mk p).parent then IO.FS.createDirAll d
        IO.FS.Handle.mk p .append)
      match Lean.Json.parse contents with
      | .error err => IO.println (cliErrorJson s!"{input}: JSON parse error: {err}").compress; return 1
      | .ok json =>
        match GoLean.NativeToIR.decodeProgram json with
        | .error err => IO.println (cliErrorJson s!"{input}: {err}").compress; return 1
        | .ok program => do
          let t0 ← IO.monoMsNow
          -- Premise 1: the slow setup (init phase is short; measured).
          match runProgramSetupM args.fuel program functionName #[] [] with
          | .error err => IO.println (errorJson err [("stage", Json.str "setup")]).compress; return 1
          | .ok (c₀, s₃, locs, ch₁) => do
            emitRecord recOut [("stage", Json.str "setup-ok"),
                            ("heapCells", Lean.toJson s₃.heap.length),
                            ("nextAddr", Lean.toJson s₃.nextAddr)]
            -- Premise 2: the γ-anchor over the untrusted conversion.
            let σF₀ := absState s₃
            if h : ExecState.eqb (γF σF₀) s₃ = true then do
              emitRecord recOut [("stage", Json.str "anchor-ok")]
              -- Step-count discovery (untrusted; premise 3 is checked
              -- directly below at the discovered count).
              match ← runLoop recOut t0 args.chunk args.fuel 0 σF₀ c₀ ch₁ with
              | .done steps _ _ => do
                if steps ≤ args.fuel then
                  -- Premise 3, checked DIRECTLY (audit fix round,
                  -- 2026-08-25): one whole-run `iterF` at the discovered
                  -- step count — literally the theorem's premise
                  -- expression. The chunked discovery pass above
                  -- contributes nothing but `steps` and the progress
                  -- record; the verdict's `σF'`/`ch'` come from HERE.
                  match iterF stepFast steps σF₀ c₀ ch₁ with
                  | .ok (.next .stop, σF', ch') => do
                      let now ← IO.monoMsNow
                      emitRecord recOut [("stage", Json.str "premise3-ok"),
                                         ("steps", Lean.toJson steps),
                                         ("elapsedMs", Lean.toJson (now - t0))]
                      -- Premise 4: the fast readout.
                      match loadManyF σF' locs with
                      | .error err =>
                          IO.println (errorJson err [("stage", Json.str "readout")]).compress
                          return 1
                      | .ok vs =>
                        match vs.mapM valueJson with
                        | .error msg => IO.println (cliErrorJson msg).compress; return 1
                        | .ok vjsons => do
                          let now ← IO.monoMsNow
                          let obs := Json.mkObj [
                            ("schema", Json.str schema),
                            ("status", Json.str "ok"),
                            ("values", Json.arr vjsons.toArray),
                            ("engine", Json.str "fastreplay"),
                            ("steps", Lean.toJson steps),
                            ("fuel", Lean.toJson args.fuel),
                            ("elapsedMs", Lean.toJson (now - t0)),
                            ("transfer", Json.str "GoLean.FastEval.fastRun_transfer_eqb"),
                            ("choicesLeft", Lean.toJson ch'.length)]
                          emitRecord recOut [("stage", Json.str "final"), ("obs", obs)]
                          IO.println obs.compress
                          return 0
                  | _ => do
                      let obs := cliErrorJson
                        "fastreplay: premise-3 direct check failed (whole-run `iterF` at the discovered step count did not reach `.next .stop`) — fail closed"
                      emitRecord recOut [("stage", Json.str "final"), ("obs", obs)]
                      IO.println obs.compress
                      return 1
                else do
                  let obs := cliErrorJson
                    "fastreplay: discovered step count exceeds --fuel — fail closed"
                  emitRecord recOut [("stage", Json.str "final"), ("obs", obs)]
                  IO.println obs.compress
                  return 1
              | .failed atStep err => do
                  let obs := errorJson err [("stage", Json.str "fast-step"),
                                            ("step", Lean.toJson atStep)]
                  emitRecord recOut [("stage", Json.str "final"), ("obs", obs)]
                  IO.println obs.compress
                  return 1
              | .fuelOut steps => do
                  let obs := errorJson .fuelOut [("stage", Json.str "fast-step"),
                                                ("step", Lean.toJson steps)]
                  emitRecord recOut [("stage", Json.str "final"), ("obs", obs)]
                  IO.println obs.compress
                  return 1
            else do
              let obs := cliErrorJson
                "fastreplay: γ-anchor check failed (absState image differs from the setup state) — fail closed"
              emitRecord recOut [("stage", Json.str "final"), ("obs", obs)]
              IO.println obs.compress
              return 1
    | _, _ => IO.eprintln "usage: fastreplay --input <wire.json> --function <name> [--fuel N] [--chunk N] [--record file]"; return 2

end GoLean.FastReplay

/-- Exe entry (`lake build fastreplay`). -/
def main (argv : List String) : IO UInt32 := GoLean.FastReplay.main argv
