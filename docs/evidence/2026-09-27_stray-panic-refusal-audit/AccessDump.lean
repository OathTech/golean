import GoLean.ChoiceTrace
open GoLean GoCore GoCore.Machine

/-! Audit scratch (stray-panic refusal audit, 2026-09-27): per case, the
init-phase `stepFn` labels and the pool's `StepEvent.trace` labels, in step
order, folded into a hash; plus status, step count and output. Run with
the SAME wire batch against main's and the candidate's GoLean. -/

def mix (h : UInt64) (s : String) : UInt64 := mixHash h (hash s)

partial def initLoop (ctx : ProgramCtx) (ch : Choices) : Nat → Store → Config → UInt64 → Nat →
    Except (String × UInt64 × Nat) (Store × UInt64 × Nat × Choices)
  | 0, _, _, h, n => .error ("fuel-out(init)", h, n)
  | fuel+1, σ, c, h, n =>
    match c with
    | .next .stop => .ok (σ, h, n, ch)
    | .blockedSend _ _ _ | .blockedRecv _ _ _ _ _ | .blockedSelect _ _ _ => .error ("deadlock(init)", h, n)
    | _ =>
    match stepFn ctx σ c ch with
    | .error e => .error (s!"{e.status}: {e.message}", h, n)
    | .ok (c', σ', ch', tr) => initLoop ctx ch' fuel σ' c' (mix h (reprStr tr)) (n+1)

partial def poolLoop (ctx : ProgramCtx) : Nat → MultiConfig → RaceState → Choices → UInt64 → Nat → String →
    String × UInt64 × Nat × String
  | fuel, m, r, ch, h, n, acc =>
    if m.threads.isEmpty then ("internal-empty", h, n, acc) else
    match m.panicMsg? with
    | some msg => (s!"panic: {msg}", h, n, acc)
    | none =>
      let doStep (ch : Choices) : String × UInt64 × Nat × String :=
        match fuel with
        | 0 => ("fuel-out", h, n, acc)
        | fuel+1 =>
          match stepMulti ctx m ch with
          | .error e => (s!"{e.status}: {e.message}", h, n, acc)
          | .ok (m', ch', ev) =>
            let h' := mix h (s!"{ev.who}|" ++ reprStr ev.trace)
            match raceUpdate ev m' r with
            | .error e => (s!"{e.status}: {e.message}", h', n+1, acc)
            | .ok r' => poolLoop ctx fuel m' r' ch' h' (n+1) (ev.out.foldl (fun a s => a ++ reprStr s) acc)
      match m.mainOutcome? with
      | some _ =>
        match runnableIdxs ctx m.shared m.threads with
        | [] => ("ok", h, n, acc)
        | _ :: _ =>
          let (pick, ch₁) := Choices.consumeAt .l5ExitWindow 2 ch
          if pick == 0 then ("ok", h, n, acc) else doStep ch₁
      | none =>
        if (runnableIdxs ctx m.shared m.threads).isEmpty then ("deadlock", h, n, acc) else doStep ch

def runCase (wire fn : String) (args : Array Int) (fuel : Nat) (stream : Choices) : IO String := do
  match ← ChoiceTrace.loadProgram wire with
  | .error e => return s!"LOADERR {e}"
  | .ok program =>
    match CLI.enumSetup program fn (args.map (fun i => GoValue.int i .int)) with
    | .error e => return s!"SETUPERR {e.status}: {e.message}"
    | .ok ep =>
      let r : Except (String × UInt64 × Nat) (Store × UInt64 × Nat × Choices) := match ep.initBody? with
        | none => .ok (ep.σ₀, (7 : UInt64), 0, stream)
        | some body => initLoop ep.ctx stream fuel ep.σ₀ (.exec body [] (.frame [] [] [] [] .stop)) 7 0
      match r with
      | .error (st, h, n) => return s!"INIT {st} steps={n} h={h}"
      | .ok (σ₁, h, n, stream) =>
        match bindParams ep.ctx [] σ₁ ep.func.args.toList ep.args.toList with
        | .error e => return s!"BIND {e.status}"
        | .ok (env, s₂) =>
          match allocDecls ep.ctx env s₂ ep.func.results.toList with
          | .error e => return s!"ALLOC {e.status}"
          | .ok (frameEnv, s₃) =>
            let (st, h, n, out) := poolLoop ep.ctx fuel
              ⟨#[.running (.exec ep.func.body frameEnv (.frame [] [] [] [] .stop)) none], s₃, 0⟩ {} stream h n ""
            return s!"{st} steps={n} h={h} outhash={hash out}"

def main (argv : List String) : IO UInt32 := do
  let batch := argv[0]!
  let fuel := (argv[1]!).toNat!
  for line in (← IO.FS.lines batch) do
    match line.splitOn "\t" with
    | id :: wire :: fn :: argsS :: _ =>
      let args := if argsS == "-" || argsS == "" then #[] else
        ((argsS.splitOn ",").filterMap String.toInt?).toArray
      for (sn, st) in [("default", ([] : Choices)), ("rand1", ChoiceTrace.randomStream 1 4096)] do
        let r ← runCase wire fn args fuel st
        IO.println s!"{id}\t{sn}\t{(r.replace "\n" " ").replace "\t" " "}"
      (← IO.getStdout).flush
    | _ => IO.println s!"BADLINE {line}"
  return 0
