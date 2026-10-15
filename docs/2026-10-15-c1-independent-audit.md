# Independent C1 implementation audit

Review completed 2026-10-15 by the independent implementation subagent. Its
brief identified project goals, sources and areas of interest, with unrestricted
investigation and no prescribed verdict. It read the upstream task brief and
followed operation, boundary and transition dependencies. No source edits.


Reviewed implementation: **55ad72493061b59363e846341380a9edce12a2de**. Independently read all seven reviewed source blobs from this exact commit with git show and compared SHA-256 hashes to the copies used for independent compilation and replay: zero mismatches. Working tree was clean. Read the final stage record; its implementation scope and descriptions of this review match the evidence.

**Findings: none.** This verdict covers both bounded local modes, concrete failure checks, the public facade and its new acceptance clients, including arbitrary malformed states, exact result causes, successful labels, guard/fuel priorities, separate failure consultations, and all-alternative refusal/fatal transfer. It does not independently rerun the full differential CI or downstream Iris development; the author records those respective validation scopes and limits. Consultation fidelity is structural: error equality alone is not a trace-instrumentation theorem, and the document accurately distinguishes it from structured replay. No whole-program all-outcome adequacy, observer completeness, locality, sequentialization or concurrency result follows from C1.

Reproduce the independently exercised public checks at this pin after building the project:

```sh
LEAN_NUM_THREADS=2 capped lake env lean Tests/RelationalOutcomes.lean
LEAN_NUM_THREADS=2 capped lake env leanchecker \
  GoLean.GoCore.RelationalOperationCheck \
  GoLean.GoCore.RelationalOperationFailure \
  GoLean.GoCore.RelationalLocalExecution \
  GoLean.GoCore.RelationalOperationFailureSound \
  GoLean.GoCore.RelationalLocalExecutionSound \
  GoLean.Relational Tests.RelationalOutcomes
```

For an isolated rebuild, create reviewer-local directories reflecting GoLean/GoCore and Tests; set LEAN_PATH to that root, then compile the five sources in the above order with `capped lake env lean -o <scratch/module.olean> <source.lean>`, followed by GoLean/Relational.lean and Tests/RelationalOutcomes.lean. Keep LEAN_NUM_THREADS=2. Use the same LEAN_PATH for the replay command. The additional initialization control is reproduced below; consultation controls are retained in Tests/RelationalOutcomes.lean.


## Additional initialization control

Save this as disposable `.tmp/InitControls.lean` and run
`LEAN_NUM_THREADS=2 capped lake env lean .tmp/InitControls.lean` at the reviewed
pin after building. These are the exact independently compiled statements:

```lean
import GoLean.Relational
open GoLean GoLean.GoCore GoLean.GoCore.Relational Local
private def a (v : GoValue) (s : Store) : State := ⟨.retV v (.stmtOpK (.print false) 0 [] [] [] .stop), s⟩
example (ctx : ProgramCtx) (s : Store) (ch : Choices) :
    Correspondence.driver .initialization ctx 0 (a (.bool true) s) ch = .error initializationStop := rfl
example (ctx : ProgramCtx) (s : Store) (ch : Choices) :
    Correspondence.driver .initialization ctx 0 (a .nil s) ch = .error .fuelOut := rfl
example (ctx : ProgramCtx) (s : Store) (ch : Choices) :
    Correspondence.driver .initialization ctx 1 (a .nil s) ch =
      .error (.unsupported "print of a nil pointer/interface/slice/map/chan/func operand: gc prints an ADDRESS (0x0 / (0x0,0x0) / [0/0]0x0), which the machine does not model — refused by name") := rfl
example (ctx : ProgramCtx) (s : Store) :
    OperationFailure ctx (a .nil s) []
      (.refusal (.unsupported "print of a nil pointer/interface/slice/map/chan/func operand: gc prints an ADDRESS (0x0 / (0x0,0x0) / [0/0]0x0), which the machine does not model — refused by name")) := .failed
```

## Disposition

No final implementation findings require fixes or waivers. The earlier
constraint review's fabricated-record counterexample and premature unseq
projection issue are dispositioned individually in the
[C1 handoff](2026-10-14_relational-outcome-completeness.md#review-dispositions).
The documented structural-consultation scope is retained: the executable
returns no failure trace, and error-cause equality is not presented as one.
Full differential CI is the author's separate checked evidence; it is not
misattributed to the independent reviewer.
