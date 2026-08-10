import GoLeanProofs.Surface
import GoLean.GoCore.MultiStreams
import GoLeanProofs.Specs.ImportedGooseSelectTricky
import GoLeanProofs.Specs.ImportedGooseMuxer
import GoLeanProofs.Specs.ImportedGooseActris

/-!
# The curated channel-exemplar certificates (spec-parity slice 4)

The charter's flagship comparisons — the SELECT-TRICKY TRIO, MUXER,
DSP — over the staleness-guarded pinned lowerings (ci step 1c5), at
the SEEDED ∀-schedule strength the slice design note takes
(`docs/2026-08-10_gospecc-decomposition.md` §6, option (a), with the
frame-quantified `GoSpecC` gap recorded PER ROW in the manifest —
`docs/spec-parity-r3-manifest.md` feature class 3, together with each
row's measured upstream proof status at perennial @ 43d4efa).

Per program, five kernel-checked theorems (the fork/join idiom): the
`allStreamsOkPool` certificate, the ∀-schedule verdict readout (every
choice stream — schedules and data latitude together — completes at
main's `.normal` with the oracle's exact observable), the no-deadlock
and no-race first-order corollaries, and `TerminatesNormallyC`. Every
statement is interpreter-vocabulary (no Iris, no relation — this
module imports neither). The verdict values (1/1/1/42/"async"/"Hello,
World!") are the same observables the R1 differential rows pin against
`go run`.

Seeded strength, stated honestly (both directions, manifest-recorded):
these quantify EVERY modeled schedule from the concrete TotalPins-style
seed — totality + verdict + deadlock/race-refusal-freedom on the
differentially tested `execProg` — but carry NO frame quantifier;
upstream's Iris triples are heap-general partial-correctness `NotStuck`
WPs over an untested model. No ordering is claimed.

The shared derivations (`chanCert_*`) are thin generic wrappers over
`execProgLoop_ok_of_allStreamsOkPool`/`execProgLoop_mono`; they are
convention-free and are hoisting CANDIDATES for a general home at
curation (kept local this slice — the P-S3-1 lesson: moving statement
machinery is a deliberate step, not a side effect).
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

namespace GoLean.ImportedGoose

set_option maxRecDepth 1000000

/-! ## The seeded-certificate kit (generic; hoisting candidates) -/

/-- The TotalPins-style seed with a caller-typed harness cell at base
address 0 (the string-returning muxer wrappers need a string cell; the
int convention is `importedSeed`'s). -/
def chanSeed (p : Program) (cell : HeapCell) : ExecState :=
  { types := p.typeDefs.toList,
    functions := p.funcs,
    methods := p.methods,
    heap := [(.base ⟨0⟩, cell)],
    nextAddr := 1 }

/-- Int harness cell / seed / readout (the imported convention). -/
abbrev intCell0 : HeapCell := ⟨some (.int .int), .int 0 .int⟩

/-- String harness cell (empty string seed). -/
abbrev strCell0 : HeapCell := ⟨some .string, .string GoString.empty⟩

/-- The verdict readout: the harness cell holds exactly `int v`. -/
def cellIsInt (v : Int) : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.int w .int) => w == v
  | _ => false

/-- The verdict readout: the harness cell holds exactly the string. -/
def cellIsStr (v : GoString) : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.string w) => w == v
  | _ => false

/-- The ∀-schedule verdict readout, generically from a certificate. -/
theorem chanCert_allSchedules {post : ExecState → Bool} {fuel : Nat}
    {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    ∀ ch : Choices, ∃ (σf : ExecState) (ch' : Choices),
      execProg fuel env σ₀ ch prog = .ok (.normal σf, ch')
        ∧ post σf = true := by
  intro ch
  obtain ⟨σf, ch', hrun, hpost⟩ :=
    execProgLoop_ok_of_allStreamsOkPool hcert ch
  exact ⟨σf, ch', hrun, hpost⟩

/-- No modeled schedule deadlocks, generically from a certificate. -/
theorem chanCert_noDeadlock {post : ExecState → Bool} {fuel : Nat}
    {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    ∀ ch : Choices,
      execProg fuel env σ₀ ch prog ≠ .error .deadlock := by
  intro ch hcontra
  obtain ⟨σf, ch', hrun, -⟩ := chanCert_allSchedules hcert ch
  rw [hrun] at hcontra
  cases hcontra

/-- No modeled schedule trips the race detector, generically. -/
theorem chanCert_noRace {post : ExecState → Bool} {fuel : Nat}
    {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    ∀ ch : Choices,
      execProg fuel env σ₀ ch prog ≠ .error .raceDetected := by
  intro ch hcontra
  obtain ⟨σf, ch', hrun, -⟩ := chanCert_allSchedules hcert ch
  rw [hrun] at hcontra
  cases hcontra

/-- Concurrent normal-pinned termination, generically (one bound for
every stream, lifted to all larger fuels by `execProgLoop_mono`). -/
theorem chanCert_terminatesNormallyC {post : ExecState → Bool}
    {fuel : Nat} {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    TerminatesNormallyC env σ₀ prog := by
  refine ⟨fuel, fun fuel' hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ := chanCert_allSchedules hcert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

/-! ## Feature class 3, rows 1–3: the select-tricky trio
(upstream `channel_select_tricky_examples.v` @ 43d4efa — all three
upstream-Qed; per-row lines in the manifest) -/

namespace ChannelSelectTricky

/-- Driver: `r = goleanSelectNbNotReady()` at the int seed. -/
abbrev nbNotReadyDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanSelectNbNotReady"⟩ #[]

abbrev nbGuaranteedReadyDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanSelectNbGuaranteedReady"⟩ #[]

abbrev nbFullBufferDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanSelectNbFullBufferNotReady"⟩ #[]

abbrev stEnv : LocalEnv := [[("r", .base ⟨0⟩)]]
abbrev stSeed : ExecState := chanSeed selectTrickyLowered intCell0

/-- `select_nb_not_ready` (upstream Qed, two goroutines, two
non-blocking probes that must never rendezvous): the certificate. -/
theorem nbNotReadyCert :
    allStreamsOkPool (cellIsInt 1) 200
      ⟨#[.exec nbNotReadyDriver stEnv .stop], stSeed, 0⟩ {} = true := by
  decide +kernel

theorem nbNotReadyAllSchedules : ∀ ch : Choices,
    ∃ (σf : ExecState) (ch' : Choices),
      execProg 200 stEnv stSeed ch nbNotReadyDriver
        = .ok (.normal σf, ch') ∧ cellIsInt 1 σf = true :=
  chanCert_allSchedules nbNotReadyCert

theorem nbNotReadyNoDeadlock : ∀ ch : Choices,
    execProg 200 stEnv stSeed ch nbNotReadyDriver ≠ .error .deadlock :=
  chanCert_noDeadlock nbNotReadyCert

theorem nbNotReadyNoRace : ∀ ch : Choices,
    execProg 200 stEnv stSeed ch nbNotReadyDriver ≠ .error .raceDetected :=
  chanCert_noRace nbNotReadyCert

theorem nbNotReadyTerminatesNormallyC :
    TerminatesNormallyC stEnv stSeed nbNotReadyDriver :=
  chanCert_terminatesNormallyC nbNotReadyCert

/-- `select_nb_guaranteed_ready` (upstream Qed; the closed-channel
receive is guaranteed, the default must be unreachable). -/
theorem nbGuaranteedReadyCert :
    allStreamsOkPool (cellIsInt 1) 200
      ⟨#[.exec nbGuaranteedReadyDriver stEnv .stop], stSeed, 0⟩ {}
      = true := by
  decide +kernel

theorem nbGuaranteedReadyAllSchedules : ∀ ch : Choices,
    ∃ (σf : ExecState) (ch' : Choices),
      execProg 200 stEnv stSeed ch nbGuaranteedReadyDriver
        = .ok (.normal σf, ch') ∧ cellIsInt 1 σf = true :=
  chanCert_allSchedules nbGuaranteedReadyCert

theorem nbGuaranteedReadyNoDeadlock : ∀ ch : Choices,
    execProg 200 stEnv stSeed ch nbGuaranteedReadyDriver
      ≠ .error .deadlock :=
  chanCert_noDeadlock nbGuaranteedReadyCert

theorem nbGuaranteedReadyNoRace : ∀ ch : Choices,
    execProg 200 stEnv stSeed ch nbGuaranteedReadyDriver
      ≠ .error .raceDetected :=
  chanCert_noRace nbGuaranteedReadyCert

theorem nbGuaranteedReadyTerminatesNormallyC :
    TerminatesNormallyC stEnv stSeed nbGuaranteedReadyDriver :=
  chanCert_terminatesNormallyC nbGuaranteedReadyCert

/-- `select_nb_full_buffer_not_ready` (upstream Qed; the non-blocking
send on a full buffer must take default). -/
theorem nbFullBufferCert :
    allStreamsOkPool (cellIsInt 1) 200
      ⟨#[.exec nbFullBufferDriver stEnv .stop], stSeed, 0⟩ {} = true := by
  decide +kernel

theorem nbFullBufferAllSchedules : ∀ ch : Choices,
    ∃ (σf : ExecState) (ch' : Choices),
      execProg 200 stEnv stSeed ch nbFullBufferDriver
        = .ok (.normal σf, ch') ∧ cellIsInt 1 σf = true :=
  chanCert_allSchedules nbFullBufferCert

theorem nbFullBufferNoDeadlock : ∀ ch : Choices,
    execProg 200 stEnv stSeed ch nbFullBufferDriver ≠ .error .deadlock :=
  chanCert_noDeadlock nbFullBufferCert

theorem nbFullBufferNoRace : ∀ ch : Choices,
    execProg 200 stEnv stSeed ch nbFullBufferDriver
      ≠ .error .raceDetected :=
  chanCert_noRace nbFullBufferCert

theorem nbFullBufferTerminatesNormallyC :
    TerminatesNormallyC stEnv stSeed nbFullBufferDriver :=
  chanCert_terminatesNormallyC nbFullBufferCert

end ChannelSelectTricky

/-! ## Feature class 3, rows 4–5: muxer (`Async` — no upstream lemma;
`Client` — upstream `wp_Client` Qed, channel_dsp.v:172) -/

namespace ChannelMuxer

abbrev asyncDriver : Stmt := .call #[.var "r"] ⟨"goleanAsync"⟩ #[]
abbrev clientDriver : Stmt := .call #[.var "r"] ⟨"goleanClient"⟩ #[]

abbrev muxEnv : LocalEnv := [[("r", .base ⟨0⟩)]]
abbrev muxSeed : ExecState := chanSeed muxerLowered strCell0

/-- `Async` (buffered cap-1 handoff joined by a receive): the
certificate. -/
theorem asyncCert :
    allStreamsOkPool (cellIsStr (GoString.fromLeanString "async")) 400
      ⟨#[.exec asyncDriver muxEnv .stop], muxSeed, 0⟩ {} = true := by
  decide +kernel

theorem asyncAllSchedules : ∀ ch : Choices,
    ∃ (σf : ExecState) (ch' : Choices),
      execProg 400 muxEnv muxSeed ch asyncDriver = .ok (.normal σf, ch')
        ∧ cellIsStr (GoString.fromLeanString "async") σf = true :=
  chanCert_allSchedules asyncCert

theorem asyncNoDeadlock : ∀ ch : Choices,
    execProg 400 muxEnv muxSeed ch asyncDriver ≠ .error .deadlock :=
  chanCert_noDeadlock asyncCert

theorem asyncNoRace : ∀ ch : Choices,
    execProg 400 muxEnv muxSeed ch asyncDriver ≠ .error .raceDetected :=
  chanCert_noRace asyncCert

theorem asyncTerminatesNormallyC :
    TerminatesNormallyC muxEnv muxSeed asyncDriver :=
  chanCert_terminatesNormallyC asyncCert

/-- `Client` (the unbuffered request/response round-trip against the
`Serve` loop; the server is left parked at main's exit — the leaked
goroutine is inside the modeled envelope): the certificate. -/
theorem clientCert :
    allStreamsOkPool
      (cellIsStr (GoString.fromLeanString "Hello, World!")) 800
      ⟨#[.exec clientDriver muxEnv .stop], muxSeed, 0⟩ {} = true := by
  decide +kernel

theorem clientAllSchedules : ∀ ch : Choices,
    ∃ (σf : ExecState) (ch' : Choices),
      execProg 800 muxEnv muxSeed ch clientDriver = .ok (.normal σf, ch')
        ∧ cellIsStr (GoString.fromLeanString "Hello, World!") σf = true :=
  chanCert_allSchedules clientCert

theorem clientNoDeadlock : ∀ ch : Choices,
    execProg 800 muxEnv muxSeed ch clientDriver ≠ .error .deadlock :=
  chanCert_noDeadlock clientCert

theorem clientNoRace : ∀ ch : Choices,
    execProg 800 muxEnv muxSeed ch clientDriver ≠ .error .raceDetected :=
  chanCert_noRace clientCert

theorem clientTerminatesNormallyC :
    TerminatesNormallyC muxEnv muxSeed clientDriver :=
  chanCert_terminatesNormallyC clientCert

end ChannelMuxer

/-! ## Feature class 3, row 6: dsp (`DSPExample`, Actris 2.0 prog3 —
upstream `wp_DSPExample` Qed, channel_dsp.v:57) -/

namespace ChannelActris

abbrev dspDriver : Stmt := .call #[.var "r"] ⟨"goleanDSPExample"⟩ #[]

abbrev dspEnv : LocalEnv := [[("r", .base ⟨0⟩)]]
abbrev dspSeed : ExecState := chanSeed actrisLowered intCell0

/-- `DSPExample` (the pointer handoff over an unbuffered channel, the
write-back, the signal rendezvous, the deref — 42): the certificate. -/
theorem dspCert :
    allStreamsOkPool (cellIsInt 42) 400
      ⟨#[.exec dspDriver dspEnv .stop], dspSeed, 0⟩ {} = true := by
  decide +kernel

theorem dspAllSchedules : ∀ ch : Choices,
    ∃ (σf : ExecState) (ch' : Choices),
      execProg 400 dspEnv dspSeed ch dspDriver = .ok (.normal σf, ch')
        ∧ cellIsInt 42 σf = true :=
  chanCert_allSchedules dspCert

theorem dspNoDeadlock : ∀ ch : Choices,
    execProg 400 dspEnv dspSeed ch dspDriver ≠ .error .deadlock :=
  chanCert_noDeadlock dspCert

theorem dspNoRace : ∀ ch : Choices,
    execProg 400 dspEnv dspSeed ch dspDriver ≠ .error .raceDetected :=
  chanCert_noRace dspCert

theorem dspTerminatesNormallyC :
    TerminatesNormallyC dspEnv dspSeed dspDriver :=
  chanCert_terminatesNormallyC dspCert

end ChannelActris

end GoLean.ImportedGoose
