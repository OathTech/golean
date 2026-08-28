import GoLeanProofs.Surface
import GoLean.GoCore.MultiStreams
import GoLeanProofs.Specs.GooseParityTargets
import GoLeanProofs.Specs.ImportedGooseSelectTricky
import GoLeanProofs.Specs.ImportedGooseMuxer
import GoLeanProofs.Specs.ImportedGooseActris

/-!
# The curated channel-exemplar certificates (spec-parity slice 4)

The charter's flagship comparisons — the SELECT-TRICKY TRIO, MUXER,
DSP — over the staleness-guarded pinned lowerings (ci step 3a2; this
header's "1c5" was the stale pre-renumber label, corrected at slice
6), at the SEEDED ∀-schedule strength the slice design note takes
(`docs/2026-08-10_gospecc-decomposition.md` §6, option (a), with the
frame-quantified `GoSpecC` gap recorded PER ROW in the manifest —
`docs/spec-parity-r3-manifest.md` feature class 3, together with each
row's measured upstream proof status at perennial @ 43d4efa).

Per program, five kernel-checked FUEL-GENERAL theorems (the fork/join
idiom, regeneralized at slice 6 — the fuel-independence lift): the
`allStreamsOkPool` certificate in the `∃N, ∀ fuel ≥ N` form (its
kernel evidence is the per-row `<row>Cert<bound>` literal at the
shipped bound, lifted by `allStreamsOkPool_mono`), the ∀-schedule
verdict readout (every choice stream — schedules and data latitude
together — completes at main's `.normal` with the oracle's exact
observable, same `∃N, ∀ fuel ≥ N` form), the no-deadlock and no-race
first-order corollaries at ALL fuels (below the bound a truncated run
classifies `.fuelOut`, never `.deadlock`/`.raceDetected` —
`execProgLoop_le`, matrix §7.2's truth-equivalence argument
machine-checked), and `TerminatesNormallyC`. Fuel is no longer an
axis of any of the five statements. Every statement is
interpreter-vocabulary (no Iris, no relation — this module imports
neither). The verdict values, in the rows' order below
(trio, muxer async/client, dsp: 1/1/1/"async"/"Hello, World!"/42), are
the same observables the R1 differential rows pin against `go run`.

Seeded strength, stated honestly (both directions, manifest-recorded;
upstream-model wording corrected at the S4 audit round — the first
form said "an untested model", compressing away a distinction this
repo's own research note records): these quantify EVERY modeled
schedule from the concrete TotalPins-style seed — totality + verdict +
deadlock/race-refusal-freedom on the differentially tested `execProg`
— but carry NO frame quantifier. Upstream's Iris triples are
heap-general partial-correctness `NotStuck` WPs; their channel
semantics is the goose TRANSLATION of a hand-written Go model package
that IS well tested in Go (a 24-test suite incl. direct side-by-side
comparisons with real Go channels, run in upstream CI; the six rows'
programs also have upstream Go tests) — but the Rocq/GooseLang model
itself and the translation step are executed by no test. No ordering
is claimed.

The shared derivations (`chanCert_*`) are thin generic wrappers over
`execProgLoop_ok_of_allStreamsOkPool`/`execProgLoop_mono` plus the
slice-6 pair `execProgLoop_le`/`allStreamsOkPool_mono`; they are
convention-free and are hoisting CANDIDATES for a general home at
curation (kept local this slice — the P-S3-1 lesson: moving statement
machinery is a deliberate step, not a side effect).
-/

-- SCAFFOLD LABEL (plan §2d grandfather; outsider-audit R1, G-BIND fix round 2026-08-28 [AGENT]):
-- this file's `Terminates`-class content rides the `allStreamsOk` decide+kernel route —
-- fuel-bounded enumeration on pinned seeds, GRANDFATHERED for the pre-corpus pilots and BANNED
-- for new members; retirement condition: re-proved through G-TOTAL when the program is
-- re-specced, or retired with the gallery-row cleanup.

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

namespace GoLean.ImportedGoose

set_option maxRecDepth 1000000

/-! ## The seeded-certificate kit (generic; hoisting candidates) -/

/-! `chanSeed`/`intCell0`/`cellIsInt` and the dsp row's
`dspDriver`/`dspEnv`/`dspSeed` MOVED to the def-only
`Specs/GooseParityTargets.lean` at the D3 designation (user ruling
2026-08-10): the designated `dspCert`/`dspAllSchedules` statements
reference them, so they must live in the Comparator Challenge's
trusted closure, which this theorem-carrying module must not join
(the F4 def-only-hoist discipline — the P-S4-4 move, now made).
`strCell0`/`cellIsStr` (muxer-only) deliberately stay here. -/

/-- String harness cell (empty string seed). -/
abbrev strCell0 : HeapCell := ⟨some .string, .string GoString.empty⟩

/-- The verdict readout: the harness cell holds exactly the string. -/
def cellIsStr (v : GoString) : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.string w) => w == v
  | _ => false

/-- The ∀-schedule verdict readout at EVERY fuel past the
certificate's bound, generically (the `execProgLoop_mono` lift —
slice 6's fuel-independence regeneralization; the per-row statements
package this as the `∃N, ∀ fuel ≥ N` form `TerminatesNormallyC`
uses). -/
theorem chanCert_allSchedules {post : ExecState → Bool} {fuel : Nat}
    {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    ∀ fuel', fuel ≤ fuel' → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel' env σ₀ ch prog = .ok (.normal σf, ch')
          ∧ post σf = true := by
  intro fuel' hle ch
  obtain ⟨σf, ch', hrun, hpost⟩ :=
    execProgLoop_ok_of_allStreamsOkPool hcert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hle, hpost⟩

/-- NO modeled schedule AT ANY FUEL deadlocks, generically: past the
certificate's bound by `execProgLoop_mono`; below it by
`execProgLoop_le` — a sub-bound truncation of a completed run
classifies `.ok` or `.fuelOut`, never `.deadlock` (matrix §7.2's
truth-equivalence argument, now the machine-checked proof). -/
theorem chanCert_noDeadlock {post : ExecState → Bool} {fuel : Nat}
    {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    ∀ (fuel' : Nat) (ch : Choices),
      execProg fuel' env σ₀ ch prog ≠ .error .deadlock := by
  intro fuel' ch hcontra
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool hcert ch
  have hcontra' : execProgLoop fuel'
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} ch = .error .deadlock := hcontra
  rcases Nat.le_total fuel fuel' with hle | hle
  · rw [execProgLoop_mono hrun hle] at hcontra'
    cases hcontra'
  · rcases execProgLoop_le hrun hle with hok | hfo
    · rw [hok] at hcontra'; cases hcontra'
    · rw [hfo] at hcontra'; simp at hcontra'

/-- NO modeled schedule AT ANY FUEL trips the race detector,
generically (same two-lemma split as `chanCert_noDeadlock`). -/
theorem chanCert_noRace {post : ExecState → Bool} {fuel : Nat}
    {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    ∀ (fuel' : Nat) (ch : Choices),
      execProg fuel' env σ₀ ch prog ≠ .error .raceDetected := by
  intro fuel' ch hcontra
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool hcert ch
  have hcontra' : execProgLoop fuel'
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} ch = .error .raceDetected := hcontra
  rcases Nat.le_total fuel fuel' with hle | hle
  · rw [execProgLoop_mono hrun hle] at hcontra'
    cases hcontra'
  · rcases execProgLoop_le hrun hle with hok | hfo
    · rw [hok] at hcontra'; cases hcontra'
    · rw [hfo] at hcontra'; simp at hcontra'

/-- Concurrent normal-pinned termination, generically (one bound for
every stream, lifted to all larger fuels by `execProgLoop_mono`). -/
theorem chanCert_terminatesNormallyC {post : ExecState → Bool}
    {fuel : Nat} {env : LocalEnv} {σ₀ : ExecState} {prog : Stmt}
    (hcert : allStreamsOkPool post fuel
      ⟨#[.exec prog env .stop], σ₀, 0⟩ {} = true) :
    TerminatesNormallyC env σ₀ prog := by
  refine ⟨fuel, fun fuel' hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool hcert ch
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
non-blocking probes that must never rendezvous): the kernel
certificate at the shipped bound 200 (true measured minimum 86 —
S6-audit re-measure; the '100' this line first carried was a
doubling-search round point, not a minimum) — the kernel evidence the
fuel-general bundle below lifts. -/
theorem nbNotReadyCert200 :
    allStreamsOkPool (cellIsInt 1) 200
      ⟨#[.exec nbNotReadyDriver stEnv .stop], stSeed, 0⟩ {} = true := by
  decide +kernel

/-- The fuel-general certificate (slice 6, `allStreamsOkPool_mono`):
the `∃N, ∀ fuel ≥ N` form `TerminatesNormallyC` uses — fuel is no
longer an axis of the statement. -/
theorem nbNotReadyCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool (cellIsInt 1) fuel
        ⟨#[.exec nbNotReadyDriver stEnv .stop], stSeed, 0⟩ {} = true :=
  ⟨200, fun _ h => allStreamsOkPool_mono nbNotReadyCert200 h⟩

theorem nbNotReadyAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel stEnv stSeed ch nbNotReadyDriver
          = .ok (.normal σf, ch') ∧ cellIsInt 1 σf = true :=
  ⟨200, chanCert_allSchedules nbNotReadyCert200⟩

theorem nbNotReadyNoDeadlock : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel stEnv stSeed ch nbNotReadyDriver ≠ .error .deadlock :=
  chanCert_noDeadlock nbNotReadyCert200

theorem nbNotReadyNoRace : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel stEnv stSeed ch nbNotReadyDriver ≠ .error .raceDetected :=
  chanCert_noRace nbNotReadyCert200

theorem nbNotReadyTerminatesNormallyC :
    TerminatesNormallyC stEnv stSeed nbNotReadyDriver :=
  chanCert_terminatesNormallyC nbNotReadyCert200

/-- `select_nb_guaranteed_ready` (upstream Qed; the closed-channel
receive is guaranteed, the default must be unreachable): the kernel
certificate at the shipped bound 200 (true measured minimum 65 —
S6-audit re-measure; '100' was a round search point). -/
theorem nbGuaranteedReadyCert200 :
    allStreamsOkPool (cellIsInt 1) 200
      ⟨#[.exec nbGuaranteedReadyDriver stEnv .stop], stSeed, 0⟩ {}
      = true := by
  decide +kernel

/-- Fuel-general certificate (slice 6). -/
theorem nbGuaranteedReadyCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool (cellIsInt 1) fuel
        ⟨#[.exec nbGuaranteedReadyDriver stEnv .stop], stSeed, 0⟩ {}
        = true :=
  ⟨200, fun _ h => allStreamsOkPool_mono nbGuaranteedReadyCert200 h⟩

theorem nbGuaranteedReadyAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel stEnv stSeed ch nbGuaranteedReadyDriver
          = .ok (.normal σf, ch') ∧ cellIsInt 1 σf = true :=
  ⟨200, chanCert_allSchedules nbGuaranteedReadyCert200⟩

theorem nbGuaranteedReadyNoDeadlock : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel stEnv stSeed ch nbGuaranteedReadyDriver
      ≠ .error .deadlock :=
  chanCert_noDeadlock nbGuaranteedReadyCert200

theorem nbGuaranteedReadyNoRace : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel stEnv stSeed ch nbGuaranteedReadyDriver
      ≠ .error .raceDetected :=
  chanCert_noRace nbGuaranteedReadyCert200

theorem nbGuaranteedReadyTerminatesNormallyC :
    TerminatesNormallyC stEnv stSeed nbGuaranteedReadyDriver :=
  chanCert_terminatesNormallyC nbGuaranteedReadyCert200

/-- `select_nb_full_buffer_not_ready` (upstream Qed; the non-blocking
send on a full buffer must take default): the kernel certificate at
the shipped bound 200 (true measured minimum 71 — S6-audit
re-measure; '100' was a round search point). -/
theorem nbFullBufferCert200 :
    allStreamsOkPool (cellIsInt 1) 200
      ⟨#[.exec nbFullBufferDriver stEnv .stop], stSeed, 0⟩ {} = true := by
  decide +kernel

/-- Fuel-general certificate (slice 6). -/
theorem nbFullBufferCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool (cellIsInt 1) fuel
        ⟨#[.exec nbFullBufferDriver stEnv .stop], stSeed, 0⟩ {} = true :=
  ⟨200, fun _ h => allStreamsOkPool_mono nbFullBufferCert200 h⟩

theorem nbFullBufferAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel stEnv stSeed ch nbFullBufferDriver
          = .ok (.normal σf, ch') ∧ cellIsInt 1 σf = true :=
  ⟨200, chanCert_allSchedules nbFullBufferCert200⟩

theorem nbFullBufferNoDeadlock : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel stEnv stSeed ch nbFullBufferDriver ≠ .error .deadlock :=
  chanCert_noDeadlock nbFullBufferCert200

theorem nbFullBufferNoRace : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel stEnv stSeed ch nbFullBufferDriver
      ≠ .error .raceDetected :=
  chanCert_noRace nbFullBufferCert200

theorem nbFullBufferTerminatesNormallyC :
    TerminatesNormallyC stEnv stSeed nbFullBufferDriver :=
  chanCert_terminatesNormallyC nbFullBufferCert200

end ChannelSelectTricky

/-! ## Feature class 3, rows 4–5: muxer (`Async` — no upstream lemma;
`Client` — upstream `wp_Client` Qed, channel_dsp.v:172) -/

namespace ChannelMuxer

abbrev asyncDriver : Stmt := .call #[.var "r"] ⟨"goleanAsync"⟩ #[]
abbrev clientDriver : Stmt := .call #[.var "r"] ⟨"goleanClient"⟩ #[]

abbrev muxEnv : LocalEnv := [[("r", .base ⟨0⟩)]]
abbrev muxSeed : ExecState := chanSeed muxerLowered strCell0

/-- `Async` (buffered cap-1 handoff joined by a receive): the kernel
certificate at the shipped bound 400 (true measured minimum 140 —
S6-audit re-measure; '200' was a round search point). -/
theorem asyncCert400 :
    allStreamsOkPool (cellIsStr (GoString.fromLeanString "async")) 400
      ⟨#[.exec asyncDriver muxEnv .stop], muxSeed, 0⟩ {} = true := by
  decide +kernel

/-- Fuel-general certificate (slice 6). -/
theorem asyncCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool (cellIsStr (GoString.fromLeanString "async")) fuel
        ⟨#[.exec asyncDriver muxEnv .stop], muxSeed, 0⟩ {} = true :=
  ⟨400, fun _ h => allStreamsOkPool_mono asyncCert400 h⟩

theorem asyncAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel muxEnv muxSeed ch asyncDriver = .ok (.normal σf, ch')
          ∧ cellIsStr (GoString.fromLeanString "async") σf = true :=
  ⟨400, chanCert_allSchedules asyncCert400⟩

theorem asyncNoDeadlock : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel muxEnv muxSeed ch asyncDriver ≠ .error .deadlock :=
  chanCert_noDeadlock asyncCert400

theorem asyncNoRace : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel muxEnv muxSeed ch asyncDriver ≠ .error .raceDetected :=
  chanCert_noRace asyncCert400

theorem asyncTerminatesNormallyC :
    TerminatesNormallyC muxEnv muxSeed asyncDriver :=
  chanCert_terminatesNormallyC asyncCert400

/-- `Client` (the unbuffered request/response round-trip against the
`Serve` loop; the server is left parked at main's exit — the leaked
goroutine is inside the modeled envelope): the kernel certificate at
the shipped bound 800 (true measured minimum 308 — S6-audit
re-measure; '400' was a round search point). -/
theorem clientCert800 :
    allStreamsOkPool
      (cellIsStr (GoString.fromLeanString "Hello, World!")) 800
      ⟨#[.exec clientDriver muxEnv .stop], muxSeed, 0⟩ {} = true := by
  decide +kernel

/-- Fuel-general certificate (slice 6). -/
theorem clientCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool
        (cellIsStr (GoString.fromLeanString "Hello, World!")) fuel
        ⟨#[.exec clientDriver muxEnv .stop], muxSeed, 0⟩ {} = true :=
  ⟨800, fun _ h => allStreamsOkPool_mono clientCert800 h⟩

theorem clientAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel muxEnv muxSeed ch clientDriver = .ok (.normal σf, ch')
          ∧ cellIsStr (GoString.fromLeanString "Hello, World!") σf = true :=
  ⟨800, chanCert_allSchedules clientCert800⟩

theorem clientNoDeadlock : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel muxEnv muxSeed ch clientDriver ≠ .error .deadlock :=
  chanCert_noDeadlock clientCert800

theorem clientNoRace : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel muxEnv muxSeed ch clientDriver ≠ .error .raceDetected :=
  chanCert_noRace clientCert800

theorem clientTerminatesNormallyC :
    TerminatesNormallyC muxEnv muxSeed clientDriver :=
  chanCert_terminatesNormallyC clientCert800

end ChannelMuxer

/-! ## Feature class 3, row 6: dsp (`DSPExample`, Actris 2.0 prog3 —
upstream `wp_DSPExample` Qed, channel_dsp.v:57) -/

namespace ChannelActris

/-- `DSPExample` (the pointer handoff over an unbuffered channel, the
write-back, the signal rendezvous, the deref — 42): the kernel
certificate at the shipped bound 400 (true measured minimum 195 —
S6-audit re-measure; '200' was a round search point). -/
theorem dspCert400 :
    allStreamsOkPool (cellIsInt 42) 400
      ⟨#[.exec dspDriver dspEnv .stop], dspSeed, 0⟩ {} = true := by
  decide +kernel

/-- Fuel-general certificate — DESIGNATED (D3 user ruling 2026-08-10:
the fuel-free form ONLY joins the designated set; `dspCert400` below
stays undesignated kernel evidence). -/
theorem dspCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool (cellIsInt 42) fuel
        ⟨#[.exec dspDriver dspEnv .stop], dspSeed, 0⟩ {} = true :=
  ⟨400, fun _ h => allStreamsOkPool_mono dspCert400 h⟩

/-- ∀-schedule verdict readout — DESIGNATED (D3 user ruling
2026-08-10, fuel-free form). -/
theorem dspAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel dspEnv dspSeed ch dspDriver = .ok (.normal σf, ch')
          ∧ cellIsInt 42 σf = true :=
  ⟨400, chanCert_allSchedules dspCert400⟩

theorem dspNoDeadlock : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel dspEnv dspSeed ch dspDriver ≠ .error .deadlock :=
  chanCert_noDeadlock dspCert400

theorem dspNoRace : ∀ (fuel : Nat) (ch : Choices),
    execProg fuel dspEnv dspSeed ch dspDriver ≠ .error .raceDetected :=
  chanCert_noRace dspCert400

theorem dspTerminatesNormallyC :
    TerminatesNormallyC dspEnv dspSeed dspDriver :=
  chanCert_terminatesNormallyC dspCert400

end ChannelActris

end GoLean.ImportedGoose
