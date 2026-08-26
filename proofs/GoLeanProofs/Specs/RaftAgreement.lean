import GoLeanProofs.Specs.TwinProgram
import GoLean.GoCore.StepFn

/-!
# T1 — conditioned agreement over the choice-driven raft twin: THE
STATEMENTS (campaign Arc 1; constitution §2.1, realized per
`docs/2026-08-22_campaign-arc1-statement-design.md`)

These are the PINNED STATEMENT SHAPES — `Prop` definitions, not
theorems; the campaign proves them (Arcs 2–4) and they are QUEUED for
[USER] designation (§3.2). Everything here is first-order over the
interpreter: `runProgramM` (globals seeded, `$pkginit` run, then the
entry function — exactly `native-json-run`'s wiring) applied to the
pinned lowering `twinLowered`, quantified over the raw choice stream
and fuel. No Iris, no relation, no accelerator (§3.1).

THE ABOUTNESS SENTENCE (read this to know what the theorems claim):
`twinChoiceVerdict` is the choice-driven n=3 RawNode twin — real
etcd-io/raft at the recorded pin plus the itemised subject deltas —
delivering its message multiset in an order drawn from Go's own
map-iteration latitude (the machine's `mapIter` choice site), with
the harness's S1–S3 checker (election safety; log/apply agreement
under the §2.2-item-4 projection; apply monotonicity, loud on
unmodeled entry types) run at every apply/claim step INSIDE the
program, and S4 as the stopping condition. Its observable is five
ints: violations, claims, committed, complete, floor. T1 says: under
EVERY delivery order and EVERY fuel, a completing run recorded no
violation — `violations = 0`. PRECISION (landing fix round,
2026-08-26): the violation counter is incremented at TWELVE sites in
the subject (twin-lib.go), of which five are the S1–S3 checker
proper and SEVEN are harness-liveness/error guards (harvest/drain
quiescence bounds, storage-call failures, the unexpected-snapshot
refusal). `violations = 0` therefore asserts the checker held AND
every harness guard stayed silent — the per-site census with each
guard's discharge route is census item T1-V of the T1
open-obligation census (`docs/campaign-arc4-log.md`, fix-round
entry). The earlier sentence here ("a completing run's checker
recorded nothing") understated this. The witness says: some delivery
order completes with the exercise floor met — so T1 is not vacuous.
The v1 fine print (constitution §2.2): reliable-first network,
bundled harvest, deterministic single-election client (term-1
exercise; richer drivers are witness-family strengthenings).
-/

namespace GoLean.Examples.RaftTwin

open GoLean.GoCore GoLean.GoCore.Machine

/-- The twin's run, as the statement reads it: `native-json-run`'s
program wiring (`runProgramM`: seed globals → `$pkginit` → the entry
function), at the pinned lowering, entry `twinChoiceVerdict`, no
arguments. -/
def twinRun (fuel : Nat) (ch : Choices) : Except GoError Result :=
  runProgramM fuel twinLowered "twinChoiceVerdict" #[] ch

/-- **T1 — conditioned agreement** (constitution §2.1, the base end):
for ALL choice streams and ALL fuel, a completing run has a zero
violation count — the in-program S1–S3 checker held at every step. -/
def AgreementT1 : Prop :=
  ∀ (fuel : Nat) (ch : Choices) (r : Result),
    twinRun fuel ch = .ok r →
    r.values[0]? = some (.int 0 .int)

/-- **The completion witness** (§2.1's non-vacuity twin): some stream
and fuel complete with the exercise floor met (`complete = 1`,
`floor = 1` — all commands committed on every node, ≥1 claim). -/
def CompletionWitness : Prop :=
  ∃ (fuel : Nat) (ch : Choices) (r : Result),
    twinRun fuel ch = .ok r
    ∧ r.values[3]? = some (.int 1 .int)
    ∧ r.values[4]? = some (.int 1 .int)

/-! ## The verdict decoder (wave α, S4 — readout/aboutness ONLY)

`TwinVerdict.ofResult` names the harness's five observable ints so
docstrings and corollaries can speak the harness's vocabulary
("violations", "floor") instead of positional `values[i]?`. It is
**NOT part of the pinned statements above**: `AgreementT1` and
`CompletionWitness` read `r.values` positionally, byte-for-byte as
before, and designation (when it happens) covers those definitions
verbatim — the decoder is a labeled window onto the same five ints,
with `ofResult_violations` pinning that the label points at the
position the statement reads. -/

/-- The twin harness's decoded verdict: the five observable ints in
the order `twinChoiceVerdict` returns them (the aboutness sentence's
"five ints"). -/
structure TwinVerdict where
  violations : Int
  claims : Int
  committed : Int
  complete : Int
  floor : Int
  deriving Repr, DecidableEq

/-- Read `values[i]` as a machine int, kind forgotten. Fail closed. -/
private def intAt (r : Result) (i : Nat) : Option Int :=
  match r.values[i]? with
  | some (.int v _) => some v
  | _ => none

/-- Decode a run's `Result` into the named verdict. Fail closed:
five positions, each a machine int, or `none`. -/
def TwinVerdict.ofResult (r : Result) : Option TwinVerdict := do
  let violations ← intAt r 0
  let claims ← intAt r 1
  let committed ← intAt r 2
  let complete ← intAt r 3
  let floor ← intAt r 4
  pure { violations, claims, committed, complete, floor }

/-- The decoder is faithful to the position `AgreementT1` pins: a
decoded verdict's `violations` field IS the int at `values[0]`. -/
theorem TwinVerdict.ofResult_violations {r : Result} {vd : TwinVerdict}
    (h : TwinVerdict.ofResult r = some vd) :
    ∃ k, r.values[0]? = some (.int vd.violations k) := by
  unfold TwinVerdict.ofResult at h
  cases h0 : intAt r 0 with
  | none => rw [h0] at h; cases h
  | some v0 =>
      rw [h0] at h
      unfold intAt at h0
      cases hv : r.values[0]? with
      | none => rw [hv] at h0; cases h0
      | some gv =>
          rw [hv] at h0
          cases gv with
          | int v k =>
              refine ⟨k, ?_⟩
              cases h1 : intAt r 1 with
              | none => rw [h1] at h; cases h
              | some v1 =>
                rw [h1] at h
                cases h2 : intAt r 2 with
                | none => rw [h2] at h; cases h
                | some v2 =>
                  rw [h2] at h
                  cases h3 : intAt r 3 with
                  | none => rw [h3] at h; cases h
                  | some v3 =>
                    rw [h3] at h
                    cases h4 : intAt r 4 with
                    | none => rw [h4] at h; cases h
                    | some v4 =>
                      rw [h4] at h
                      cases h
                      injection h0 with h0'
                      subst h0'
                      simpa using hv
          | unit => cases h0
          | bool _ => cases h0
          | float _ _ => cases h0
          | string _ => cases h0
          | addr _ => cases h0
          | nil => cases h0
          | interface _ _ => cases h0
          | struct _ _ => cases h0
          | array _ => cases h0
          | slice _ => cases h0
          | map _ => cases h0
          | mapData _ => cases h0
          | chan _ => cases h0
          | chanData _ _ _ => cases h0
          | funcVal _ _ => cases h0
          | syncData _ => cases h0

/-- Aboutness corollary (first-order readout in the decoder's
vocabulary): under `AgreementT1`, every completing run that decodes
has a zero `violations` field. -/
theorem agreementT1_verdict (hT1 : AgreementT1) {fuel : Nat}
    {ch : Choices} {r : Result} {vd : TwinVerdict}
    (hrun : twinRun fuel ch = .ok r)
    (hdec : TwinVerdict.ofResult r = some vd) :
    vd.violations = 0 := by
  obtain ⟨k, hv⟩ := TwinVerdict.ofResult_violations hdec
  have h0 := hT1 fuel ch r hrun
  rw [hv] at h0
  simp only [Option.some.injEq, GoValue.int.injEq] at h0
  exact h0.1

end GoLean.Examples.RaftTwin
