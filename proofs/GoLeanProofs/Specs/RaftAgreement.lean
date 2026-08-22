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
EVERY delivery order and EVERY fuel, a completing run's checker
recorded nothing — `violations = 0`. The witness says: some delivery
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

end GoLean.Examples.RaftTwin
