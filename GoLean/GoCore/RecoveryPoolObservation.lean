import GoLean.GoCore.AbortObservation
import GoLean.GoCore.ProgramTrace

/-! Observational instrumentation of the shipped pool driver. `Pool.front`
is already proved equal to that driver's pre-fuel classification. Every
transition, detector update, event output and choice is the original one.
Metadata is retained only from a selected thread's actual abort transition. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine
open GoLean.Semantics

/-- The `repanicCollapse` pick an abort event RECORDED (landing chunk L3):
`[]` at a bound-1 consult (the forced pick 0), the one labeled record at
bound 2; any other picks shape is not an abort event's and yields `none`
(fail closed — the observer never guesses a pick). -/
def abortEventPick? (event : StepEvent) : Option Nat :=
  match event.picks with
  | [] => some 0
  | [⟨.repanicCollapse, _, pick⟩] => some pick
  | _ => none

def stepAbortRecord? (before after : MultiConfig) (event : StepEvent) (message : String) :
    Option AbortRecord :=
  match event.action, before.threads[event.who]?, after.threads[event.who]? with
  | .aborted, some (.running c _), some (.aborted actual) =>
    if actual != message then none else
      match c.abort?, abortEventPick? event with
      | some (first, rest), some pick => match abortMsg before.shared first rest pick with
        | .ok rendered => if rendered != message then none else abortRecord? c
        | .error _ => none
      | _, _ => none
  | _, _, _ => none

def attachAbort (before after : MultiConfig) (event : StepEvent)
    (result : Pool.Result × Option AbortRecord) : Pool.Result × Option AbortRecord :=
  (result.1, match result.2 with
    | some record => some record
    | none => match result.1.2 with
      | .error (.panic message) => stepAbortRecord? before after event message
      | _ => none)

theorem stepAbortRecord?_some {before after event message record}
    (h : stepAbortRecord? before after event message = some record) :
    ∃ (c : Config) (flag : Option ChoiceSite) (first : PanicEntry) (rest : List PanicEntry)
      (pick : Nat),
      event.action = .aborted ∧ before.threads[event.who]? = some (.running c flag) ∧
      after.threads[event.who]? = some (.aborted message) ∧ c.abort? = some (first, rest) ∧
      abortEventPick? event = some pick ∧
      first :: rest = record.chain ∧ abortMsg before.shared first rest pick = .ok message := by
  fun_cases stepAbortRecord? before after event message <;>
    simp_all [stepAbortRecord?]
  rename_i c flag actual first rest pick rendered hafter hbefore haction hactual hevpick query
    render hrender
  obtain ⟨first', rest', query', _, _, chain⟩ := abortRecord?_some h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (query.symm.trans query'))
  exact ⟨first, rest, ⟨rfl, rfl⟩, chain, render⟩

/-- The abort event the pool's tombstone arm emits records exactly the pick
its consult drew: `consumeAtE`'s `[]` at bound 1 is the forced 0, its
labeled record at bound 2 carries the pick — so `abortEventPick?` reads the
consult's own answer back (landing chunk L3). -/
theorem abortEventPick?_consumeAtE (i : Nat) (bound : Nat) (ch : Choices) (out : List GoString) :
    abortEventPick? ⟨i, .aborted, (Choices.consumeAtE .repanicCollapse bound ch).2.2, out⟩
      = some (Choices.consumeAtE .repanicCollapse bound ch).1 := by
  unfold Choices.consumeAtE
  by_cases hb : bound ≤ 1
  · rw [Choices.consumeAt_le_one hb]
    simp [abortEventPick?, hb]
  · simp [abortEventPick?, hb]

def execPoolWithAbort : Nat → MultiConfig → RaceState → Choices → GoString →
    Pool.Result × Option AbortRecord
  | fuel, m, r, ch, out =>
    match Pool.front m ch with
    | .error e => ((out, .error e), none)
    | .ok (.inl result) => ((out, .ok result), none)
    | .ok (.inr next) => match fuel with
      | 0 => ((out, .error .fuelOut), none)
      | fuel + 1 => match stepMulti m next with
        | .error e => ((out, .error e), none)
        | .ok (m', ch', event) => match raceUpdate m.shared m.threads event m' r with
          | .error e => ((out, .error e), none)
          | .ok r' => attachAbort m m' event
            (execPoolWithAbort fuel m' r' ch' (event.out.foldl GoString.append out))

/-- Exact all-input erasure to the shipped output-folding driver, including
main-exit picks, race refusals, output prefixes and zero-fuel classifications. -/
theorem execPoolWithAbort_erasure (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (out : GoString) :
    (execPoolWithAbort fuel m r ch out).1 = execProgLoopOut fuel m r ch out := by
  fun_induction execPoolWithAbort fuel m r ch out <;>
    rw [Pool.unfold_driver] <;> simp_all [attachAbort]

inductive PoolPrefix : Nat → MultiConfig → RaceState → Choices → GoString →
    MultiConfig → RaceState → Choices → GoString → Prop where
  | refl : PoolPrefix 0 m r ch out m r ch out
  | step {n m r ch out next m' ch' event r' final finalRace finalCh finalOut} :
      Pool.front m ch = .ok (.inr next) →
      stepMulti m next = .ok (m', ch', event) →
      raceUpdate m.shared m.threads event m' r = .ok r' →
      PoolPrefix n m' r' ch' (event.out.foldl GoString.append out) final finalRace finalCh finalOut →
      PoolPrefix (n + 1) m r ch out final finalRace finalCh finalOut

/-- A provenance carrier made exclusively from actual driver premises.
The `here` constructor records the selected abort transition and the actual
remaining driver execution; `later` retains every preceding transition. -/
inductive PoolAbortWitness : Nat → MultiConfig → RaceState → Choices → GoString →
    Pool.Result → AbortRecord → Prop where
  | here {n m r ch out next m' ch' event r' finalOut message record} :
      Pool.front m ch = .ok (.inr next) →
      stepMulti m next = .ok (m', ch', event) →
      raceUpdate m.shared m.threads event m' r = .ok r' →
      stepAbortRecord? m m' event message = some record →
      Pool.Run n m' r' ch' (event.out.foldl GoString.append out) (finalOut, .error (.panic message)) →
      PoolAbortWitness (n + 1) m r ch out (finalOut, .error (.panic message)) record
  | later {n m r ch out next m' ch' event r' result record} :
      Pool.front m ch = .ok (.inr next) →
      stepMulti m next = .ok (m', ch', event) →
      raceUpdate m.shared m.threads event m' r = .ok r' →
      PoolAbortWitness n m' r' ch' (event.out.foldl GoString.append out) result record →
      PoolAbortWitness (n + 1) m r ch out result record

theorem PoolAbortWitness.run {fuel m r ch out result record}
    (h : PoolAbortWitness fuel m r ch out result record) : Pool.Run fuel m r ch out result := by
  induction h with
  | here front step race _ run => exact .step front step race run
  | later front step race _ ih => exact .step front step race ih

theorem PoolAbortWitness.panic_result {fuel m r ch out result record}
    (h : PoolAbortWitness fuel m r ch out result record) :
    ∃ finalOut message, result = (finalOut, .error (.panic message)) := by
  induction h with
  | here => exact ⟨_, _, rfl⟩
  | later _ _ _ _ ih => exact ih

/-- Flatten the record's provenance into the exact driver prefix, selected
abort transition and remaining actual driver run. All streams, detector
states and output prefixes are retained, including main-exit picks. -/
theorem PoolAbortWitness.reached {fuel m r ch out result record}
    (h : PoolAbortWitness fuel m r ch out result record) :
    ∃ (spent remaining : Nat) (before : MultiConfig) (beforeRace : RaceState)
      (beforeCh : Choices) (beforeOut : GoString) (next : Choices)
      (after : MultiConfig) (afterCh : Choices) (event : StepEvent) (afterRace : RaceState)
      (finalOut : GoString) (message : String),
      spent + (remaining + 1) = fuel ∧ PoolPrefix spent m r ch out before beforeRace beforeCh beforeOut ∧
      Pool.front before beforeCh = .ok (.inr next) ∧
      stepMulti before next = .ok (after, afterCh, event) ∧
      raceUpdate before.shared before.threads event after beforeRace = .ok afterRace ∧
      stepAbortRecord? before after event message = some record ∧
      Pool.Run remaining after afterRace afterCh (event.out.foldl GoString.append beforeOut)
        (finalOut, .error (.panic message)) ∧ result = (finalOut, .error (.panic message)) := by
  induction h with
  | @here n m r ch out next m' ch' event r' finalOut message record front step race metadata run =>
    exact ⟨0, n, m, r, ch, out, next, m', ch', event, r', finalOut, message,
      by simp, .refl, front, step, race, metadata, run, rfl⟩
  | later front step race _ ih =>
    obtain ⟨spent, remaining, before, beforeRace, beforeCh, beforeOut, next,
      after, afterCh, event, afterRace, finalOut, message, bound, hprefix,
      hfront, hstep, hrace, metadata, run, result⟩ := ih
    exact ⟨spent + 1, remaining, before, beforeRace, beforeCh, beforeOut, next,
      after, afterCh, event, afterRace, finalOut, message, by omega,
      .step front step race hprefix, hfront, hstep, hrace, metadata, run, result⟩

theorem execPoolWithAbort_witness {fuel m r ch out result record}
    (h : execPoolWithAbort fuel m r ch out = (result, some record)) :
    PoolAbortWitness fuel m r ch out result record := by
  fun_induction execPoolWithAbort fuel m r ch out with
  | case1 => simp at h
  | case2 => simp at h
  | case3 => simp at h
  | case4 => simp at h
  | case5 => simp at h
  | case6 =>
    rename_i m r ch out next front fuel m' ch' event step r' race ih
    generalize hr : execPoolWithAbort fuel m' r' ch' (event.out.foldl GoString.append out) = observed at h ih
    obtain ⟨actual, metadata⟩ := observed
    cases metadata with
    | some head =>
      have he : actual = result ∧ head = record := by simpa [attachAbort] using h
      obtain ⟨rfl, rfl⟩ := he
      exact .later front step race (ih rfl)
    | none =>
      obtain ⟨finalOut, actual⟩ := actual
      cases actual with
      | ok value => simp [attachAbort] at h
      | error e =>
        cases e with
        | fuelOut => simp [attachAbort] at h
        | refusal reason => simp [attachAbort] at h
        | terminal term =>
          cases term with
          | panic message =>
            have he : (finalOut, Except.error (.panic message)) = result ∧
                stepAbortRecord? m m' event message = some record := by simpa [attachAbort] using h
            obtain ⟨rfl, hm⟩ := he
            apply PoolAbortWitness.here front step race hm
            apply Pool.run_iff.mp
            have erasure := execPoolWithAbort_erasure fuel m' r' ch'
              (event.out.foldl GoString.append out)
            rw [hr] at erasure
            exact erasure.symm
          | fatal message => simp [attachAbort] at h
          | deadlock => simp [attachAbort] at h
          | raceDetected => simp [attachAbort] at h

end GoLean.GoCore.RecoveryRuntime
