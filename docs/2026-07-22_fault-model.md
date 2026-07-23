# The fault model must agree with Go (2026-07-22)

Recorded from design discussion (2026-07-22). Companion to
`docs/2026-07-22_invariant-readout-design.md`; this note is a standing
charter item for the **F4 concurrency note** (TODO.md), which must contain a
fault-model section satisfying it.

## 1. Principle

Separation-logic soundness is **fault-avoiding** ("verified programs don't
go wrong"), so "going wrong" must be a first-class citizen of the semantics
— and for us it must be *Go's* notion of going wrong, pinned by the
differential oracle, not an imported C intuition. Go makes this unusually
tractable: almost all Go faults are **defined, observable behavior** (a
panic prints and exits with code 2; `go run` shows it), so the oracle can
check the fault model, not just the happy path.

## 2. Faults live at two layers — never conflate them

- **Semantics layer:** a panic is *not* a fault; it is a defined transition
  — a value propagates, defers run, `recover` can catch it. `Eval`/`Rel`
  model this faithfully (`.panicked`), and must, because programs recover:
  an unrecovered panic is a program outcome, a recovered one is a normal
  control path. Differentially pinned today by the `panic-recover` exec
  suite (~30 cases: recover-direct, defer-registered-during-unwind,
  panic-typed-nil-recover, defer-arg-during-panic, …) plus the
  semantic-edges bestiary.
- **Spec layer:** *classifying* unrecovered panic as "going wrong" is a
  spec-strength choice: `Progress` counts `.panicked` as stuck (the #24
  scoping), so the soundness statement is **verified ⇒ no unrecovered
  panic** — the Go analogue of memory-safety-fault avoidance. This choice is
  only statable because the layer below represents panics precisely.

## 3. Fail-closed is secretly fault-model integrity

The enforced three-way split —

| class | meaning | owner |
| --- | --- | --- |
| `.panicked` | program fault; Go-defined, oracle-visible | the program |
| `.unsupported` | model incompleteness; never counted either way | us |
| fuel exhaustion | divergence bound | the harness |

— is what keeps `Progress` meaningful. If `unsupported` ever leaked into
"stuck," soundness would claim programs avoid *our implementation gaps*:
false as stated, vacuous as intended. The runner's classification
discipline IS the fault model's integrity check.

## 4. The gap list (each item needs guardrail cases BEFORE machinery)

1. **Unrecoverable runtime failures are a distinct class from panics.**
   Concurrent map access is a **fatal error** (no `recover`); the runtime
   deadlock detector ("all goroutines are asleep") is another class. When
   goroutines arrive these need their own corpus suites first,
   guardrails-first.
2. **Fault identity, not fault existence.** The runner must compare *which*
   fault occurred (message/class), not just "both sides exited nonzero" — a
   case that panics in Go but deadlocks in Eval agreeing on "failure" is a
   hidden wrong answer (fail-closed doctrine applied to faults).
3. **Races — the one genuinely UB-shaped region of Go.** The memory model
   permits real corruption for races on multi-word values. An interleaving
   `Rel` gives races *defined* behavior, i.e. over-promises relative to Go.
   Confinement: CSL-style verification yields DRF, and Go's memory model
   promises SC for DRF programs — so the mismatch is confined to programs
   the logic cannot verify. **Soundness claims must carry this scope
   condition explicitly**, not silently.
4. **Resource exhaustion idealization.** Stack overflow / OOM are real Go
   faults an idealized semantics does not model. Standard idealization —
   but it must be a written scope statement, not an assumption.
5. **Non-faults C intuition mislabels.** Signed overflow wraps; it does not
   fault. The corpus must pin these negatives too, so we don't inherit
   faults Go doesn't have.

## 5. Charter for the F4 note

F4's fault-model section must give: the taxonomy (panic / fatal error /
deadlock / race-scope / exhaustion-idealization), which classes `Rel`
represents, which the oracle can discriminate, and the guardrail suite that
pins each class — before any goroutine machinery is built.
