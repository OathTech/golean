package main

import "reflect"

// FRONTIER PIN (slice 6): the H-3 residual, measured as a case. Method
// STENCILS — a method of a generic type at one receiver instantiation
// — have NO per-declaration quarantine (mono.go, flushTypeInsts): one
// unlowerable stencil still refuses the WHOLE package export, so this
// package's innocent sibling subject is RED for someone else's
// declaration. That is exactly the defect shape H-3 fixed for ordinary
// methods (docs/bugfix-arc-log.md §H-3), pinned here so the frontier
// row (ledger FR row, sequential build queue) has its guardrail before
// any implementation exists. The instantiation s6box[int] is USED, so
// the stencil set flushes; render's reflect.TypeOf is the unlowerable
// construct (the same trigger as the H-3 suite).
//
// WHY `reflect.TypeOf` (JC-17, THIRD pick — audit R4-M-1): the
// unlowerable construct here is load-bearing — it is what makes
// the stencil refuse at all. `fmt.Sprintf` lowered when the W4.1
// desugar landed; `fmt.Sprint` lowered when audit R4-M-1 modeled the
// fixed-arity form. The old text here justified REFUSING fmt.Sprint
// by this fixture's needs — a corpus-scoped refusal inversion (common
// Go kept refused to keep a witness stable); the lesson is to pick
// the cause by structural distance from the modeled envelope, not by
// "currently unmodeled". Reflection is the deep-latitude surface the
// closed-world frontend does not model by doctrine. No eternal
// refusal exists: if reflect ever lowers, this row flips LOUDLY in
// the baseline and must be retargeted again, never let go green.

type s6box[T any] struct{ v T }

func (b s6box[T]) render() string { return reflect.TypeOf(b.v).String() }

func stencilSibling() int {
	b := s6box[int]{v: 3}
	return b.v * 3 // 9 — never calls render; red only because the export refuses whole
}

func main() {
	stencilSibling()
}
