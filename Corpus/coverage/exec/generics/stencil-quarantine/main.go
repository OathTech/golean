package main

import "fmt"

// FRONTIER PIN (slice 6): the H-3 residual, measured as a case. Method
// STENCILS — a method of a generic type at one receiver instantiation
// — have NO per-declaration quarantine (mono.go, flushTypeInsts): one
// unlowerable stencil still refuses the WHOLE package export, so this
// package's innocent sibling subject is RED for someone else's
// declaration. That is exactly the defect shape H-3 fixed for ordinary
// methods (docs/bugfix-arc-log.md §H-3), pinned here so the frontier
// row (ledger FR row, sequential build queue) has its guardrail before
// any implementation exists. The instantiation s6box[int] is USED, so
// the stencil set flushes; render's fmt.Sprintf is the unlowerable
// construct (the same trigger as the H-3 suite).

type s6box[T any] struct{ v T }

func (b s6box[T]) render() string { return fmt.Sprintf("%v", b.v) }

func stencilSibling() int {
	b := s6box[int]{v: 3}
	return b.v * 3 // 9 — never calls render; red only because the export refuses whole
}

func main() {
	stencilSibling()
}
