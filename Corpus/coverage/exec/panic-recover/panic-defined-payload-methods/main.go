package main

// Go's `preprintpanics` rewrites a panic payload to `v.Error()` (error) or
// `v.String()` (fmt.Stringer) BEFORE `printpanicval` reaches
// `printanycustomtype`, so only a METHOD-LESS defined type renders as
// `main.T(v)` (pre-merge audit 2026-07-31, finding 3 — the unconditional
// `main.T(v)` arm was a fail-closed → wrong-answer regression). Rendering the
// rewritten form would mean CALLING a method at abort time, which the terminal
// rule cannot do, so the two method-bearing rows are pinned RED (fail closed).

type payloadCode int

func (c payloadCode) Error() string { return "boom" }

type payloadName int

func (n payloadName) String() string { return "strung" }

type payloadPlain int

func panicDefinedErrorPayload() int {
	panic(payloadCode(9))
}

func panicDefinedStringerPayload() int {
	panic(payloadName(3))
}

func panicDefinedPlainPayload() int {
	panic(payloadPlain(7))
}
