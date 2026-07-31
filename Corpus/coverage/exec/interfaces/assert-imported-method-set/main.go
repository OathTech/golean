package main

// The dynamic type of a boxed IMPORTED named type has no declaration on
// the wire, so its METHOD SET is unknown to the machine — not empty.
// Answering the satisfaction check `false` from an empty method table is a
// definite answer derived from no information: the comma-ok form returned
// the wrong boolean and the panicking form fabricated a `missing method`
// panic on a program Go runs to completion (pre-merge audit 2026-07-31,
// finding 8 — the same hazard BUG-008 closed for comparability, left open
// in the satisfaction polarity).
//
// `*strings.Builder` really does implement `fmt.Stringer`. Both cases are
// RED pins: the machine must fail CLOSED (`unsupported`) until imported
// named types carry declarations, never answer.

import (
	"fmt"
	"strings"
)

func assertImportedMethodSetCommaOk() int {
	var p *strings.Builder
	var x any = p
	_, ok := x.(fmt.Stringer)
	if ok {
		return 1
	}
	return 0
}

func assertImportedMethodSetPanicForm() int {
	var p *strings.Builder
	var x any = p
	_ = x.(fmt.Stringer)
	return 7
}
