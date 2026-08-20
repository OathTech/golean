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
// `*strings.Builder` really does implement `fmt.Stringer`.
//
// STATUS REWRITTEN 2026-08-20 (raft W4.1 audit round, finding B-8 — the
// header below this line said "Both cases are RED pins: the machine must
// fail CLOSED (`unsupported`) ... never answer", and that has been false
// since W4.1 item 2). `strings.Builder` is now MODELED (the E5-T pinned
// mini-`package strings`, `tools/nativefrontend/importedmodel.go`): its
// six methods — `WriteString`/`WriteByte`/`Write`/`String`/`Len`/`Reset`
// — are lowered through the ordinary pipeline under the type's own
// identity, so `*strings.Builder` DOES carry declarations on the wire and
// the satisfaction check has real information to answer from. Both rows
// are therefore GREEN, and green for the right reason: the machine
// answers `true` (comma-ok returns 1, the panicking form returns 7) and
// `go run` agrees. They pin the ANSWER now, not a refusal.
//
// WHAT THE ORIGINAL HAZARD STILL COVERS, unchanged: an imported named
// type with NO declarations on the wire — a `bytes.Buffer`, anything
// outside the modeled set — must still fail CLOSED rather than answer
// `false` from an empty method table. These two rows no longer witness
// that, because their subject stopped being such a type. A fixture over
// a genuinely undeclared imported type is what would witness it; until
// one exists, the polarity is pinned by the frontend's own refusal path
// and not by this file. Do not read these PASSes as covering it.

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
