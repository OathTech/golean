package main

import "errors"

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The ABORT report's first line per byte class — the machine's
// `renderPanicPayload` / `stringFirstLine?` against gc's `printpanicval` bytes
// as the harness's `makeAbortView` captures them: DEL / C1, BOM and the line
// separators, the JSON-sensitive bytes, an encoded U+FFFD, the empty string, a
// 4-byte rune then NUL, a long payload, an error payload with NUL / unicode, a
// recovered-then-repanicked payload with DEL / C1. Not rowed, recorded as gaps:
// an invalid first line (BUG-004 item 3 / D5, both sides refuse by name) and a
// DEFINED string type payload (`main.T("…")`: only the int-underlying
// `printanycustomtype` form is pinned — BUG-004 item 2's scope, S12).

func panicDelC1() { panic("a\x7fb\u0085c\u0080") }

func panicBomAndLineSeps() { panic("x\uFEFFy z w") }

func panicJsonSensitive() { panic("q\"b\\s/h<>&'\x08\x0c\x1f") }

func panicEncodedReplacement() { panic("r\xef\xbf\xbds") }

func panicEmptyString() { panic("") }

func panicFourByteThenNul() { panic("😀\x00z") }

func panicLong() {
	s := ""
	for i := 0; i < 50; i++ {
		s += "é0123456789"
	}
	panic(s)
}

func panicErrorNulUnicode() { panic(errors.New("e\x00é\u0085\t")) }

func panicRecoveredDelC1() {
	defer func() {
		_ = recover()
		panic("again\x7f\u0085")
	}()
	panic("first\x7f")
}

func main() {
	panicDelC1()
}
