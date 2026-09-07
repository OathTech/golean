package main

// Valid-UTF-8 and first-line panic rendering (landing chunk L3,
// docs/2026-09-07_land-panic-text-tape.md §2.1; the nine unicode/newline
// subjects are the typed-consumer sprint's ff7173dd, credited). gc writes a
// string payload's RAW bytes (`printindented`), a TAB after every LF, and
// the `[recovered…]` suffix after the WHOLE payload — so the first abort
// line of a multi-line payload is the bytes before its first LF, with no
// suffix. The invalid-UTF-8 subjects pin BUG-004 item 3's residue under
// landing decision D5 (no byte channel — an [AGENT] default at the lane's
// tip, RULED [USER] 2026-09-07 at merge train round 24, «Go ahead with the
// merge», relayed by the [AGENT] coordinator, the merge-ask naming D5 among
// the four items ratified): a first line that is not valid
// UTF-8 REFUSES by name (red rows); a first line that is valid renders
// even when a later line is not (invalid-after-lf); the recovered VALUE of
// an invalid payload is compared in-language (invalid-recovered-value, the
// forced half).
func panicUnicodeTwo()      { panic("é") }
func panicUnicodeThree()    { panic("界") }
func panicUnicodeFour()     { panic("😀") }
func panicUnicodeMixed()    { panic("aé界😀z") }
func panicUnicodeNewline()  { panic("é\n界") }
func panicTrailingNewline() { panic("first\n") }

func panicRecoveredNewline() {
	defer func() {
		_ = recover()
		panic("other")
	}()
	panic("first\nsecond")
}

func panicRecoveredUnicode() {
	defer func() {
		_ = recover()
		panic("other")
	}()
	panic("é")
}

func panicPrintUnicode() {
	print("before\n")
	panic("é")
}

// gc: `panic: a⏎⇥\xff⏎` — the first line is the valid byte `a`; the invalid
// byte is on the second line, which the first-line observation never sees.
// A FIRST-LINE-SCOPE CONTROL, not invalid-UTF-8 coverage (audit fix round
// 2026-09-07, R4d, [AGENT]): the compared observation contains no invalid
// byte on either side — the tail is unmodelled by the machine and
// unobserved by the harness (`docs/2026-07-25_unwinding-arc.md`, the
// 2026-09-07 first-line rule; ledger FR-32). Tagged `first_line_scope`.
func panicInvalidAfterLF() { panic("a\n\xff") }

// gc: `panic: \xffZ⏎` — raw bytes; no String can carry them (RED, BUG-004).
func panicInvalidSingle() { panic("\xffZ") }

// gc: `panic: \xffZ⏎⇥Y⏎` — the FIRST line is invalid (RED, BUG-004).
func panicInvalidFirstLine() { panic("\xffZ\nY") }

// gc: `panic: \xffZ [recovered, repanicked]⏎` — the recovered box passed
// through; the first line is invalid whichever member the collapse pick
// selects, so the refusal is stream-invariant (RED, BUG-004).
func panicInvalidRecoveredEqual() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic("\xffZ")
}

// The forced half beside the red text rows: the recovered VALUE of an
// invalid-UTF-8 payload is the payload, byte for byte (in-language `==`).
func invalidRecoveredValue() (same bool) {
	defer func() {
		r := recover()
		s, ok := r.(string)
		same = ok && s == "\xffZ" && len(s) == 2
	}()
	panic("\xffZ")
}

func main() {}
