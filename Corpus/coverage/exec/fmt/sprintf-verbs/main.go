package main

// fmt.Sprintf conformance pins (raft W4.1 item 2 — H-6, the Q3 OPTION 1
// ruling: a modeled Sprintf SUBSET over the measured verb/kind set,
// differential-pinned PER VERB). The oracle runs the real fmt; the
// machine runs the frontend's desugar (constant format string parsed at
// emit time, per-verb helper calls in a lifted per-site function whose
// call preserves fmt's evaluate-all-arguments-first order). Every row
// is a direct oracle test of one verb x kind pair; anything outside the
// set stays a visible frontend-export refusal (fail closed) — see the
// fail-closed rows at the bottom of cases.tsv.

import "fmt"

// enumT mirrors the plainpb enum shape: a named int32 WITH a String
// method — %d must render the NUMBER (%d is a PURE-NUMERIC verb, the
// one family that skips the Stringer check), %v/%s must call String.
// The stringable verbs are v, s, x, X, q — see the Stringer-precedence
// block below.
type enumT int32

func (e enumT) String() string { return "enum!" }

// panicky mirrors the plainpb fail-closed String stubs: String panics
// with a string value; fmt recovers and renders the panic.
type panicky int32

func (p panicky) String() string { panic("stub message here") }

// ps is the pointer-Stringer shape (*pb.ConfState): String on the
// pointer receiver, panicking.
type ps struct{ n int }

func (p *ps) String() string { panic("ptr stub") }

func sprintfDUint() string {
	return fmt.Sprintf("index %d (applied to %d)", uint64(7), uint64(18446744073709551615))
}

func sprintfDInt() string {
	return fmt.Sprintf("%d,%d,%d", -3, int64(-9223372036854775808), 0)
}

func sprintfDEnum() string {
	return fmt.Sprintf("type %d", enumT(2))
}

func sprintfXUint() string {
	return fmt.Sprintf("%x|%x|%x", uint64(0), uint64(48879), uint64(1)<<40)
}

func sprintfSString() string {
	return fmt.Sprintf("[%s]", "plain")
}

func sprintfSStringer() string {
	return fmt.Sprintf("state %s", enumT(1))
}

func sprintfSStringerPanic() string {
	return fmt.Sprintf("not a vote message: %s", panicky(9))
}

func sprintfVKinds() string {
	return fmt.Sprintf("%v %v %v %v", uint64(7), -2, "str", true)
}

func sprintfVStringerPanic() string {
	return fmt.Sprintf("transition:%v", panicky(1))
}

func sprintfPlusVPtrStringer() string {
	p := &ps{n: 1}
	return fmt.Sprintf("unable to restore config %+v", p)
}

func sprintfPlusVNilPtr() string {
	var p *ps
	return fmt.Sprintf("cfg %+v end", p)
}

func sprintfQBytes() string {
	return fmt.Sprintf("context:%q", []byte{'a', 0x00, '"', '\\', '\n', 0x7f, 0x1f, ' ', '~'})
}

func sprintfQBytesEmpty() string {
	var nilb []byte
	return fmt.Sprintf("%q|%q", []byte{}, nilb)
}

func sprintfPercent() string {
	return fmt.Sprintf("100%% of %d", 5)
}

func sprintfLiteralOnly() string {
	return fmt.Sprintf("no verbs at all")
}

// The measured decision-path shape (raft.go:1332): the result feeds a
// branch, not a log line.
func sprintfDecisionPath() int {
	failedCheck := ""
	pending, applied := uint64(9), uint64(4)
	if pending > applied {
		failedCheck = fmt.Sprintf("possible unapplied conf change at index %d (applied to %d)", pending, applied)
	}
	if failedCheck != "" {
		return len(failedCheck)
	}
	return 0
}

// Argument evaluation order: fmt evaluates ALL arguments (left to
// right) BEFORE any String method runs — the lift must preserve that
// (probed against gc: order is E1 E2 S1 S2, never E1 S1 E2 S2).
var evalOrder = ""

type tickT string

func (t tickT) String() string {
	evalOrder += "S(" + string(t) + ")"
	return string(t)
}

func tick(s string) tickT {
	evalOrder += "E(" + s + ")"
	return tickT(s)
}

func sprintfEvalOrder() (string, string) {
	evalOrder = ""
	r := fmt.Sprintf("%s %s", tick("a"), tick("b"))
	return r, evalOrder
}

// s on an error VALUE (the raft.go:1933 shape) and on a nil error.
func sprintfSError() string {
	err := fmt.Errorf("got %d entries", 0)
	return fmt.Sprintf("restore failed: %s", err)
}

func sprintfSNilError() string {
	var err error
	return fmt.Sprintf("[%s]", err)
}

func sprintfVNilError() string {
	var err error
	return fmt.Sprintf("[%v]", err)
}

// ---- %x / %q Stringer precedence (audit A-F1) ----
//
// gc's fmt consults error/Stringer for the STRINGABLE verbs — v, s, x,
// X, q (fmt/print.go handleMethods) — and skips it only for the
// pure-numeric verbs (%d and family). So %x over a Stringer-implementing
// UNSIGNED type is the hex of the String() RESULT, never of the number
// (probed against gc: "HI!" -> 484921, two lowercase hexits per byte,
// zero-padded), and %q over a Stringer-implementing []byte type quotes
// the String() result, never the bytes. The panic render does NOT get
// post-processed by the verb (probed: %!x(PANIC=String method: ...)
// verbatim, not hex).

type hexer uint64

func (h hexer) String() string { return "HI!" }

type hexPanicky uint64

func (h hexPanicky) String() string { panic("hex stub") }

type qbytes []byte

func (q qbytes) String() string { return "qs\"\n" }

type qbytesPanicky []byte

func (q qbytesPanicky) String() string { panic("q stub") }

func sprintfXStringer() string {
	return fmt.Sprintf("[%x]", hexer(255))
}

func sprintfXStringerPanic() string {
	return fmt.Sprintf("[%x]", hexPanicky(255))
}

func sprintfQStringer() string {
	return fmt.Sprintf("[%q]", qbytes{1, 2, 3})
}

func sprintfQStringerPanic() string {
	return fmt.Sprintf("[%q]", qbytesPanicky{1, 2, 3})
}

// The same precedence through a static `error` interface argument.
func sprintfXError() string {
	err := fmt.Errorf("got %d entries", 0)
	return fmt.Sprintf("[%x]", err)
}

func sprintfXNilError() string {
	var err error
	return fmt.Sprintf("[%x]", err)
}

// ---- fail-closed boundary rows (red at frontend-export BY DESIGN) ----

func sprintfVerbOutsideSet() string {
	return fmt.Sprintf("%T", 5)
}

func sprintfNonConstFormat(n int) string {
	f := "x%d"
	if n > 0 {
		f = "y%d"
	}
	return fmt.Sprintf(f, n)
}

func main() {
	r, o := sprintfEvalOrder()
	println(sprintfDUint(), sprintfDInt(), sprintfDEnum(), sprintfXUint(),
		sprintfSString(), sprintfSStringer(), sprintfSStringerPanic(),
		sprintfVKinds(), sprintfVStringerPanic(), sprintfPlusVPtrStringer(),
		sprintfPlusVNilPtr(), sprintfQBytes(), sprintfQBytesEmpty(),
		sprintfPercent(), sprintfLiteralOnly(), sprintfDecisionPath(),
		r, o, sprintfSError(), sprintfSNilError(), sprintfVNilError(),
		sprintfXStringer(), sprintfXStringerPanic(), sprintfQStringer(),
		sprintfQStringerPanic(), sprintfXError(), sprintfXNilError(),
		sprintfVerbOutsideSet(), sprintfNonConstFormat(1))
}
