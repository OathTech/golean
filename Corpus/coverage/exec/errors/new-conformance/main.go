package main

// errors.New conformance guardrails (G-2/H-10, raft W4.0 2026-08-20;
// E5 stdlib-shim pattern — the shim is Go's own implementation modulo
// names, tools/nativefrontend/stdlibshim.go; fidelity argument:
// docs/raft-w4-log.md item 2). What raft observes of an error is its
// IDENTITY and its NIL-NESS, never its text (raft-w3 log §2.4), so the
// identity rows are the load-bearing ones; the text rows pin Error()
// readback because newRaft's panic path (raft.go:441) is live.

import "errors"

// freshNotEq: two errors.New with EQUAL TEXT are distinct values —
// errors.New allocates a fresh cell per call (probed against gc
// 2026-08-20: false). A shim that interned by text would silently make
// `err == errBreak` true everywhere in raft (W3 log §2.4).
func errNewFreshNotEq() int {
	a := errors.New("same")
	b := errors.New("same")
	if a == b {
		return 0
	}
	return 1
}

func errNewSelfEq() int {
	a := errors.New("same")
	if a == a {
		return 1
	}
	return 0
}

func errNewNilness() int {
	a := errors.New("x")
	var z error
	n := 0
	if a != nil {
		n += 1
	}
	if z == nil {
		n += 2
	}
	return n
}

// readback: Error() returns the constructor's string, verbatim.
func errNewReadback() int {
	a := errors.New("some text")
	if a.Error() == "some text" {
		return len(a.Error())
	}
	return -1
}

// crossImpl: identity comparison is (dynamic type, value), never text —
// an errors.New error and a user error with the same text are not ==.
type textErr struct{ s string }

func (t textErr) Error() string { return t.s }

func errNewCrossImpl() int {
	a := errors.New("same")
	if a == error(textErr{"same"}) {
		return 0
	}
	return 1
}

// assertOk: the error INTERFACE value round-trips through any with a
// comma-ok assertion (the boxing rides the ordinary interface
// machinery — no special-cased representation).
func errNewAssertOk() int {
	var i any = errors.New("boxed")
	if e, ok := i.(error); ok && e != nil {
		return 1
	}
	return 0
}

func main() {
	println(errNewFreshNotEq(), errNewSelfEq(), errNewNilness(),
		errNewReadback(), errNewCrossImpl(), errNewAssertOk())
}
