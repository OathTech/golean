package main

// fmt.Errorf conformance pins (raft W4.1 item 2 — H-6's Errorf rider).
// Without %w, fmt.Errorf IS errors.New over the formatted text (fmt/
// errors.go), so the desugar rides the E5 errors.New shim: identity is
// a fresh cell per call, nil-ness always false, text via Error(). raft
// observes exactly nil-ness and identity of these errors (W3 log §2.4);
// text is pinned here anyway because Error() is live (raft.go:441).

import (
	"errors"
	"fmt"
)

func errorfFresh() int {
	a := fmt.Errorf("same %d", 1)
	b := fmt.Errorf("same %d", 1)
	n := 0
	if a != b {
		n += 1
	}
	if a == a {
		n += 2
	}
	if a != nil {
		n += 4
	}
	return n
}

func errorfText() string {
	err := fmt.Errorf("got %d entries in [%d, %d)", 0, uint64(3), uint64(9))
	return err.Error()
}

// The raft consumer shape: an Errorf error propagates and is
// discriminated by IDENTITY against a sentinel, never by text.
var errBreak = errors.New("break")

func errorfSentinelClassify() int {
	step := func(fail bool) error {
		if fail {
			return fmt.Errorf("unexpected conf type %d", 3)
		}
		return errBreak
	}
	n := 0
	if err := step(true); err != nil && err != errBreak {
		n += 1
	}
	if err := step(false); err == errBreak {
		n += 2
	}
	return n
}

func errorfVsErrorsNew() int {
	a := fmt.Errorf("t")
	b := errors.New("t")
	if a != b && a.Error() == b.Error() {
		return 1
	}
	return 0
}

func main() {
	println(errorfFresh(), errorfText(), errorfSentinelClassify(), errorfVsErrorsNew())
}
