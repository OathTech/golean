package main

import (
	"strings"
	"testing"
)

// Red-first (stdlib slice 3): written against a stub `splitStderr` that
// returned the whole input; the audit fix round A2 (2026-09-05) added the
// four shapes the first cut UNDERSTATED (they returned a prefix where gc's
// stream is ambiguous) — each failed against the first cut before the fix.

const trace = "\n\ngoroutine 1 [running]:\nmain.main()\n\t/tmp/x.go:5 +0x1d\nexit status 2\n"

func refuses(t *testing.T, stderr, status, want string) {
	t.Helper()
	got, err := splitStderr([]byte(stderr), status)
	if err == nil {
		t.Fatalf("%s: must refuse, got prefix %q", status, got)
	}
	if !strings.Contains(err.Error(), want) {
		t.Fatalf("%s: refusal does not name %q: %v", status, want, err)
	}
}

func accepts(t *testing.T, stderr, status, want string) {
	t.Helper()
	got, err := splitStderr([]byte(stderr), status)
	if err != nil || string(got) != want {
		t.Fatalf("%s: want prefix %q, got %q %v", status, want, got, err)
	}
}

func TestSplitStderrOk(t *testing.T) {
	accepts(t, "1 2 3\nab", "ok", "1 2 3\nab")
	accepts(t, "panic: not really\n", "ok", "panic: not really\n") // rc 0: it IS the program's output
	refuses(t, "x\nexit status 2\n", "ok", "exit status")
}

func TestSplitStderrPanic(t *testing.T) {
	accepts(t, "before\npanic: boom"+trace, "panic", "before\n")
	accepts(t, "panic: boom"+trace, "panic", "")
	// a payload with a newline: the block is still one marker + header
	accepts(t, "p\npanic: first line\n\tsecond line"+trace, "panic", "p\n")
	// the repanic chain: the continuation `\n\tpanic: ` does not count
	accepts(t, "x\npanic: a [recovered]\n\tpanic: b"+trace, "panic", "x\n")
	// A2 shape 1: the program printed the marker text without a newline —
	// gc's block is glued to it (`panic: fakepanic: real`): two occurrences
	refuses(t, "panic: fakepanic: real"+trace, "panic", "ambiguous")
	// A2 shape 2: the program printed a `panic: …` LINE of its own
	refuses(t, "hello\npanic: fake\npanic: real"+trace, "panic", "ambiguous")
	// a print without a trailing newline glues onto the report
	refuses(t, "abcpanic: boom"+trace, "panic", "glued")
	// no header: not a well-formed report
	refuses(t, "panic: boom\nexit status 2\n", "panic", "trace header")
	refuses(t, "panic: boom\n", "panic", "trailer")
}

func TestSplitStderrFatalAndDeadlock(t *testing.T) {
	dl := "tick\nfatal error: all goroutines are asleep - deadlock!\n\ngoroutine 1 [chan receive]:\nexit status 2\n"
	accepts(t, dl, "deadlock", "tick\n")
	// the unwinding shape: panic line first, tab-indented fatal continuation
	unw := "p\npanic: v [recovered]\n\tfatal error: sync: unlock of unlocked mutex"+trace
	accepts(t, unw, "fatal", "p\n")
	// A2 shape 3: a printed `panic: …` line beside a real deadlock block
	refuses(t, "panic: hello\nfatal error: all goroutines are asleep - deadlock!\n\ngoroutine 1 [chan receive]:\nexit status 2\n", "deadlock", "ambiguous")
	// A2 shape 4: the marker text printed without a newline, glued to the block
	refuses(t, "fatal error: minefatal error: all goroutines are asleep - deadlock!\n\ngoroutine 1 [chan receive]:\nexit status 2\n", "deadlock", "ambiguous")
	refuses(t, "fatal error: a\nfatal error: b\n\ngoroutine 1 [running]:\nexit status 2\n", "fatal", "ambiguous")
}

func TestSplitStderrRace(t *testing.T) {
	rep := "==================\nWARNING: DATA RACE\n==================\nFound 1 data race(s)\nexit status 66\n"
	accepts(t, rep, "race", "")
	refuses(t, "hi\n"+rep, "race", "not comparable")
}

func TestSplitStderrUTF8AndLiteral(t *testing.T) {
	refuses(t, string([]byte{0xff, 0xfe}), "ok", "UTF-8")
	lit, err := outputLiteral([]byte("a\"b\n<>&\t"))
	if err != nil || lit != `"a\"b\n<>&\t"` {
		t.Fatalf("literal: %s %v", lit, err)
	}
}
