package main

import (
	"strings"
	"testing"
)

// Red-first (stdlib slice 3): these tests were written against a stub
// `splitStderr` that returned the whole input — every refusal row below
// failed, and the panic/fatal rows returned the abort block as "output".

func TestSplitStderrOk(t *testing.T) {
	got, err := splitStderr([]byte("1 2 3\nab"), "ok")
	if err != nil || string(got) != "1 2 3\nab" {
		t.Fatalf("ok: %q %v", got, err)
	}
	if _, err := splitStderr([]byte("x\nexit status 2\n"), "ok"); err == nil {
		t.Fatal("ok with an exit trailer must refuse")
	}
}

func TestSplitStderrPanic(t *testing.T) {
	stderr := "before\npanic: boom\n\ngoroutine 1 [running]:\nmain.main()\n\t/tmp/x.go:5 +0x1d\nexit status 2\n"
	got, err := splitStderr([]byte(stderr), "panic")
	if err != nil || string(got) != "before\n" {
		t.Fatalf("panic prefix: %q %v", got, err)
	}
	// no print at all
	got, err = splitStderr([]byte("panic: boom\n\ngoroutine 1 [running]:\nexit status 2\n"), "panic")
	if err != nil || string(got) != "" {
		t.Fatalf("panic empty prefix: %q %v", got, err)
	}
	// a print without a trailing newline glues onto the report: refuse
	if _, err := splitStderr([]byte("abcpanic: boom\n\ngoroutine 1 [running]:\nexit status 2\n"), "panic"); err == nil || !strings.Contains(err.Error(), "no line-start") {
		t.Fatalf("glued panic must refuse by name, got %v", err)
	}
	// a program line beginning `panic: ` : ambiguous, refuse
	if _, err := splitStderr([]byte("panic: fake\npanic: boom\n\ngoroutine 1 [running]:\nexit status 2\n"), "panic"); err == nil || !strings.Contains(err.Error(), "ambiguous") {
		t.Fatalf("two panic lines must refuse by name, got %v", err)
	}
	// missing trailer: not a verdict
	if _, err := splitStderr([]byte("panic: boom\n"), "panic"); err == nil || !strings.Contains(err.Error(), "trailer") {
		t.Fatalf("missing trailer must refuse, got %v", err)
	}
}

func TestSplitStderrFatalAndDeadlock(t *testing.T) {
	dl := "tick\nfatal error: all goroutines are asleep - deadlock!\n\ngoroutine 1 [chan receive]:\nexit status 2\n"
	got, err := splitStderr([]byte(dl), "deadlock")
	if err != nil || string(got) != "tick\n" {
		t.Fatalf("deadlock prefix: %q %v", got, err)
	}
	// the unwinding shape: panic line first, tab-indented fatal
	unw := "p\npanic: v [recovered]\n\tfatal error: sync: unlock of unlocked mutex\n\ngoroutine 1 [running]:\nexit status 2\n"
	got, err = splitStderr([]byte(unw), "fatal")
	if err != nil || string(got) != "p\n" {
		t.Fatalf("fatal-during-unwind prefix: %q %v", got, err)
	}
	if _, err := splitStderr([]byte("fatal error: a\nfatal error: b\nexit status 2\n"), "fatal"); err == nil {
		t.Fatal("two fatal lines must refuse")
	}
}

func TestSplitStderrRace(t *testing.T) {
	rep := "==================\nWARNING: DATA RACE\n==================\nFound 1 data race(s)\nexit status 66\n"
	got, err := splitStderr([]byte(rep), "race")
	if err != nil || string(got) != "" {
		t.Fatalf("race: %q %v", got, err)
	}
	if _, err := splitStderr([]byte("hi\n"+rep), "race"); err == nil || !strings.Contains(err.Error(), "not comparable") {
		t.Fatalf("race with program output must refuse by name, got %v", err)
	}
}

func TestSplitStderrUTF8AndLiteral(t *testing.T) {
	if _, err := splitStderr([]byte{0xff, 0xfe}, "ok"); err == nil || !strings.Contains(err.Error(), "UTF-8") {
		t.Fatalf("invalid UTF-8 must refuse by name, got %v", err)
	}
	lit, err := outputLiteral([]byte("a\"b\n<>&\t"))
	if err != nil || lit != `"a\"b\n<>&\t"` {
		t.Fatalf("literal: %s %v", lit, err)
	}
}
