package main

import (
	"strings"
	"testing"
)

// Red-first (stdlib slice 3): written against a stub splitter that returned
// the whole input; the audit fix round A2 (2026-09-05) added the four shapes
// the first cut UNDERSTATED. Since the same-run crash channel became
// mandatory (A-R6, 2026-09-07) every fixture names its runtime-written
// report: shapes the RAW bytes left ambiguous (a glued print, a printed
// `panic: ` line before the real one) are now resolved by the channel, and
// only the fatal path — whose message precedes m.dying — keeps a raw rule.

const trace = panicTrace

func refuses(t *testing.T, stderr, status string, e crashEvidence, want string) {
	t.Helper()
	got, err := observedOutput([]byte(stderr), status, e)
	if err == nil {
		t.Fatalf("%s: must refuse, got prefix %q", status, got)
	}
	if !strings.Contains(err.Error(), want) {
		t.Fatalf("%s: refusal does not name %q: %v", status, want, err)
	}
}

func accepts(t *testing.T, stderr, status string, e crashEvidence, want string) {
	t.Helper()
	got, err := observedOutput([]byte(stderr), status, e)
	if err != nil || string(got) != want {
		t.Fatalf("%s: want prefix %q, got %q %v", status, want, got, err)
	}
}

func TestSplitStderrOk(t *testing.T) {
	accepts(t, "1 2 3\nab", "ok", okChannel, "1 2 3\nab")
	accepts(t, "panic: not really\n", "ok", okChannel, "panic: not really\n") // rc 0: it IS the program's output
	refuses(t, "x\nexit status 2\n", "ok", okChannel, "exit status")
	// a registered run that the runtime DID crash cannot be read as ok
	refuses(t, "x\n", "ok", channelFor("panic: x"+noTrailer(trace)), "empty crash report")
}

func TestSplitStderrPanic(t *testing.T) {
	rep := func(head string) crashEvidence { return channelFor(head + noTrailer(trace)) }
	accepts(t, "panic: boom"+trace, "panic", rep("panic: boom"), "")
	// a payload with a newline: the runtime TAB-indents the continuation
	accepts(t, "p\npanic: first line\n\tsecond line"+trace, "panic", rep("panic: first line\n\tsecond line"), "p\n")
	// the repanic chain is one report; the channel says where it starts
	accepts(t, "x\npanic: a [recovered]\n\tpanic: b"+trace, "panic", rep("panic: a [recovered]\n\tpanic: b"), "x\n")
	// A2 shape 1: the program printed marker text without a newline and gc's
	// block is glued to it — the RAW bytes are ambiguous, the channel is not
	accepts(t, "panic: fakepanic: real"+trace, "panic", rep("panic: real"), "panic: fake")
	// A2 shape 2: a printed `panic: …` line of its own before the real one
	accepts(t, "panic: fake\npanic: real"+trace, "panic", rep("panic: real"), "panic: fake\n")
	// the report must be the byte-identical suffix: a channel that disagrees
	// with stderr refuses rather than picking either
	refuses(t, "panic: fake\npanic: real"+trace, "panic", rep("panic: fake\npanic: real"), "un-indented continuation")
	refuses(t, "panic: boom"+trace, "panic", rep("panic: other"), "byte-identical stderr suffix")
	// a panic report cannot be read under the fatal status
	refuses(t, "panic: boom"+trace, "fatal", rep("panic: boom"), "actual panic")
}

func TestSplitStderrFatalAndDeadlock(t *testing.T) {
	rt := channelFor(noTrailer(runtimeFatalTrace))
	ft := channelFor(noTrailer(fatalTrace))
	dl := "tick\nfatal error: all goroutines are asleep - deadlock!" + runtimeFatalTrace
	accepts(t, dl, "deadlock", rt, "tick\n")
	accepts(t, "fatal error: sync: unlock of unlocked mutex"+fatalTrace, "fatal", ft, "")
	// the unwinding shape (BUG-106): panic line first, tab-indented fatal
	// continuation — the message region precedes m.dying and is unauthenticated
	unw := "p\npanic: v [recovered]\n\tfatal error: sync: unlock of unlocked mutex" + fatalTrace
	refuses(t, unw, "fatal", ft, "before m.dying")
	// A2 shape 3: a printed `panic: …` line beside a real deadlock block
	refuses(t, "panic: hello\nfatal error: all goroutines are asleep - deadlock!"+runtimeFatalTrace, "deadlock", rt, "ambiguous")
	// A2 shape 4: the marker text printed without a newline, glued to the block
	refuses(t, "fatal error: minefatal error: all goroutines are asleep - deadlock!"+runtimeFatalTrace, "deadlock", rt, "ambiguous")
	refuses(t, "fatal error: a\nfatal error: b"+fatalTrace, "fatal", ft, "ambiguous")
	// glued to program output without a newline
	refuses(t, "outfatal error: x"+fatalTrace, "fatal", ft, "glued")
	// a deadlock report cannot be read as a plain fatal, nor the converse
	refuses(t, dl, "fatal", rt, "actual deadlock")
	refuses(t, "fatal error: sync: unlock of unlocked mutex"+fatalTrace, "deadlock", ft, "actual fatal")
}

func TestSplitStderrRace(t *testing.T) {
	rep := "==================\nWARNING: DATA RACE\n==================\nFound 1 data race(s)\nexit status 66\n"
	accepts(t, rep, "race", okChannel, "")
	refuses(t, "hi\n"+rep, "race", okChannel, "not comparable")
}

func TestSplitStderrUTF8AndLiteral(t *testing.T) {
	refuses(t, string([]byte{0xff, 0xfe}), "ok", okChannel, "UTF-8")
	lit, err := outputLiteral([]byte("a\"b\n<>&\t"))
	if err != nil || lit != `"a\"b\n<>&\t"` {
		t.Fatalf("literal: %s %v", lit, err)
	}
}
