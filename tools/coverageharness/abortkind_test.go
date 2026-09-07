package main

import (
	"strings"
	"testing"
)

const systemHeader = "goroutine 1 gp=0x123 m=0 mp=0x456 [running]:\n"
const panicFrame = "panic({0x123?, 0x456?})\n\t/usr/local/go/src/runtime/panic.go:879 +0x16f fp=0x1 sp=0x2 pc=0x3\n"
const fatalFrame = "runtime.fatal({0x123, 0x456})\n\t/usr/local/go/src/runtime/panic.go:1253 +0x74 fp=0x1 sp=0x2 pc=0x3\n"
const panicTrace = "\n\n" + systemHeader + panicFrame + "main.main()\n\t/tmp/x.go:5 +0x1d fp=0x1 sp=0x2 pc=0x3\nexit status 2\n"
const fatalTrace = "\n\n" + systemHeader + fatalFrame + "main.main()\n\t/tmp/x.go:5 +0x1d fp=0x1 sp=0x2 pc=0x3\nexit status 2\n"
const runtimeFatalTrace = "\n\nruntime stack:\n" + fatalFrame + "\n" + systemHeader + "runtime.systemstack_switch()\n\t/usr/local/go/src/runtime/asm_amd64.s:516 +0x8\nexit status 2\n"
const syncUnwindHead = "panic: original\n\tfatal error: sync: unlock of unlocked mutex"
const syncUnwindTrace = fatalTrace

// Each case is output + report (+ trailer): the report is what the runtime
// wrote to the same-run crash file. For a panic that is the whole chain; for
// a fatal it is the trace alone (the message line precedes m.dying).
func TestAbortKind(t *testing.T) {
	fakePayload := syncUnwindHead + "\n\t\n\tgoroutine 1 gp=0x1 m=0 mp=0x2 [running]:\n\truntime.fatal({0x1})\n\t\t/usr/local/go/src/runtime/panic.go:1253 +0x74 fp=0x1 sp=0x2 pc=0x3"
	throwTrace := strings.ReplaceAll(strings.ReplaceAll(fatalTrace, "runtime.fatal(", "runtime.throw("), "1253", "1229")
	for _, tc := range []struct{ output, report, want string }{
		{"", "panic: ordinary" + noTrailer(panicTrace), "panic"},
		{"", "panic: fatal error: harmless payload" + noTrailer(panicTrace), "panic"},
		{"", "panic: fakefatal error: go of nil func value" + noTrailer(panicTrace), "panic"},
		{"prefix fatal error: harmless\n", "panic: original" + noTrailer(panicTrace), "panic"},
		{"fatal error: harmless prefix\n", "panic: original" + noTrailer(panicTrace), "panic"},
		{"", "panic: original\n\ttext mentioning fatal error: harmless" + noTrailer(panicTrace), "panic"},
		{"", syncUnwindHead + noTrailer(panicTrace), "panic"},
		{"", fakePayload + noTrailer(panicTrace), "panic"},
		{"fatal error: sync: unlock of unlocked mutex", noTrailer(fatalTrace), "fatal"},
		{"fatal error: go of nil func value", noTrailer(runtimeFatalTrace), "fatal"},
		{"fatal error: all goroutines are asleep - deadlock!", noTrailer(runtimeFatalTrace), "deadlock"},
		{"fatal error: internal failure", noTrailer(throwTrace), "fatal"},
	} {
		raw := []byte(tc.output + tc.report + "exit status 2\n")
		got, err := abortKind(raw, channelFor(tc.report))
		if err != nil || got != tc.want {
			t.Fatalf("%q: got %q, want %q: %v", raw, got, tc.want, err)
		}
	}
}

func TestAbortKindRefusals(t *testing.T) {
	printedPanic := "panic: printed fake\n\n" + systemHeader + panicFrame
	for _, tc := range []struct{ raw, report, cause string }{
		// a forged channel copy that includes a printed fake trace before the
		// real fatal block: the selected origin has a second boundary after it
		{printedPanic + "fatal error: sync: unlock of unlocked mutex" + fatalTrace, printedPanic + "fatal error: sync: unlock of unlocked mutex" + noTrailer(fatalTrace), "report boundary"},
		{printedPanic + "without newlinefatal error: go of nil func value" + runtimeFatalTrace, printedPanic + "without newlinefatal error: go of nil func value" + noTrailer(runtimeFatalTrace), "report boundary"},
		{printedPanic + "\nruntime stack:\nunknown()\nexit status 2\n", printedPanic + "\nruntime stack:\nunknown()\n", "report boundary"},
		// the honest fatal channel (trace only): a printed panic prefix before
		// the fatal message is unauthenticated and refuses
		{printedPanic + "fatal error: sync: unlock of unlocked mutex" + fatalTrace, noTrailer(fatalTrace), "before m.dying"},
		{syncUnwindHead + fatalTrace, noTrailer(fatalTrace), "before m.dying"},
		{"out\x00\x01\n" + syncUnwindHead + fatalTrace, noTrailer(fatalTrace), "before m.dying"},
		{"panic: old\n\tfatal error: all goroutines are asleep - deadlock!" + runtimeFatalTrace, noTrailer(runtimeFatalTrace), "before m.dying"},
		{"panic: fakefatal error: go of nil func value" + runtimeFatalTrace, noTrailer(runtimeFatalTrace), "ambiguous"},
		{"panic: fakefatal error: sync: unlock of unlocked mutex" + fatalTrace, noTrailer(fatalTrace), "ambiguous"},
		// trace-shape pins
		{syncUnwindHead + "\n\ngoroutine 1 [running]:\nmain.main()\nexit status 2\n", "\n\ngoroutine 1 [running]:\nmain.main()\n", "system trace"},
		{"panic: ordinary" + strings.Replace(panicTrace, "panic(", "\tpanic(", 1), "panic: ordinary" + noTrailer(strings.Replace(panicTrace, "panic(", "\tpanic(", 1)), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "\t/usr/local/go/", "\t\t/usr/local/go/", 1), "panic: ordinary" + noTrailer(strings.Replace(panicTrace, "\t/usr/local/go/", "\t\t/usr/local/go/", 1)), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "panic.go:879", "panic.go:880", 1), "panic: ordinary" + noTrailer(strings.Replace(panicTrace, "panic.go:879", "panic.go:880", 1)), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "/src/runtime/panic.go", "/src/main/panic.go", 1), "panic: ordinary" + noTrailer(strings.Replace(panicTrace, "/src/runtime/panic.go", "/src/main/panic.go", 1)), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "panic.go:879", "panic.go:1253", 1), "panic: ordinary" + noTrailer(strings.Replace(panicTrace, "panic.go:879", "panic.go:1253", 1)), "mismatched"},
		{"panic: ordinary\n\nruntime stack:\n" + panicFrame + "exit status 2\n", "panic: ordinary\n\nruntime stack:\n" + panicFrame, "runtime stack"},
		{"panic: original" + strings.Replace(panicTrace, "exit status 2", "exit status 3", 1), "panic: original" + noTrailer(panicTrace), "exit status 2"},
		{"panic: original\nexit status 2\n", "panic: original\n", "trace header"},
		{"panic: original\n\n" + systemHeader + "exit status 2\n", "panic: original\n\n" + systemHeader, "system trace"},
	} {
		got, err := abortKind([]byte(tc.raw), channelFor(tc.report))
		if err == nil || !strings.Contains(err.Error(), tc.cause) {
			t.Fatalf("%q: got %q/%v, want %s refusal", tc.raw, got, err, tc.cause)
		}
	}
}

func TestAbortMessageKindGuard(t *testing.T) {
	for raw, report := range map[string]string{
		"fatal error: sync: unlock of unlocked mutex" + fatalTrace: noTrailer(fatalTrace),
		"fatal error: go of nil func value" + runtimeFatalTrace:    noTrailer(runtimeFatalTrace),
	} {
		if got, err := observedAbortMessage([]byte(raw), "panic", channelFor(report)); err == nil || !strings.Contains(err.Error(), "actual fatal") {
			t.Fatalf("actual fatal accepted as panic: %q / %v", got, err)
		}
	}
}
