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

// Independent-review minimal counterexample: one authentic runtime origin
// does not authenticate the first printed panic marker. The raw fallback
// must refuse; the separately owned crash channel supplies the exact split.
func TestRawPrintedContinuationRefused(t *testing.T) {
	for _, prefix := range []string{"panic: forged\n\t", "panic: forged [recovered]\n\t"} {
		raw := []byte(prefix + "panic: actual" + panicTrace)
		if got, err := abortMessageLiteral(raw, "panic"); err == nil {
			t.Fatalf("printed prefix became a panic message: %s", got)
		}
	}
}

func TestAbortKind(t *testing.T) {
	fakePayload := syncUnwindHead + "\n\t\n\tgoroutine 1 gp=0x1 m=0 mp=0x2 [running]:\n\truntime.fatal({0x1})\n\t\t/usr/local/go/src/runtime/panic.go:1253 +0x74 fp=0x1 sp=0x2 pc=0x3"
	for _, tc := range []struct{ raw, want string }{
		{"panic: ordinary" + panicTrace, "panic"},
		{"panic: fatal error: harmless payload" + panicTrace, "panic"},
		{"panic: fakefatal error: go of nil func value" + panicTrace, "panic"},
		{"prefix fatal error: harmless\npanic: original" + panicTrace, "panic"},
		{"fatal error: harmless prefix\npanic: original" + panicTrace, "panic"},
		{"panic: original\n\ttext mentioning fatal error: harmless" + panicTrace, "panic"},
		{syncUnwindHead + panicTrace, "panic"},
		{fakePayload + panicTrace, "panic"},
		{"fatal error: sync: unlock of unlocked mutex" + fatalTrace, "fatal"},
		{"fatal error: go of nil func value" + runtimeFatalTrace, "fatal"},
		{"fatal error: all goroutines are asleep - deadlock!" + runtimeFatalTrace, "deadlock"},
		{"fatal error: internal failure" + strings.ReplaceAll(strings.ReplaceAll(fatalTrace, "runtime.fatal(", "runtime.throw("), "1253", "1229"), "fatal"},
	} {
		got, err := abortKind([]byte(tc.raw))
		if err != nil || got != tc.want {
			t.Fatalf("%q: got %q, want %q: %v", tc.raw, got, tc.want, err)
		}
	}
}

func TestAbortKindRefusals(t *testing.T) {
	printedPanic := "panic: printed fake\n\n" + systemHeader + panicFrame
	for _, tc := range []struct{ raw, cause string }{
		{printedPanic + "fatal error: sync: unlock of unlocked mutex" + fatalTrace, "report boundary"},
		{printedPanic + "without newlinefatal error: go of nil func value" + runtimeFatalTrace, "report boundary"},
		{printedPanic + "\nruntime stack:\nunknown()\nexit status 2\n", "report boundary"},
		{syncUnwindHead + fatalTrace, "before m.dying"},
		{"out\x00\x01\n" + syncUnwindHead + fatalTrace, "before m.dying"},
		{"panic: old\n\tfatal error: all goroutines are asleep - deadlock!" + runtimeFatalTrace, "before m.dying"},
		{"panic: fakefatal error: go of nil func value" + runtimeFatalTrace, "ambiguous"},
		{"panic: fakefatal error: sync: unlock of unlocked mutex" + fatalTrace, "ambiguous"},
		{syncUnwindHead + "\n\ngoroutine 1 [running]:\nmain.main()\nexit status 2\n", "system trace"},
		{"panic: ordinary" + strings.Replace(panicTrace, "panic(", "\tpanic(", 1), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "\t/usr/local/go/", "\t\t/usr/local/go/", 1), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "panic.go:879", "panic.go:880", 1), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "/src/runtime/panic.go", "/src/main/panic.go", 1), "unknown first"},
		{"panic: ordinary" + strings.Replace(panicTrace, "panic.go:879", "panic.go:1253", 1), "mismatched"},
		{"panic: ordinary\n\nruntime stack:\n" + panicFrame + "exit status 2\n", "runtime stack"},
		{"panic: fake\npanic: real" + panicTrace, "ambiguous"},
		{"panic: original" + strings.Replace(panicTrace, "exit status 2", "exit status 3", 1), "exit status 2"},
		{"panic: original\nexit status 2\n", "trace header"},
		{"panic: original\n\n" + systemHeader + "exit status 2\n", "system trace"},
	} {
		got, err := abortKind([]byte(tc.raw))
		if err == nil || !strings.Contains(err.Error(), tc.cause) {
			t.Fatalf("%q: got %q/%v, want %s refusal", tc.raw, got, err, tc.cause)
		}
	}
}

func TestAbortMessageKindGuard(t *testing.T) {
	for _, raw := range []string{"fatal error: sync: unlock of unlocked mutex" + fatalTrace, "fatal error: go of nil func value" + runtimeFatalTrace} {
		if got, err := abortMessageLiteral([]byte(raw), "panic"); err == nil || !strings.Contains(err.Error(), "actual fatal") {
			t.Fatalf("actual fatal accepted as panic: %q / %v", got, err)
		}
	}
}
