package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestOwnedPanicPartition(t *testing.T) {
	var allASCII []byte
	for i := 0; i < 128; i++ {
		allASCII = append(allASCII, byte(i))
	}
	trace := strings.TrimSuffix(panicTrace, "exit status 2\n")
	for _, tc := range []struct{ output, report, message string }{
		{"panic: forged\n\t", "panic: actual" + trace, "actual"},
		{"panic: forged [recovered]\n\t", "panic: actual" + trace, "actual"},
		{"", "panic: forged\n\tpanic: actual" + trace, "forged"},
		{"glued", "panic: actual" + trace, "actual"},
		{string(allASCII) + "界panic: fake\n\t", "panic: a\x00\x01\t\r\n\tsecond" + trace, "a\x00\x01\t\r"},
		{"panic: fake\n\n" + systemHeader + panicFrame + "\n\t", "panic: actual" + trace, "actual"},
		{"", "panic: first [recovered]\n\tpanic: second" + trace, "first [recovered]"},
		// a payload that imitates a fatal report + system trace: printindented
		// renders every payload LF as LF TAB, so the imitation stays indented
		{"", "panic: first\n\tfatal error: fake\n\t\n\t" + systemHeader + "\t" + strings.TrimSuffix(fatalFrame, "\n") + trace, "first"},
	} {
		raw := []byte(tc.output + tc.report + "exit status 2\n")
		e := channelFor(tc.report)
		view, err := checkedAbortView(raw, e)
		if err != nil || view.kind != "panic" || string(view.message) != tc.message || string(view.output) != tc.output {
			t.Fatalf("exact partition failed: %+v/%v; want %+v", view, err, tc)
		}
		lit, err := observedAbortMessage(raw, "panic", e)
		var message string
		if err != nil || json.Unmarshal([]byte(lit), &message) != nil || message != tc.message {
			t.Fatalf("message JSON changed bytes: %q/%v", lit, err)
		}
		out, err := observedOutput(raw, "panic", e)
		if err != nil || string(out) != tc.output {
			t.Fatalf("output differs: %q/%v", out, err)
		}
	}
}

// A signal-induced panic (nil dereference) prints ONE un-indented
// `[signal …]` line after the chain (dopanic_m); it is part of the runtime's
// shape and must classify. The same line anywhere else is not.
func TestSignalLineShape(t *testing.T) {
	const sig = "[signal SIGSEGV: segmentation violation code=0x1 addr=0x0 pc=0x47b2c5]\n"
	trace := strings.TrimSuffix(panicTrace, "exit status 2\n")
	// trace begins "\n\n<header>"; the runtime prints msg LF, signal line, then LF header
	report := "panic: runtime error: invalid memory address or nil pointer dereference\n" + sig + trace[1:]
	raw := []byte("out\n" + report + "exit status 2\n")
	v, err := checkedAbortView(raw, channelFor(report))
	if err != nil || v.kind != "panic" || string(v.output) != "out\n" ||
		string(v.message) != "runtime error: invalid memory address or nil pointer dereference" {
		t.Fatalf("signal-induced panic must classify: %+v/%v", v, err)
	}
	// a recovered-then-repanicked chain ending in a signal line
	report = "panic: first [recovered]\n\tpanic: runtime error: index out of range [5] with length 2\n" + sig + trace[1:]
	if v, err := checkedAbortView([]byte(report+"exit status 2\n"), channelFor(report)); err != nil || string(v.message) != "first [recovered]" {
		t.Fatalf("chain + signal line must classify: %+v/%v", v, err)
	}
	// the signal line followed by more chain lines is not the runtime's shape
	report = "panic: first\n" + sig + "\tpanic: second\n" + trace[1:]
	if v, err := checkedAbortView([]byte(report+"exit status 2\n"), channelFor(report)); err == nil || !strings.Contains(err.Error(), "un-indented continuation") {
		t.Fatalf("mid-chain signal line accepted: %+v/%v", v, err)
	}
	report = "panic: first\n" + sig + "panic: second\n" + trace[1:]
	if v, err := checkedAbortView([]byte(report+"exit status 2\n"), channelFor(report)); err == nil || !strings.Contains(err.Error(), "un-indented continuation") {
		t.Fatalf("signal line before a bare marker accepted: %+v/%v", v, err)
	}
}

func TestCrashEvidenceRefusals(t *testing.T) {
	report := "panic: actual" + strings.TrimSuffix(panicTrace, "exit status 2\n")
	raw := []byte("prefix" + report + "exit status 2\n")
	for _, e := range []crashEvidence{
		{true, []byte(report), nil},
		{true, []byte(report), []byte("registered\nextra")},
		channelFor(report + "x"),
		channelFor(strings.Replace(report, "actual", "other", 1)),
		channelFor("panic: actual\n"),
	} {
		if v, err := checkedAbortView(raw, e); err == nil {
			t.Fatalf("corrupt evidence accepted: %+v", v)
		}
	}
	for _, report := range []string{
		"panic: actual\n\n" + systemHeader + "unknown()\n",
		"panic: actual" + strings.TrimSuffix(panicTrace, "exit status 2\n") + "panic: later\n",
		"panic: actual" + strings.TrimSuffix(panicTrace, "exit status 2\n") + "\nruntime stack:\nunknown()\n",
	} {
		if v, err := checkedAbortView([]byte(report+"exit status 2\n"), channelFor(report)); err == nil {
			t.Fatalf("unsupported report accepted: %+v", v)
		}
	}
	// First-line invalid bytes stay available in the raw view, but no JSON
	// observation silently replaces them. Invalid output also refuses.
	invalid := strings.Replace(report, "actual", "\xff", 1)
	if _, err := observedAbortMessage([]byte(invalid+"exit status 2\n"), "panic", channelFor(invalid)); err == nil {
		t.Fatal("invalid UTF-8 became JSON")
	}
	if _, err := checkedAbortView(append([]byte{0xff}, []byte(report+"exit status 2\n")...), channelFor(report)); err == nil {
		t.Fatal("invalid output accepted")
	}
}

func TestCrashEvidenceSuccessAndFiles(t *testing.T) {
	valid := crashEvidence{true, nil, []byte("registered\n")}
	if out, err := observedOutput([]byte("\x00\x01\n"), "ok", valid); err != nil || !bytes.Equal(out, []byte("\x00\x01\n")) {
		t.Fatalf("success bytes: %q/%v", out, err)
	}
	for _, e := range []crashEvidence{{true, nil, nil}, channelFor("unexpected"), {true, nil, []byte("wrong")}} {
		if _, err := observedOutput(nil, "ok", e); err == nil {
			t.Fatal("success accepted without valid empty channel")
		}
	}
	dir := t.TempDir()
	report, ack := filepath.Join(dir, "crash"), filepath.Join(dir, "ack")
	if err := os.WriteFile(report, nil, 0600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(ack, []byte("registered\n"), 0600); err != nil {
		t.Fatal(err)
	}
	for _, paths := range [][2]string{{report, ""}, {"", ack}, {report, ack + "missing"}, {report + "missing", ack}} {
		if _, err := readCrashEvidence(paths[0], paths[1]); err == nil {
			t.Fatal("unpaired/missing evidence accepted")
		}
	}
	if _, err := readCrashEvidence(report, ack); err != nil {
		t.Fatal(err)
	}
}

func TestFatalUnwindRemainsExplicitRefusal(t *testing.T) {
	report := strings.TrimSuffix(fatalTrace, "exit status 2\n")
	raw := []byte(syncUnwindHead + report + "exit status 2\n")
	// BUG-106 (sync/mutex-unlock-fatal/during-panic-unwind): the message
	// region precedes m.dying and is unauthenticated — an explicit refusal
	// with the honest channel, and a channel-required refusal without one.
	if v, err := checkedAbortView(raw, channelFor(report)); err == nil || !strings.Contains(err.Error(), "before m.dying") {
		t.Fatalf("fatal output guessed: %+v/%v", v, err)
	}
	if v, err := checkedAbortView(raw, crashEvidence{}); err == nil || !strings.Contains(err.Error(), "crash evidence: required") {
		t.Fatalf("no-evidence fatal unwind classified: %+v/%v", v, err)
	}
	// Simple fatal remains observable under the explicit fallback.
	raw = []byte("before\nfatal error: sync: unlock of unlocked mutex" + report + "exit status 2\n")
	v, err := checkedAbortView(raw, channelFor(report))
	if err != nil || v.kind != "fatal" || string(v.output) != "before\n" {
		t.Fatalf("simple fatal: %+v/%v", v, err)
	}
}
