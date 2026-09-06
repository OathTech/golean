package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func channelFor(report string) crashEvidence {
	return crashEvidence{true, []byte(report), []byte("registered\n")}
}

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
		{"", "panic: first\n\tfatal error: fake\n\t\n\t" + systemHeader + "\t" + fatalFrame + trace, "first"},
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
	for _, e := range []crashEvidence{{}, channelFor(report)} {
		if v, err := checkedAbortView(raw, e); err == nil || !strings.Contains(err.Error(), "before m.dying") {
			t.Fatalf("fatal output guessed: %+v/%v", v, err)
		}
	}
	// Simple fatal remains observable under the explicit fallback.
	raw = []byte("before\nfatal error: sync: unlock of unlocked mutex" + report + "exit status 2\n")
	v, err := checkedAbortView(raw, channelFor(report))
	if err != nil || v.kind != "fatal" || string(v.output) != "before\n" {
		t.Fatalf("simple fatal: %+v/%v", v, err)
	}
}
