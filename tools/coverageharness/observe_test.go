package main

import (
	"encoding/json"
	"strings"
	"testing"
)

func TestAbortMessageBytes(t *testing.T) {
	for _, tc := range []struct{ status, output, report, want string }{
		{"panic", "", "panic: a\x00b\x01c\t\r" + noTrailer(panicTrace), "a\x00b\x01c\t\r"},
		{"panic", "out\x00\x01\n", "panic: é\x00\x01\t\r\n\tsecond [recovered]\n\tpanic: other" + noTrailer(panicTrace), "é\x00\x01\t\r"},
		{"panic", "", "panic: \n\tsecond" + noTrailer(panicTrace), ""},
		{"panic", "", "panic: first [recovered]\n\tpanic: second" + noTrailer(panicTrace), "first [recovered]"},
		{"fatal", "fatal error: a\x00\x01\t\r", noTrailer(fatalTrace), "a\x00\x01\t\r"},
	} {
		raw := []byte(tc.output + tc.report + "exit status 2\n")
		lit, err := observedAbortMessage(raw, tc.status, channelFor(tc.report))
		if err != nil {
			t.Fatalf("%q: %v", raw, err)
		}
		var got string
		if err := json.Unmarshal([]byte(lit), &got); err != nil || got != tc.want {
			t.Fatalf("%q: literal %q decoded %q, want bytes %q: %v", raw, lit, got, tc.want, err)
		}
	}
}

func TestObservationAllControls(t *testing.T) {
	var controls []byte
	for i := 0; i < 32; i++ {
		controls = append(controls, byte(i))
	}
	controls = append(controls, []byte("é界😀\"\\<>&")...)
	// Prefix/output encoding uses the same exact JSON byte contract.
	for _, status := range []string{"ok", "panic"} {
		raw := append([]byte(nil), controls...)
		e := okChannel
		if status == "panic" {
			raw = append(raw, []byte("\npanic: payload"+panicTrace)...)
			e = channelFor("panic: payload" + noTrailer(panicTrace))
		}
		prefix, err := observedOutput(raw, status, e)
		if err != nil {
			t.Fatal(err)
		}
		lit, err := outputLiteral(prefix)
		var got string
		if err != nil {
			t.Fatal(err)
		}
		if err := json.Unmarshal([]byte(lit), &got); err != nil || got != string(prefix) {
			t.Fatalf("roundtrip %q: %v", lit, err)
		}
		if _, err := observationText([]byte(`{"output":` + lit + `}`)); err != nil {
			t.Fatal(err)
		}
	}
}

func TestAbortMessageRefusals(t *testing.T) {
	for _, tc := range []struct{ status, output, report, trailer, cause string }{
		{"panic", "", "panic: \xff" + noTrailer(panicTrace), "exit status 2\n", "UTF-8"},
		{"panic", "\xff\n", "panic: real" + noTrailer(panicTrace), "exit status 2\n", "UTF-8"},
		{"fatal", "gluedfatal error: x", noTrailer(fatalTrace), "exit status 2\n", "glued"},
		{"panic", "", "panic: real\n", "exit status 2\n", "trace header"},
		{"panic", "", "panic: real\n\ngoroutine 1 [running]:\n", "", "trailer"},
		{"fatal", "", "panic: only" + noTrailer(panicTrace), "exit status 2\n", "actual panic"},
		{"fatal", "", "panic: old [recovered]\n\tfatal error: new\x01\r" + noTrailer(panicTrace), "exit status 2\n", "actual panic"},
		{"ok", "", "", "", "unsupported status"},
	} {
		raw := []byte(tc.output + tc.report + tc.trailer)
		if got, err := observedAbortMessage(raw, tc.status, channelFor(tc.report)); err == nil || !strings.Contains(err.Error(), tc.cause) {
			t.Fatalf("%q: expected %s refusal, got %q / %v", raw, tc.cause, got, err)
		}
	}
}

func TestRawStdoutRefusals(t *testing.T) {
	for _, raw := range []string{"\x00{}", "{}\x00", "{\"x\":\"a\x01b\"}", "{\"x\":\"\xff\"}", "{}{}", "not JSON", ""} {
		if got, err := observationText([]byte(raw)); err == nil {
			t.Fatalf("accepted malformed stdout %q as %q", raw, got)
		}
	}
	valid := "{\"x\":\"a\\u0000b\\u0001c\\t\\r\\n界\"}\n"
	if got, err := observationText([]byte(valid)); err != nil || got != valid {
		t.Fatalf("valid stdout changed: %q %v", got, err)
	}
	if _, err := outputLiteral([]byte{0xff}); err == nil {
		t.Fatal("invalid UTF-8 silently replaced")
	}
}
