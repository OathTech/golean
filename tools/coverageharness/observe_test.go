package main

import (
	"encoding/json"
	"os"
	"path/filepath"
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

// Release-readiness item 22 (2026-10-12): a func-typed result — bare, nil,
// of a declared func type, in a struct field or array, boxed in an interface
// (a declared func type's nil included) — is refused BY NAME by the
// generated observer (the machine's readout refuses the same values,
// GoLean/CLI.lean funcObserved?), and an int result beside it still answers
// (the positive control). Runs the pinned `go run`; a missing go fails.
const funcObsFixture = `package main

func add1(n int) int { return n + 1 }

type Box struct {
	F func(int) int
	N int
}

func retFunc() func(int) int    { return add1 }
func retNilFunc() func(int) int { return nil }
func retBoxed() Box             { return Box{F: add1, N: 3} }
func retAny() any               { return add1 }
func retInt() int               { return add1(6) }

type Fn func(int) int

func retNamedFuncNilBare() Fn            { return nil }
func retNamedFuncNilBoxed() any          { var f Fn; return f }
func retNilFuncInStruct() Box            { return Box{N: 3} }
func retNilFuncInArray() [2]func(int) int { return [2]func(int) int{} }

func main() {}
`

func TestFuncObservationRefusedByName(t *testing.T) {
	root := t.TempDir()
	input := filepath.Join(root, "main.go")
	if err := os.WriteFile(input, []byte(funcObsFixture), 0o644); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct{ subject, want string }{
		{"retFunc", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retNilFunc", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retBoxed", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retAny", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retNamedFuncNilBare", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retNamedFuncNilBoxed", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retNilFuncInStruct", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retNilFuncInArray", "unsupported Go observation kind func (a Go func value has no observable identity"},
		{"retInt", `"status":"ok","values":[{"kind":"int","tag":"int","value":7}]`},
	} {
		dir := filepath.Join(root, tc.subject)
		if err := run(config{input: input, out: dir, subject: tc.subject, args: "-", status: "ok"}); err != nil {
			t.Fatalf("%s: harness generation: %v", tc.subject, err)
		}
		r := goRunOracle(t, dir)
		var obs map[string]any
		if r.exit != 0 || json.Unmarshal(r.stdout, &obs) != nil || !strings.Contains(string(r.stdout), tc.want) {
			t.Fatalf("%s: want exit 0 and an observation containing %q, got exit %d: %s", tc.subject, tc.want, r.exit, r.stdout)
		}
		if tc.subject != "retInt" && obs["status"] != "error" {
			t.Fatalf("%s: a func observation must be the observer's status:error refusal: %s", tc.subject, r.stdout)
		}
	}
}
