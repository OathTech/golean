package main

import (
	"strings"
	"testing"
)

// Test-side channel constructors. A fixture is `output + report + trailer`;
// the REPORT is what the runtime wrote to the same-run crash file after
// m.dying (the whole panic chain for a panic; the trace only for a fatal).
// Every classification test names its report explicitly — there is no
// zero-evidence path any more (A-R6, crashview.go).

func channelFor(report string) crashEvidence {
	return crashEvidence{true, []byte(report), []byte(crashAckText)}
}

// okChannel is a registered run in which the runtime wrote no crash report.
var okChannel = crashEvidence{true, nil, []byte(crashAckText)}

// preMainAbort is the channel state of a subject that aborted before main's
// first statement: both owned files untouched (empty).
var preMainAbort = crashEvidence{true, nil, nil}

func noTrailer(trace string) string { return strings.TrimSuffix(trace, "exit status 2\n") }

// A-R6: the acknowledgement is required UNIFORMLY. Every entry point that
// classifies stderr refuses BY NAME when the hook never registered, whether
// the query is ok, race, panic, fatal, message or record.
func TestMissingRegistrationRefusedByName(t *testing.T) {
	const want = "no hook registration acknowledgement"
	panicRaw := []byte("panic: init boom" + panicTrace)
	fatalRaw := []byte("fatal error: all goroutines are asleep - deadlock!" + runtimeFatalTrace)
	check := func(label string, err error) {
		t.Helper()
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Fatalf("%s: pre-main abort must refuse naming %q, got %v", label, want, err)
		}
	}
	_, err := checkedAbortView(panicRaw, preMainAbort)
	check("checkedAbortView/panic", err)
	_, err = checkedAbortView(fatalRaw, preMainAbort)
	check("checkedAbortView/fatal", err)
	_, err = observedOutput(panicRaw, "panic", preMainAbort)
	check("observedOutput/panic", err)
	_, err = observedOutput([]byte("plain output\n"), "ok", preMainAbort)
	check("observedOutput/ok", err)
	_, err = observedOutput([]byte("==================\nWARNING: DATA RACE\n==================\nexit status 66\n"), "race", preMainAbort)
	check("observedOutput/race", err)
	_, err = observedAbortMessage(panicRaw, "panic", preMainAbort)
	check("observedAbortMessage", err)
	_, err = observedAbortRecord(panicRaw, preMainAbort)
	check("observedAbortRecord", err)
	_, err = abortKind(panicRaw, preMainAbort)
	check("abortKind", err)
	// The refusal is not a fallback: the SAME bytes with a registered channel
	// classify cleanly, so the red is attributable to the channel alone.
	if v, err := checkedAbortView(panicRaw, channelFor(noTrailer(string(panicRaw)))); err != nil || v.kind != "panic" || string(v.message) != "init boom" {
		t.Fatalf("registered channel must classify the same bytes: %+v/%v", v, err)
	}
}

// A-R6: no channel at all is a refusal too, never a weaker classification.
func TestNoEvidenceRefused(t *testing.T) {
	const want = "crash evidence: required"
	raw := []byte("panic: boom" + panicTrace)
	for label, err := range map[string]error{
		"checkedAbortView":     second(checkedAbortView(raw, crashEvidence{})),
		"observedOutput/ok":    second(observedOutput([]byte("x\n"), "ok", crashEvidence{})),
		"observedOutput/race":  second(observedOutput([]byte("==================\nWARNING: DATA RACE\nexit status 66\n"), "race", crashEvidence{})),
		"observedOutput/panic": second(observedOutput(raw, "panic", crashEvidence{})),
		"observedAbortMessage": second(observedAbortMessage(raw, "panic", crashEvidence{})),
		"observedAbortRecord":  second(observedAbortRecord(raw, crashEvidence{})),
		"abortKind":            second(abortKind(raw, crashEvidence{})),
	} {
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Fatalf("%s: must refuse naming %q, got %v", label, want, err)
		}
	}
}

// A-R6: an exit-2 run whose crash file stayed EMPTY after registration did
// not crash in the runtime — the "report" on stderr was printed by the
// program (or it called os.Exit(2)). Refused by name; never split.
func TestAbortWithoutCrashReportRefused(t *testing.T) {
	const want = "runtime wrote no crash report"
	printed := []byte("panic: printed by the program" + panicTrace)
	for label, err := range map[string]error{
		"checkedAbortView":     second(checkedAbortView(printed, okChannel)),
		"observedOutput/panic": second(observedOutput(printed, "panic", okChannel)),
		"observedAbortMessage": second(observedAbortMessage(printed, "panic", okChannel)),
		"observedAbortRecord":  second(observedAbortRecord(printed, okChannel)),
	} {
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Fatalf("%s: must refuse naming %q, got %v", label, want, err)
		}
	}
}

func second[T any](_ T, err error) error { return err }
