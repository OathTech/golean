package main

import (
	"bytes"
	"fmt"
	"os"
	"unicode/utf8"
)

// Paired evidence belongs to one completed run in a runner-owned directory.
// This validates a runtime channel, not arbitrary caller-forged capture files.
type crashEvidence struct {
	enabled bool
	report  []byte
	ack     []byte
}

type abortView struct {
	kind    string
	message []byte
	output  []byte
}

func readCrashEvidence(reportPath, ackPath string) (crashEvidence, error) {
	if reportPath == "" && ackPath == "" {
		return crashEvidence{}, nil
	}
	if reportPath == "" || ackPath == "" {
		return crashEvidence{}, fmt.Errorf("crash evidence: report and registration paths must be paired")
	}
	report, err := os.ReadFile(reportPath)
	if err != nil {
		return crashEvidence{}, fmt.Errorf("crash evidence: read report: %w", err)
	}
	ack, err := os.ReadFile(ackPath)
	if err != nil {
		return crashEvidence{}, fmt.Errorf("crash evidence: read registration: %w", err)
	}
	e := crashEvidence{true, report, ack}
	return e, e.validate()
}

func (e crashEvidence) validate() error {
	if !e.enabled {
		return nil
	}
	if len(e.ack) != 0 && !bytes.Equal(e.ack, []byte("registered\n")) {
		return fmt.Errorf("crash evidence: malformed registration acknowledgement")
	}
	if len(e.ack) == 0 && len(e.report) != 0 {
		return fmt.Errorf("crash evidence: nonempty report without registration acknowledgement")
	}
	return nil
}

// originKind validates raw indentation BEFORE any decoding/normalization.
// Payload newlines acquire TAB in printindented. With an owned crash channel
// this distinguishes the actual first trace from a payload's fake header.
// A raw fallback additionally needs a unique marker/output boundary.
func originKind(report []byte) (string, error) {
	header := abortTraceHeaderRe.FindIndex(report)
	if header == nil {
		return "", fmt.Errorf("abort classification: missing trace header")
	}
	trace := report[header[0]:]
	if trace[0] == '\n' {
		trace = trace[1:]
	}
	kind, err := pinnedTraceKind(trace)
	if err != nil {
		return "", err
	}
	tail := report[header[1]:]
	if bytes.Contains(tail, []byte("panic: ")) || bytes.Contains(tail, []byte("fatal error: ")) ||
		bytes.Contains(tail, []byte("\nruntime stack:")) {
		return "", fmt.Errorf("abort classification: additional or unknown report boundary after selected origin, refused")
	}
	return kind, nil
}

func makeAbortView(kind string, report, output []byte) (abortView, error) {
	if !utf8.Valid(output) {
		return abortView{}, fmt.Errorf("stderr split: program output is not valid UTF-8, refused")
	}
	marker := []byte("panic: ")
	if kind == "fatal" {
		marker = []byte("fatal error: ")
	}
	if !bytes.HasPrefix(report, marker) {
		return abortView{}, fmt.Errorf("abort classification: %s origin without initial message marker, refused", kind)
	}
	message := bytes.SplitN(report[len(marker):], []byte{'\n'}, 2)[0]
	if kind == "fatal" && bytes.Equal(message, []byte("all goroutines are asleep - deadlock!")) {
		kind = "deadlock"
	}
	return abortView{kind, message, output}, nil
}

func checkedAbortView(stderr []byte, e crashEvidence) (abortView, error) {
	if err := e.validate(); err != nil {
		return abortView{}, err
	}
	if !bytes.HasSuffix(stderr, []byte("\nexit status 2\n")) {
		return abortView{}, fmt.Errorf("abort classification: expected the child's exact exit status 2 trailer")
	}
	// Strip ONLY go run's trailer; the preceding LF belongs to the report.
	body := stderr[:len(stderr)-len("exit status 2\n")]
	if e.enabled && len(e.report) != 0 {
		if !bytes.HasSuffix(body, e.report) {
			return abortView{}, fmt.Errorf("crash evidence: report is not the entire byte-identical stderr suffix")
		}
		kind, err := originKind(e.report)
		if err != nil {
			return abortView{}, err
		}
		if kind == "panic" {
			return makeAbortView(kind, e.report, body[:len(body)-len(e.report)])
		}
		// fatal's messages precede m.dying and are absent from the copy.
		// The bytes before that copied trace are not authenticated output.
	}
	// Strict fallback for init aborts and pre-dying fatal reports. EVERY raw
	// marker counts, including LF TAB continuations. The old exemption made
	// print("panic: forged\n\t");panic("actual") a false observation.
	panics, fatals := bytes.Count(body, []byte("panic: ")), bytes.Count(body, []byte("fatal error: "))
	marker := []byte("panic: ")
	if panics != 1 {
		if panics != 0 || fatals != 1 {
			return abortView{}, fmt.Errorf("abort classification: ambiguous raw continuation/output markers, refused")
		}
		marker = []byte("fatal error: ")
	}
	start := bytes.Index(body, marker)
	if start != 0 && body[start-1] != '\n' {
		return abortView{}, fmt.Errorf("stderr split: raw report marker glued to program output, refused")
	}
	report := body[start:]
	kind, err := originKind(report)
	if err != nil {
		return abortView{}, err
	}
	if kind == "fatal" && (panics != 0 || fatals != 1) {
		return abortView{}, fmt.Errorf("abort classification: ambiguous fatal message/output before m.dying, refused")
	}
	return makeAbortView(kind, report, body[:start])
}

func observedOutput(stderr []byte, status string, e crashEvidence) ([]byte, error) {
	if err := e.validate(); err != nil {
		return nil, err
	}
	if status == "ok" || status == "race" {
		if e.enabled && (len(e.report) != 0 || len(e.ack) == 0) {
			return nil, fmt.Errorf("crash evidence: %s run requires registration and empty crash report", status)
		}
		return splitNonAbortStderr(stderr, status)
	}
	view, err := checkedAbortView(stderr, e)
	if err != nil {
		return nil, err
	}
	if view.kind != status {
		return nil, fmt.Errorf("stderr split: actual %s report cannot be observed as %s", view.kind, status)
	}
	return view.output, nil
}
