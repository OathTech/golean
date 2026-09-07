package main

// Observation transport must read bytes from files before passing JSON to
// Bash: command substitution drops NUL, and ad-hoc shell escaping misses
// other JSON control characters. These helpers do not change the observer's
// first-line policy or choose a representation for invalid UTF-8.
import (
	"encoding/json"
	"fmt"
	"unicode/utf8"
)

// observedAbortMessage extracts the actual first panic/fatal message AFTER
// checking the output/report split against the same-run crash channel. LF
// ends the observed line; CR is a payload byte and must survive. Never
// substitute the manifest reason.
func observedAbortMessage(stderr []byte, status string, e crashEvidence) (string, error) {
	if status != "panic" && status != "fatal" {
		return "", fmt.Errorf("abort message: unsupported status %q", status)
	}
	view, err := checkedAbortView(stderr, e)
	if err != nil {
		return "", err
	}
	if view.kind != status {
		return "", fmt.Errorf("abort message: actual %s report cannot be observed as %s", view.kind, status)
	}
	return outputLiteral(view.message)
}

// rawPanicRecord is a transport record for the explicit R-1 string-member
// checker, not a golean-observation-v1 value or a dynamic-type certificate.
// The shared view authenticates the same-run report and its exit-2 trailer;
// the runner separately checks the actual outer process exit and stdout.
// Integer arrays deliberately avoid both UTF-8 replacement and []byte's
// encoding/json base64 representation. Empty byte sequences are always [].
type rawPanicRecord struct {
	Schema       string `json:"schema"`
	Status       string `json:"status"`
	ChildExit    int    `json:"childExit"`
	MessageBytes []int  `json:"messageBytes"`
	OutputBytes  []int  `json:"outputBytes"`
}

func byteIntegers(raw []byte) []int {
	values := make([]int, len(raw))
	for i, b := range raw {
		values[i] = int(b)
	}
	return values
}

func observedAbortRecord(stderr []byte, e crashEvidence) (string, error) {
	view, err := checkedAbortView(stderr, e)
	if err != nil {
		return "", err
	}
	if view.kind != "panic" {
		return "", fmt.Errorf("raw panic record: actual %s report is not panic", view.kind)
	}
	encoded, err := json.Marshal(rawPanicRecord{
		Schema: "golean-raw-panic-v1", Status: "panic", ChildExit: 2,
		MessageBytes: byteIntegers(view.message), OutputBytes: byteIntegers(view.output),
	})
	return string(encoded), err
}

// observationText validates the untouched stdout file before shell capture.
// The Lean comparator still validates the observation schema and values.
// Rejecting invalid UTF-8 explicitly avoids encoding/json's replacement
// behavior. JSON cannot contain a raw NUL (or any unescaped control byte).
func observationText(stdout []byte) (string, error) {
	if !utf8.Valid(stdout) {
		return "", fmt.Errorf("Go output is not a valid observation: stdout is not valid UTF-8")
	}
	if !json.Valid(stdout) {
		return "", fmt.Errorf("Go output is not a valid observation: stdout is not one complete JSON value")
	}
	return string(stdout), nil
}
