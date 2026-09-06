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

// abortMessageLiteral extracts the actual first panic/fatal message AFTER
// checking the existing output/report split. Fatal continuations during
// panic unwinding may have one leading tab. LF ends the observed line; CR
// is a payload byte and must survive. Never substitute the manifest reason.
func abortMessageLiteral(stderr []byte, status string) (string, error) {
	return observedAbortMessage(stderr, status, crashEvidence{})
}

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
