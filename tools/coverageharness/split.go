package main

// The oracle's fd-2 SPLIT (stdlib slice 3, 2026-09-04): the differential's
// `output` observation field is the program's own stderr — the bytes
// `print`/`println` wrote — and gc writes its abort report (`panic: …`,
// `fatal error: …`, the TSan block) to the SAME descriptor, AFTER the
// program's bytes (the runtime flushes prints before printpanics;
// runtime/print.go gwrite → writeErr is synchronous). `go run` then appends
// its own trailer line `exit status N`. This file recovers the program's
// prefix from a captured stderr, FAIL-CLOSED: every ambiguous shape refuses
// by name (the runner turns that into a red row, never a guessed split).
//
// Non-abort rules (abort kind/message/output share crashview.go's checked
// view; a raw legacy query has no continuation exemption):
//   ok        no trailer; the whole stderr is the program's output.
//   race      TSan's report interleaves ASYNCHRONOUSLY with the program's
//             prints and the program continues past it (exit 66 at the end),
//             so a program prefix is not well-defined: any byte before the
//             first `==================` line refuses ("race rows with program
//             output are not comparable"); an empty prefix passes. Bytes the
//             program prints AFTER the report are NOT detected (recorded gap:
//             the race lane's observation is the fixed refusal on both sides).
// The prefix must be valid UTF-8 (the observation JSON carries it as a
// string; the Lean encoder refuses the same way) and is printed as a JSON
// string literal with HTML escaping off.

import (
	"bytes"
	"encoding/json"
	"fmt"
	"regexp"
	"strings"
	"unicode/utf8"
)

var exitTrailerRe = regexp.MustCompile(`(?m)^exit status \d+\n\z`)

// Accept historical plain headers for standalone split tests, and the
// scoped system headers used by current oracle runs. Terminal classification
// separately requires the pinned system origin; splitting is not a verdict.
var abortTraceHeaderRe = regexp.MustCompile(`(?:^|\n)(?:goroutine \d+(?: gp=0x[0-9a-f]+ m=(?:nil|-?\d+ mp=0x[0-9a-f]+))? \[[^\r\n]*\]:|runtime stack:)\n`)

// stripTrailer removes `go run`'s `exit status N` trailer (required for every
// non-ok status; refused if absent — a run that did not report the child's
// exit is not a verdict).
func stripTrailer(stderr []byte) ([]byte, error) {
	loc := exitTrailerRe.FindIndex(stderr)
	if loc == nil {
		return nil, fmt.Errorf("stderr split: no `exit status N` trailer from go run (the child's exit was not reported; not a verdict)")
	}
	return stderr[:loc[0]], nil
}

// splitNonAbortStderr returns the program's own output prefix from a
// captured ok/race stderr, or a refusal naming its cause. Abort statuses go
// through crashview.go's checked view (observedOutput), which also holds
// the mandatory same-run crash channel.
func splitNonAbortStderr(stderr []byte, status string) ([]byte, error) {
	var prefix []byte
	switch status {
	case "ok":
		if exitTrailerRe.Match(stderr) {
			return nil, fmt.Errorf("stderr split: an `exit status N` trailer on an ok run (the child did not exit 0)")
		}
		prefix = stderr
	case "race":
		body, err := stripTrailer(stderr)
		if err != nil {
			return nil, err
		}
		i := bytes.Index(body, []byte("=================="))
		if i < 0 {
			return nil, fmt.Errorf("stderr split: no TSan report block on a race run, refused")
		}
		if i != 0 {
			return nil, fmt.Errorf("stderr split: %d byte(s) of program output before the TSan report — race rows with program output are not comparable (the report interleaves asynchronously with the program's prints), refused", i)
		}
		prefix = body[:0]
	default:
		return nil, fmt.Errorf("stderr split: unknown status %q", status)
	}
	if !utf8.Valid(prefix) {
		return nil, fmt.Errorf("stderr split: the program output is not valid UTF-8 (%d bytes) — the observation JSON cannot carry it byte-exactly, refused", len(prefix))
	}
	return prefix, nil
}

// outputLiteral renders the prefix as a JSON string literal (no trailing
// newline, HTML escaping off — the Lean decoder parses either).
func outputLiteral(prefix []byte) (string, error) {
	if !utf8.Valid(prefix) {
		return "", fmt.Errorf("observation string is not valid UTF-8 (%d bytes), refused", len(prefix))
	}
	var sb strings.Builder
	enc := json.NewEncoder(&sb)
	enc.SetEscapeHTML(false)
	if err := enc.Encode(string(prefix)); err != nil {
		return "", err
	}
	return strings.TrimSuffix(sb.String(), "\n"), nil
}
