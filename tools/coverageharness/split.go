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
// Rules, per expected status (mirrors scripts/diff-coverage's classification):
//   ok        no trailer; the whole stderr is the program's output.
//   panic     exactly ONE line-start `panic: ` (position 0 or after '\n');
//             the prefix ends there. Zero candidates → refuse (a print without
//             a trailing newline glues onto the report: `abcpanic: x` — the
//             boundary is not recoverable); two or more → refuse (a payload or
//             a program line that itself begins `panic: ` — ambiguous).
//   fatal,    the runtime's `fatal error: ` line, or — the unwinding shape,
//   deadlock  `defer m.Unlock()` in a panicking frame — a leading `panic: `
//             line with the fatal on a tab-indented continuation: the block
//             starts at the earliest line-start marker; more than one
//             line-start `panic: ` or more than one line-start `fatal error: `
//             refuses.
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

// lineStarts returns every offset at which `marker` occurs at a line start.
func lineStarts(b, marker []byte) []int {
	var out []int
	off := 0
	for {
		i := bytes.Index(b[off:], marker)
		if i < 0 {
			return out
		}
		p := off + i
		if p == 0 || b[p-1] == '\n' {
			out = append(out, p)
		}
		off = p + 1
	}
}

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

// splitStderr returns the program's own output prefix from a captured
// stderr, or a refusal naming its cause.
func splitStderr(stderr []byte, status string) ([]byte, error) {
	var prefix []byte
	switch status {
	case "ok":
		if exitTrailerRe.Match(stderr) {
			return nil, fmt.Errorf("stderr split: an `exit status N` trailer on an ok run (the child did not exit 0)")
		}
		prefix = stderr
	case "panic":
		body, err := stripTrailer(stderr)
		if err != nil {
			return nil, err
		}
		ps := lineStarts(body, []byte("panic: "))
		switch len(ps) {
		case 1:
			prefix = body[:ps[0]]
		case 0:
			return nil, fmt.Errorf("stderr split: no line-start `panic: ` block — a print without a trailing newline glued onto the panic report (or no report at all); the boundary is not recoverable, refused")
		default:
			return nil, fmt.Errorf("stderr split: %d line-start `panic: ` lines — ambiguous (a program line or a payload line that itself begins `panic: `), refused", len(ps))
		}
	case "fatal", "deadlock":
		body, err := stripTrailer(stderr)
		if err != nil {
			return nil, err
		}
		fs := lineStarts(body, []byte("fatal error: "))
		ps := lineStarts(body, []byte("panic: "))
		if len(fs) > 1 || len(ps) > 1 || len(fs)+len(ps) == 0 {
			return nil, fmt.Errorf("stderr split: %d line-start `fatal error: ` and %d line-start `panic: ` lines — the abort block must start at exactly one line-start marker (or the panic-then-fatal unwinding shape), refused", len(fs), len(ps))
		}
		start := -1
		for _, p := range append(fs, ps...) {
			if start < 0 || p < start {
				start = p
			}
		}
		prefix = body[:start]
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
	var sb strings.Builder
	enc := json.NewEncoder(&sb)
	enc.SetEscapeHTML(false)
	if err := enc.Encode(string(prefix)); err != nil {
		return "", err
	}
	return strings.TrimSuffix(sb.String(), "\n"), nil
}
