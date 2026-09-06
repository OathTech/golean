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
//   panic     exactly ONE occurrence of `panic: ` ANYWHERE in the stream
//             (repanic continuations `\n\tpanic: ` excepted), at a line start,
//             followed by gc's goroutine trace header — the prefix ends
//             there (abortBlockStart). A print of the marker text — on its
//             own line, glued to the report, or anywhere — refuses.
//   fatal,    exactly ONE occurrence of `fatal error: ` OR `panic: ` in
//   deadlock  total (the unwinding shape `panic: v [recovered]\n\tfatal
//             error: …` counts once — its fatal line is a continuation), at a
//             line start, followed by the trace header. A printed `panic: …`
//             beside a real `fatal error: ` block (or the converse) refuses.
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

var goroutineHeaderRe = regexp.MustCompile(`\n\ngoroutine \d+ \[`)

// markerOccurrences returns every offset of `marker` in b that is NOT a
// repanic/unwinding CONTINUATION line — gc prints a recovered-and-repanicked
// chain as `panic: first [recovered]\n\tpanic: second` and a fatal raised
// during unwinding as `panic: v [recovered]\n\tfatal error: …` (runtime/
// panic.go printpanics, :734-752 @ go1.26.5): a marker preceded by "\n\t"
// belongs to the block that began above it. Every OTHER occurrence — at a
// line start OR glued mid-line — counts, so a program that printed the
// marker text itself, with or without a trailing newline, is VISIBLE.
func markerOccurrences(b, marker []byte) []int {
	var out []int
	off := 0
	for {
		i := bytes.Index(b[off:], marker)
		if i < 0 {
			return out
		}
		p := off + i
		if !(p >= 2 && b[p-1] == '\t' && b[p-2] == '\n') {
			out = append(out, p)
		}
		off = p + 1
	}
}

// abortBlockStart finds the ONE abort block among the given markers
// (audit fix round A2, 2026-09-05 — fail-closed on every shape a program's
// own prints could confuse): across ALL the markers there must be exactly
// one non-continuation occurrence in total; it must sit at a line start
// (offset 0 or after '\n' — a marker glued to a print that lacked its
// newline is not recoverable: the program's text and gc's report share a
// line); and the block must be WELL-FORMED — the goroutine trace header
// `\n\ngoroutine N [` must follow (gc prints it after the panic/fatal lines
// under the default GOTRACEBACK). Zero or several occurrences refuse by
// name (a print of `panic: …`/`fatal error: …` anywhere makes the split
// ambiguous, even on a line of its own — the block is never guessed).
func abortBlockStart(body []byte, markers ...string) (int, error) {
	var occ []int
	for _, m := range markers {
		occ = append(occ, markerOccurrences(body, []byte(m))...)
	}
	switch len(occ) {
	case 0:
		return -1, fmt.Errorf("stderr split: no %s block found (no report at all), refused", strings.Join(markers, "/"))
	case 1:
	default:
		return -1, fmt.Errorf("stderr split: %d occurrences of %s outside repanic/unwinding continuations — ambiguous (the program printed the marker text itself, or printed without a trailing newline so its text and the report share a line), refused", len(occ), strings.Join(markers, "/"))
	}
	p := occ[0]
	if !(p == 0 || body[p-1] == '\n') {
		return -1, fmt.Errorf("stderr split: the %s block is glued mid-line to the program's output (a print without a trailing newline) — the boundary is not recoverable, refused", strings.Join(markers, "/"))
	}
	if !goroutineHeaderRe.Match(body[p:]) {
		return -1, fmt.Errorf("stderr split: the %s block at offset %d is not followed by gc's goroutine trace header — not a well-formed abort report, refused", strings.Join(markers, "/"), p)
	}
	return p, nil
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
		p, err := abortBlockStart(body, "panic: ")
		if err != nil {
			return nil, err
		}
		prefix = body[:p]
	case "fatal", "deadlock":
		body, err := stripTrailer(stderr)
		if err != nil {
			return nil, err
		}
		// The block starts at the ONE marker — `fatal error: ` for a plain
		// throw/deadlock, `panic: ` for the panic-then-fatal unwinding shape
		// (whose fatal line is a "\n\t" continuation). One in total: a
		// program-printed `panic: …` line beside a real `fatal error: `
		// block (or the converse) is ambiguous and refuses.
		p, err := abortBlockStart(body, "fatal error: ", "panic: ")
		if err != nil {
			return nil, err
		}
		prefix = body[:p]
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
