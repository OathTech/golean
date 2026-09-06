package main

import (
	"bytes"
	"fmt"
	"regexp"
	"runtime"
)

// This is the first crashing trace block from the SAME oracle execution,
// scoped to GOTRACEBACK=system. See the source-pinned design note: fatalpanic
// traces its gopanic caller (printed as "panic"); fatalthrow traces its fatal
// or throw caller. Source positions supplement that runtime call-path
// argument; source paths or arbitrary printed function names alone do not
// establish a terminal class. Unknown shapes refuse.
var systemGoroutineHeader = regexp.MustCompile(`^goroutine [0-9]+ gp=0x[0-9a-f]+ m=(?:nil|-?[0-9]+ mp=0x[0-9a-f]+) \[[^\r\n]*\]:$`)
var terminalFrame = regexp.MustCompile(`^(panic|runtime\.fatal|runtime\.throw)\([^\r\n]*\)$`)
var terminalSource = regexp.MustCompile(`^\t/[^\t\r\n]*/src/runtime/panic\.go:(879|1253|1229) \+0x[0-9a-f]+ fp=0x[0-9a-f]+ sp=0x[0-9a-f]+ pc=0x[0-9a-f]+$`)

func pinnedTraceKind(trace []byte) (string, error) {
	if runtime.Version() != "go1.26.5" {
		return "", fmt.Errorf("abort classification: runtime frame contract requires pinned go1.26.5")
	}
	// No TrimSpace: printindented puts TAB after every payload LF. A fake
	// payload header/frame/source must remain visibly indented. This fact
	// does not authenticate program output; abortKind also checks boundaries.
	lines := bytes.Split(trace, []byte{'\n'})
	if len(lines) < 3 || !(bytes.Equal(lines[0], []byte("runtime stack:")) || systemGoroutineHeader.Match(lines[0])) {
		return "", fmt.Errorf("abort classification: missing pinned system trace header, refused")
	}
	frame, source := terminalFrame.FindSubmatch(lines[1]), terminalSource.FindSubmatch(lines[2])
	if frame == nil || source == nil {
		return "", fmt.Errorf("abort classification: unknown first runtime frame/source, refused")
	}
	switch string(frame[1]) + ":" + string(source[1]) {
	case "panic:879":
		if bytes.Equal(lines[0], []byte("runtime stack:")) {
			return "", fmt.Errorf("abort classification: panic on a runtime stack is not an ordinary panic origin, refused")
		}
		return "panic", nil
	case "runtime.fatal:1253", "runtime.throw:1229":
		return "fatal", nil
	default:
		return "", fmt.Errorf("abort classification: mismatched runtime symbol/source pin, refused")
	}
}

// abortKind classifies raw terminal evidence, with no expected-status input.
// Both the original panic-during-fatal case and a program-printed fake panic
// prefix must never make an actual fatal execution into a panic observation.
func abortKind(stderr []byte) (string, error) {
	if !bytes.HasSuffix(stderr, []byte("\nexit status 2\n")) {
		return "", fmt.Errorf("abort classification: expected the child's exact exit status 2 trailer")
	}
	body, err := stripTrailer(stderr)
	if err != nil {
		return "", err
	}
	prefix, err := splitStderr(stderr, "panic")
	if err != nil {
		prefix, err = splitStderr(stderr, "fatal")
		if err != nil {
			return "", err
		}
	}
	report := body[len(prefix):]
	header := abortTraceHeaderRe.FindIndex(report)
	if header == nil {
		return "", fmt.Errorf("abort classification: missing trace header")
	}
	// Output can forge a panic marker AND first trace before a real fatal
	// report. A later fatal marker makes that selected boundary untrusted;
	// do not classify it using the earlier printed frame. Unknown marker-
	// bearing stack diagnostics also refuse: no general frame grammar here.
	if bytes.Contains(report[header[0]:], []byte("fatal error: ")) {
		return "", fmt.Errorf("abort classification: fatal marker after selected trace header; report boundary is ambiguous, refused")
	}
	if bytes.Contains(report[header[1]:], []byte("\nruntime stack:")) {
		return "", fmt.Errorf("abort classification: additional runtime stack block after the selected origin, refused")
	}
	kind, err := pinnedTraceKind(report[header[0]+2:])
	if err != nil {
		return "", err
	}
	// Recheck the output boundary for the ACTUAL terminal kind. In
	// particular, a glued printed panic prefix before runtime.fatal cannot
	// provide a well-defined fatal message/output even with an authentic
	// runtime origin, and must refuse rather than fabricate that split.
	actualPrefix, err := splitStderr(stderr, kind)
	if err != nil {
		return "", err
	}
	if !bytes.Equal(actualPrefix, prefix) {
		return "", fmt.Errorf("abort classification: terminal kind disagrees with report boundary, refused")
	}
	if kind == "fatal" {
		for _, line := range bytes.Split(report[:header[0]], []byte{'\n'}) {
			line = bytes.TrimPrefix(line, []byte{'\t'})
			if bytes.HasPrefix(line, []byte("fatal error: ")) {
				if bytes.Equal(line, []byte("fatal error: all goroutines are asleep - deadlock!")) {
					return "deadlock", nil
				}
				return "fatal", nil
			}
		}
		return "", fmt.Errorf("abort classification: fatal origin without a leading fatal message, refused")
	}
	return kind, nil
}
