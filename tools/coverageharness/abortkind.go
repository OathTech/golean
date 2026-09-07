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

// abortKind classifies terminal evidence, with no expected-status input.
// Both the original panic-during-fatal case and a program-printed fake panic
// prefix must never make an actual fatal execution into a panic observation.
// The same-run crash channel is mandatory (crashview.go, A-R6).
func abortKind(stderr []byte, e crashEvidence) (string, error) {
	view, err := checkedAbortView(stderr, e)
	return view.kind, err
}
