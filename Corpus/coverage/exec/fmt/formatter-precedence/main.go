package main

// fmt.Formatter precedence pins (W4.3 audit fix round, R1-F2 —
// docs/raft-w43-log.md). gc's fmt consults fmt.Formatter FIRST — for
// EVERY verb, ahead of error/Stringer and ahead of the kind matrix
// (fmt/print.go handleMethods). The frontend never checked it: a
// Formatter+Stringer type silently rendered through String(), and a
// Formatter-only named int rendered through the int matrix — silent
// wrong answers both (gc-probed .tmp/fixround-probes/f2{,b}:
// "FMT:v:1|FMT:s:2|FMT:d:3", "fd:d|fd:v", and at composite depth
// "{FMT:v:1}"). Static sites now REFUSE types implementing
// fmt.Formatter (types.Implements against the type-checked fmt
// package's Formatter) — all three rows are RED BY DESIGN at
// frontend-export. Modeling Format() would mean modeling fmt.State;
// nothing in scope needs it. The DYNAMIC shim cannot see Formatter at
// runtime — that bound is recorded at goleanShimFmtDynVerb.

import "fmt"

type fmtBoth int // Formatter AND Stringer: Format must win in gc

func (f fmtBoth) String() string { return "STR" }
func (f fmtBoth) Format(s fmt.State, verb rune) {
	fmt.Fprintf(s, "FMT:%c:%d", verb, int(f))
}

type fmtOnly int // Formatter only, underlying int: Format beats %d

func (f fmtOnly) Format(s fmt.State, verb rune) {
	fmt.Fprintf(s, "fd:%c", verb)
}

func formatterOverStringer() string {
	return fmt.Sprintf("%v|%s", fmtBoth(1), fmtBoth(2))
}

func formatterOverKindMatrix() string {
	return fmt.Sprintf("%d|%v", fmtOnly(4), fmtOnly(5))
}

type wrapFmt struct{ F fmtBoth }

func formatterAtDepth() string {
	return fmt.Sprintf("%v", wrapFmt{1})
}

func main() {
	println(formatterOverStringer(), formatterOverKindMatrix(),
		formatterAtDepth())
}
