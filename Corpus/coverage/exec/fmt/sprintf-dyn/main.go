package main

// DYNAMIC fmt conformance (W4.3 item 1 landing C — cause 9 of the
// rendered-tier census; docs/raft-w43-log.md): Sprintf/Sprint/Sprintln
// with a SPREAD []any argument — the DefaultLogger bodies' shape and
// the replay env's recording logger. The format string is parsed at
// RUNTIME over the modeled verb set; each verb dispatches on the
// argument's DYNAMIC kind (error/Stringer first for the stringable
// verbs, then basic kinds + []byte + []uint64). Everything else is a
// fail-closed machine PANIC naming the verb — the two boundary rows
// pin that (go run renders where the machine stops: a visible red,
// never a wrong answer).
//
// gc probes: artifacts/w43/probe-fmt K1-K3 (Sprint's space rule),
// artifacts/w43/probe-b L1-L2 (Sprintln), D3 (Sprint(nil)).

import (
	"errors"
	"fmt"
)

type dynStringer uint64

func (d dynStringer) String() string { return "DS<" + fmt.Sprintf("%d", uint64(d)) + ">" }

type dynPanicky int32

func (p dynPanicky) String() string { panic("dyn stub") }

// logf is the DefaultLogger/recording-logger shape VERBATIM: a
// runtime format and a spread []any, reached through a method on an
// interface (the raft Logger dispatch chain).
type miniLogger interface {
	Infof(format string, v ...any)
}

type recLog struct{ out string }

func (l *recLog) Infof(format string, v ...any) {
	l.out += "INFO " + fmt.Sprintf(format, v...) + "\n"
}

func dynLoggerShape() string {
	var lg miniLogger = &recLog{}
	lg.Infof("%x became follower at term %d", uint64(1), uint64(0))
	lg.Infof("%x [logterm: %d, index: %d] sent %s request to %x at term %d",
		uint64(1), uint64(1), uint64(2), dynStringer(3), uint64(2), uint64(1))
	return lg.(*recLog).out
}

func dynVerbKinds() string {
	f := func(format string, v ...any) string { return fmt.Sprintf(format, v...) }
	return f("%d|%d|%x|%s|%v|%t|%q", -5, uint64(7), uint64(255), "str", true, false, "q\"x") +
		f("|%v|%s", []uint64{1, 2}, []byte("bs"))
}

func dynStringerError() string {
	f := func(format string, v ...any) string { return fmt.Sprintf(format, v...) }
	var err error = errors.New("boom")
	var nilErr error
	return f("%s %v %x", dynStringer(9), err, dynStringer(255)) +
		"|" + f("%v", nilErr)
}

func dynStringerPanic() string {
	f := func(format string, v ...any) string { return fmt.Sprintf(format, v...) }
	return f("[%v]", dynPanicky(3))
}

func dynSprintSpaceRule() string {
	f := func(v ...any) string { return fmt.Sprint(v...) }
	return "[" + f("a", "b", 1, 2, "c", 3) + "][" + f(1, 2, 3) + "][" + f("a", 1, "b") + "]"
}

func dynSprintln() string {
	f := func(v ...any) string { return fmt.Sprintln(v...) }
	return f("a", 1, "b", 2) + f()
}

func dynSprintNil() string {
	f := func(v ...any) string { return fmt.Sprint(v...) }
	return "[" + f(nil) + "]"
}

// ---- fail-closed boundary rows (red BY DESIGN: go renders, the
// machine's dyn shim panics naming the gap) ----

func dynUnmodeledKind() string {
	f := func(format string, v ...any) string { return fmt.Sprintf(format, v...) }
	return f("%v", 1.5)
}

func dynArityMismatch() string {
	f := func(format string, v ...any) string { return fmt.Sprintf(format, v...) }
	return f("%d %d", 1)
}

// ---- R4-M-1 (audit fix round): FIXED-ARITY Sprint/Sprintln — the
// single most common fmt.Sprint shape a Go programmer writes
// (probe r4-p6). gc semantics: exactly Sprint(args...) after
// variadic packing; the space rule and rendering live in the SAME
// differentially-pinned dyn shims the spread rows above exercise —
// the desugar packs the args into a []any and calls them. The first
// version REFUSED these forms, with a comment saying the JC-17
// quarantine witnesses "depend on fmt.Sprint refusing" — a
// corpus-scoped refusal inversion (common Go turned away to keep a
// test fixture stable); the witnesses now use a genuinely-unmodeled
// cause instead. ----
func dynSprintFixedArity() string {
	return fmt.Sprint("a=", 1, " b=", true) // gc: "a=1 b=true"
}

func dynSprintlnFixedArity() string {
	return fmt.Sprintln("a", 1, true) // gc: "a 1 true\n"
}

func main() {
	println(dynLoggerShape(), dynVerbKinds(), dynStringerError(),
		dynStringerPanic(), dynSprintSpaceRule(), dynSprintln(),
		dynSprintNil(), dynUnmodeledKind(), dynArityMismatch(),
		dynSprintFixedArity(), dynSprintlnFixedArity())
}
