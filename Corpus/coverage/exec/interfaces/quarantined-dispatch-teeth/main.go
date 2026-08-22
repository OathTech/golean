package main

// The logger-teeth pair as corpus rows (W4.3 item 4 — the W4.2 owed
// row "fail-closed interface-stub dispatch"; docs/raft-w43-log.md).
// The W4.2 probe pair witnessed, on the raft tree, that (a) a call
// dispatched through an interface to a QUARANTINED concrete method is
// a visible machine STOP (never a silent no-op), and (b) installing a
// modeled implementation through the same seam runs green. This
// family pins that mechanism in the gated corpus with a miniature of
// the same shape: the same interface, two concrete impls — one inside
// the modeled subset, one whose body keeps a standing refusal
// (reflect.TypeOf — retargeted by audit R4-M-1 when the fixed-arity
// fmt.Sprint it used before became MODELED; the JC-17 lost-witness
// discipline), so its METHOD is per-declaration quarantined and
// dispatch to it stops the machine the moment it is called.

import "reflect"

type miniLog interface {
	Infof(format string, v ...any)
}

// installed: the harness-logger shape — a body inside the modeled
// subset (records without formatting).
type quietLog struct{ n int }

func (l *quietLog) Infof(format string, v ...any) { l.n += len(v) + len(format) }

// uninstalled: the DefaultLogger shape — the body keeps a standing
// refusal (reflect.TypeOf asks a DYNAMIC-type question the frontend's
// closed static world does not carry), so
// the method lands as a fail-closed stub.
type fancyLog struct{ out string }

func (l *fancyLog) Infof(format string, v ...any) {
	l.out += "x: " + reflect.TypeOf(format).String()
}

func teethInstalled() int {
	var lg miniLog = &quietLog{}
	lg.Infof("%x became follower at term %d", uint64(1), uint64(0))
	lg.Infof("ok", nil)
	return lg.(*quietLog).n
}

// RED BY DESIGN: go run formats; the machine stops at the quarantined
// stub the moment the dispatch lands — the teeth.
func teethUninstalled() string {
	var lg miniLog = &fancyLog{}
	lg.Infof("boom", uint64(1))
	return lg.(*fancyLog).out
}

func main() { println(teethInstalled(), teethUninstalled()) }
