package main

import (
	"errors"
	"fmt"
	"runtime"
)

// AUDIT PROBES, stdlib half (pre-merge audit of core/panic-preprint-1003,
// 2026-10-03; [AGENT] auditor). The handoff's §6 names the reachability-
// pruned library `Error()` bodies as a follow-up: these rows show what the
// machine answers today for the most common Go idiom, `panic(err)` with a
// library error.

type ev struct{ s string }

func (e ev) Error() string {
	println("CALLED:" + e.s)
	return e.s
}

// S1 errors.New: (*errorString).Error reads a field
func errorsNewPayload() { panic(errors.New("lib")) }

// S2 fmt.Errorf: a wrapError / *fmt.wrapError or *errors.errorString
func fmtErrorfPayload() { panic(fmt.Errorf("w: %d", 3)) }

// S3 the recovered errors.New box re-panicked (identity)
func errorsNewRepanic() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(errors.New("again"))
}

// S4 Goexit from a deferred call while panicking with an error payload: the
// panic is abandoned by the exiting goroutine (main) — gc's own line
func goexitDuringErrorPanic() {
	defer func() { runtime.Goexit() }()
	panic(ev{"abandoned"})
}

// S5 the method prints to stdout through fmt before returning
type printer int

func (printer) Error() string {
	fmt.Println("side-effect")
	return "printed"
}

func methodPrintsStdout() { panic(printer(1)) }
