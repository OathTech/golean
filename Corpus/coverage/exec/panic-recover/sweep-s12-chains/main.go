package main

// Sweep S12 — nested panics and re-panics: the REPORT's shape (matrix cells
// F04–F07, F09, F10; lane sweep/s12-panic-recover, 2026-10-27). gc prints the
// chain oldest first (runtime/panic.go printpanics), each entry with its
// own ` [recovered]` suffix; the compared observation is the FIRST line, so
// the head (oldest) entry and its suffix are what these rows pin. Every
// adjacent pair here is UNEQUAL, so no `repanicCollapse` draw (strict rows).
// The machine: `renderPanicHead` / `recoveredSuffix` over the chain's head.

// Three entries, none recovered: `panic: a` / `\tpanic: b` / `\tpanic: c`.
func chainThreeDeep() {
	defer func() { panic("c") }()
	defer func() { panic("b") }()
	panic("a")
}

// The middle deferred call recovers `a` and panics `b`; the last panics `c`:
// `panic: a [recovered]` / `\tpanic: b` / `\tpanic: c`.
func chainMiddleRecovered() {
	defer func() { panic("c") }()
	defer func() {
		_ = recover()
		panic("b")
	}()
	panic("a")
}

// Recovered, then re-panicked with a value of a DIFFERENT kind.
func repanicDifferentKind() {
	defer func() {
		_ = recover()
		panic(7)
	}()
	panic("s")
}

// Recovered by the newest deferred call; an OLDER deferred call then panics.
// The recovery COMPLETES when that deferred call returns (the recovered
// entry leaves the chain and the frame resumes its normal deferred drain),
// so the older call's panic starts a FRESH chain: the report is `panic:
// second` alone — no `[recovered]` line (probed at the pin; contrast
// chainMiddleRecovered, where the re-panic is raised INSIDE the recovering
// deferred call and the recovered entry is still on the chain).
func repanicAfterRecoveryNewDefer() {
	defer func() { panic("second") }()
	defer func() { _ = recover() }()
	panic("first")
}

// Two DIFFERENT run-time faults: an index fault recovered, a nil dereference
// raised in the deferred call.
func repanicTwoDifferentFaults() {
	defer func() {
		_ = recover()
		var p *int
		_ = *p
	}()
	var s []int
	_ = s[0]
}

// `panic(recover())` one frame too deep: that recover() is nil (gc's rule),
// so the re-panic is the nil-argument error; the head line is the original.
func repanicFromDeferDepth2() {
	defer func() {
		defer func() {
			panic(recover())
		}()
	}()
	panic("x")
}

func main() {}
