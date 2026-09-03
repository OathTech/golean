package main

// Shim-refusal UNRECOVERABILITY pins (W4.3 audit fix round, R4-C-3 —
// docs/raft-w43-log.md; probe r4-p2). A golean shim's fail-closed
// refusal used to be an ordinary Go panic — and ordinary panics are
// RECOVERABLE, so the defensive idioms below turned visible refusals
// into SILENT WRONG ANSWERS: machine v=0 ok=false where gc says
// v=42 ok=true; n=0 where gc says 3; "%!v(PANIC=...)" where gc
// renders "a-b". Refusals now route through goleanShimUnsupported —
// a frontend-quarantined stub whose CALL throws GoError.unsupported,
// an interpreter-level stop recover() cannot catch (StepFn throws are
// outside the .panicking machinery entirely). All three rows are RED
// BY DESIGN at frontend-export: a visible coverage gap, never a
// wrong answer.

import (
	"fmt"
	"strconv"
	"strings"
)

// strconv.ParseUint base 0 (prefix auto-detect) is a recorded shim
// bound; the user's recover must NOT swallow the refusal.
func safeParse(s string) (v uint64, ok bool) {
	defer func() {
		if r := recover(); r != nil {
			v, ok = 0, false
		}
	}()
	n, err := strconv.ParseUint(s, 0, 64)
	if err != nil {
		return 0, false
	}
	return n, true
}

func parseRecover() string {
	v, ok := safeParse("0x2a")
	return fmt.Sprintf("v=%d ok=%t", v, ok) // gc: v=42 ok=true
}

// strings.Split with an empty separator (per-rune explode) WAS a
// recorded shim bound; since stdlib-source-1 (2026-09-03) Split is the
// real library body and the explode runs — this row and renderRecover
// now PASS (the recover shape stays, exercising nothing).
func safeChars(s string) (n int) {
	defer func() { _ = recover() }()
	return len(strings.Split(s, ""))
}

func splitRecover() string {
	return fmt.Sprintf("n=%d", safeChars("abc")) // gc: n=3
}

// A refusal raised INSIDE a user String() must not be caught by the
// render path's own recover (goleanShimFmtRenderCall) and re-rendered
// as a plausible "%!v(PANIC=...)" string.
type splitter string

func (s splitter) String() string {
	return strings.Join(strings.Split(string(s), ""), "-")
}

func renderRecover() string {
	return fmt.Sprintf("%v", splitter("ab")) // gc: "a-b"
}

func main() {
	println(parseRecover(), splitRecover(), renderRecover())
}
