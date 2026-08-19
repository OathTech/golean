package main

// Multi-package guardrail (raft W1.1 delta-review F1, 2026-08-18): the
// order gc breaks ties in is NOT the order of the import paths. It is
// the order of the LINKER SYMBOL NAMES built from them.
//
// spec#Program_initialization sorts "the list of all packages ... by
// import path". gc schedules `..inittask` records and picks, at each
// step, the lexicographically first READY record BY SYMBOL NAME
// (deps/go/src/cmd/link/internal/ld/inittask.go — `lexHeap` compares
// `ldr.SymName`; the record for package p is named
// `objabi.PathToPrefix(p) + "..inittask"`).
//
// Appending `..inittask` is not order-preserving. For the two paths
// here:
//
//	"x"    <  "x-y"          (import-path order: '\0' < '-')
//	"x-y..inittask"  <  "x..inittask"
//	                         (symbol order: '-' (0x2d) < '.' (0x2e))
//
// so gc initializes `x-y` BEFORE `x`, inverting the spec's stated
// sort. Both packages are ready at step one (each imports only the
// pruned recorder), so the tie-break is the ONLY thing deciding the
// order, and the observation is the tie-break.
//
// A model that sorts by import path reports 12. Go reports 21.
//
// `PathToPrefix` also percent-escapes bytes that cannot appear in a
// symbol name — anything <= ' ', '%', '"', >= 0x7F, and '.' after the
// last '/' — which perturbs the order further; those paths are outside
// what the frontend admits today (dotted paths refuse, design note
// §3.2), so a hyphen is the reachable witness.

import (
	"rec"
	_ "x"
	_ "x-y"
)

// tiebreakSeq is 21 — `x-y` initializes first, because
// "x-y..inittask" sorts before "x..inittask".
func tiebreakSeq() int {
	return rec.Seq
}

func main() {}
