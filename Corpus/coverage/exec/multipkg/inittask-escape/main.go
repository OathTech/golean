package main

// H-9 / BUG-064 guardrail (raft W4.0, 2026-08-20): the inittask
// double-escape. buildInitGraph's worklist mixed import PATHS (source
// units) with linker symbol PREFIXES (the table's dep columns, already
// percent-escaped), and pathToPrefix escaped the prefixes AGAIN
// ('%' -> '%25'), so any MULTI-package program whose stdlib init
// closure reaches crypto/internal/entropy/v1.0.0 (the one escaped
// prefix in the Go 1.26 stdlib) refused with "crypto/internal/entropy/
// v1%2e0%2e0 is not in the stdlib inittask table" — the table HAS that
// row; the lookup asked for the double-escaped name.
//
// crypto/rand is raft's route to it (the election-jitter draw). The
// import is blank on purpose: the bug is in the initialization-order
// GRAPH, reached before any declaration is read, so no surface use is
// needed — and none would lower anyway (crypto/rand's surface is not
// modeled).
//
// Siblings: inittask-escape-closure pins that the trigger is the
// transitive init CLOSURE (crypto/sha256 never names entropy directly);
// inittask-escape-single pins single-package immunity (specInitOrder
// returns early below two source units, which is why no single-package
// case ever hit this).

import (
	_ "crypto/rand"

	"esc"
)

func inittaskEscape() int {
	return esc.Seq
}

func main() {
	println(inittaskEscape())
}
