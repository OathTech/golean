package main

// BUG-064 control: single-package immunity, pinned GREEN before and
// after the fix. specInitOrder returns early below two source units
// (load.go), so the init graph — and the double-escaping worklist —
// is never built for a single-package program. This is why the whole
// pre-W4 corpus never hit BUG-064, and it is the early return that
// makes raft's G-1 jitter draw measurable in a single-package probe
// (raft-w3 log §2.5).

import (
	_ "crypto/rand"
)

func inittaskEscapeSingle() int {
	return 7
}

func main() {
	println(inittaskEscapeSingle())
}
