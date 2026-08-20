package main

// BUG-064 edge: the trigger is the transitive init CLOSURE, not
// crypto/rand specifically. crypto/sha256's inittask deps never name
// crypto/internal/entropy/v1.0.0 directly — the escaped prefix arrives
// deps-of-deps (via crypto/internal/fips140/drbg), so the worklist's
// re-escape fires on a row the source program never imports. Any of
// the ~39 non-internal std packages whose closure reaches the fips140
// entropy module (measured from inittask-std.tsv, 2026-08-20: the
// whole crypto family, net/http, expvar, ...) reproduces; sha256 is
// the smallest familiar one.

import (
	_ "crypto/sha256"

	"esc"
)

func inittaskEscapeClosure() int {
	return esc.Seq * 2
}

func main() {
	println(inittaskEscapeClosure())
}
