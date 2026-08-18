package aaa

import (
	// Blank import: `sync` contributes NOTHING to this package's
	// semantics — it is here purely for its position in the program's
	// initialization list (spec#Program_initialization). aaa is not
	// ready until sync (and sync's whole transitive closure) has
	// initialized, which is what delays aaa past bbb.
	_ "sync"

	"rec"
)

// A records WHEN aaa initialized (the push count).
var A int

func init() {
	A = rec.Push(1)
}
