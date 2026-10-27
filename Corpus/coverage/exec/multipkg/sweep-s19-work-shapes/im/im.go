package im

import (
	"rec"
	_ "zi"
)

// Gated by zi (a node: its initializer is residual WORK under gc's
// staticinit), so this package waits and in records first.
var V = rec.Push("i", 1)
