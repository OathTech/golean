package mm

import (
	"rec"
	_ "zm"
)

// Gated by zm (a node: its initializer is residual WORK under gc's
// staticinit), so this package waits and mn records first.
var V = rec.Push("m", 1)
