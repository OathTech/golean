package am

import (
	"rec"
	_ "za"
)

// Gated by za (a node: its initializer is residual WORK under gc's
// staticinit), so this package waits and an records first.
var V = rec.Push("a", 1)
