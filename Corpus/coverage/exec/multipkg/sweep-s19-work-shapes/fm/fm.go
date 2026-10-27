package fm

import (
	"rec"
	_ "zf"
)

// Gated by zf (a node: its initializer is residual WORK under gc's
// staticinit), so this package waits and fn records first.
var V = rec.Push("f", 1)
