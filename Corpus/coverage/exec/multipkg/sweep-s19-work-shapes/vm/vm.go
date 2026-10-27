package vm

import (
	"rec"
	_ "zv"
)

// Gated by zv (a node: its initializer is residual WORK under gc's
// staticinit), so this package waits and vn records first.
var V = rec.Push("v", 1)
