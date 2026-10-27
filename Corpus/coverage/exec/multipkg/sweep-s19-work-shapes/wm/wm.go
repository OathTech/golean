package wm

import (
	"rec"
	_ "zw"
)

// Gated by zw (a node: its initializer is residual WORK under gc's
// staticinit), so this package waits and wn records first.
var V = rec.Push("w", 1)
