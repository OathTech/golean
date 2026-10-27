package pm

import (
	"rec"
	_ "zp"
)

// Gated by zp (a node: its initializer is residual WORK under gc's
// staticinit), so this package waits and pn records first.
var V = rec.Push("p", 1)
