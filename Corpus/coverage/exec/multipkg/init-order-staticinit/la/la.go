package la

import (
	// Blank import: gc pruned zq, so this gates NOTHING. The frontend
	// thinks it does.
	_ "zq"

	"rec"
)

var V = rec.Push(1)
