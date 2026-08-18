package dm

import (
	// Blank import: zdy has run-time init work, so it IS a node and
	// this import genuinely gates dm.
	_ "zdy"

	"rec"
)

var V = rec.PushD(1)
