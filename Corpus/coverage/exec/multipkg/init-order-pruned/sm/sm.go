package sm

import (
	// Blank import: zst contributes nothing but its (absent) position
	// in the schedule. gc pruned it, so this import gates NOTHING.
	_ "zst"

	"rec"
)

var V = rec.PushS(1)
