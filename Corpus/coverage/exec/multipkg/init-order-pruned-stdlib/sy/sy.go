package sy

import (
	// unicode/utf8 is likewise pure code with no initialization work:
	// no inittask, no ordering effect.
	_ "unicode/utf8"

	"rec"
)

var V = rec.Push(2)
