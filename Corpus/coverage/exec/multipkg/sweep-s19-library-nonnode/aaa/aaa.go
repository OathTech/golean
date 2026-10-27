package aaa

import (
	"cmp"
	"math/bits"
	"rec"
)

// cmp and math/bits are source-through library units with NO residual
// init work (inittask-std.tsv: cmp 0, math/bits 0): gc emits no record
// for either, so these imports gate nothing and aaa is ready at step one.
var A = rec.Push(1) + cmp.Compare(1, 1) + bits.LeadingZeros8(255)
