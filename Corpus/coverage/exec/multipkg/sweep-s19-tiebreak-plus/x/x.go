package x

import "rec"

// Symbol name "x..inittask": sorts AFTER "x+y..inittask" ('+' 0x2b <
// '.' 0x2e), so x records second although "x" < "x+y" as import paths.
var V = rec.Push(1)
