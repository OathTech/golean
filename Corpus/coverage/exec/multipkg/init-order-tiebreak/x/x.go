package x

import "rec"

// Symbol name: "x..inittask" — sorts AFTER "x-y..inittask", so x
// records SECOND even though "x" < "x-y" as import paths.
var V = rec.Push(1)
