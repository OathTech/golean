package xy

import "rec"

// Import path "x-y", symbol name "x-y..inittask" — sorts BEFORE
// "x..inittask", so this package records FIRST. The package NAME (xy)
// differs from the last element of its import path (x-y), which is
// legal Go and is what forces the hyphen into the symbol name.
var V = rec.Push(2)
