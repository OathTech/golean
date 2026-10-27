package xy

import "rec"

// Import path "x+y" ('+' is a legal import-path character:
// golang.org/x/mod/module importPathOK), symbol "x+y..inittask" — sorts
// BEFORE "x..inittask", so this package records FIRST.
var V = rec.Push(2)
