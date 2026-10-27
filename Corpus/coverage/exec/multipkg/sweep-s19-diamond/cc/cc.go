package cc

import "rec"

// Inits counts how many times this package's init ran: the shared
// dependency of a diamond initializes exactly once.
var Inits int

var V = rec.Push(1)

// W is set by init, after V: both importers see 7.
var W int

func init() { Inits++; W = 7 }
