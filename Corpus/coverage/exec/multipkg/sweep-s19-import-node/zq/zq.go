package zq

import "errors"

// errors.New's shape is one staticinit MAY fold (an inlined single
// return), but zq imports errors, which IS a node (inittask-std.tsv:
// errors 1), so zq bears a record whatever happens to E: a node under
// both rules, no uncertainty, no refusal.
var E = errors.New("x")
