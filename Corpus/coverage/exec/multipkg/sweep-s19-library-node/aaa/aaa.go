package aaa

import (
	"rec"
	"strings"
)

// strings is a SOURCE-THROUGH library unit (lowered from the pinned
// GOROOT source) AND a node of gc's schedule (inittask-std.tsv: strings 1
// — it has residual init work). Its node fact comes from the table, not
// from the lowered source (buildInitGraph's library branch), so aaa is
// gated by it and bbb, ready at step one, records first.
var A = rec.Push(1) + len(strings.Repeat("x", 0))
