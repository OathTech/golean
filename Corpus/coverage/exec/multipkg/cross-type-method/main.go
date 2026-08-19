package main

// Multi-package guardrail (raft W1.1, 2026-08-18): a cross-package TYPE
// with methods. The subject constructs the imported struct by composite
// literal, takes its address for a pointer-receiver method, and reads a
// field — pinning that an imported source-package type gets a REAL
// TypeDef (path-keyed TypeId) with its method set, not a BUG-009-style
// existence marker whose calls refuse.

import "counter"

func crossTypeMethod() int {
	c := counter.Counter{N: 40}
	c.Inc()
	c.Inc()
	d := counter.Counter{N: 5}
	return c.Get() + d.Get()
}

func main() {}
