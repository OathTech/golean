package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout. DESIGNED RED (BUG-093 iii): a print during
// package initialization, reached through a package-level variable's initializer rather than an init() body.

func announce() int {
	println("var init prints")
	return 3
}

var seeded = announce()

func readsInitVar() int { return seeded }

func main() { readsInitVar() }
