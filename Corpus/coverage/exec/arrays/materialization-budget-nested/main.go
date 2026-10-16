package main

// RED BY DESIGN (BUG-078 residual (3), fail-closed 2026-10-12 — [USER]
// Mike, release-readiness item 30: fail-close until fixed,
// relayed): an array TYPE whose FOOTPRINT — its length times its
// element type's, through nested arrays, defined types and struct
// fields — exceeds the interpreter's nested materialization budget
// (1<<24 scalar elements, GoLean/NativeToIR.lean arrayFootprintBudget)
// refuses BY NAME at the wire boundary. Every dimension here is inside
// the per-dimension bound (arrayLenBudget, 1<<16); the product, 2^27,
// is not: on main's binary at c266ce6b one element store into this
// very type measured 19.4 s (a global of it, 34.3 s; its literal
// 53.4 s) against the gate's 60 s per-case wall — an honest kill or a
// near miss, never a cause-naming refusal. The expected column records
// the oracle's truth: gc materializes the 128 MiB array fine and reads
// back the 42.
//
// SINCE 2026-10-13 (F2, BUG-078 «PER DECLARATION»): the native frontend
// applies the same budget per declaration (tools/nativefrontend/
// budgets.go), so the refusal lands as this declaration's quarantine
// stub (stage frontend-export) and the rest of the package exports; the
// decoder's check stays as the whole-wire backstop.
var big [1024][1024][128]byte

func nestedOverBudget() int {
	big[0][0][0] = 42
	if big[0][0][0] != 42 {
		panic("bad")
	}
	return 1
}
