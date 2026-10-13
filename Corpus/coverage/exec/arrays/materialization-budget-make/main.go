package main

// RED BY DESIGN (BUG-078 residual (2b), the decoder's half, fail-closed
// at the 2026-10-12 fix round — review MEDIUM-1 under [USER] Mike's
// «30: can we fail-close until we fix?», relayed): a `make` whose
// CONSTANT length (or cap) times the element type's footprint exceeds
// the interpreter's materialization footprint budget (1<<24 scalar
// elements, GoLean/NativeToIR.lean arrayFootprintBudget /
// checkMakeFootprint) refuses BY NAME at the wire boundary. The element
// COUNT here, 1<<19, is 16× under sliceCapBudget (BUG-090) and the
// element type [1024]byte is inside both array budgets; the backing is
// 2^29 leaves, which the reviewer reproduced as a KILL under `capped -m
// 16G` (exit 137 at 16.7 GB after 57 s; 1<<18 ran 37.0 s / 13.6 GB).
// The expected column records the oracle's truth: gc allocates the
// 512 MiB backing fine and reads back the 7. A make with a RUN-TIME
// count is the owed core half (release-readiness item 30).
//
// SINCE 2026-10-13 (F2, BUG-078 «PER DECLARATION»): the native frontend
// applies the same budget per declaration (tools/nativefrontend/
// budgets.go), so the refusal lands as this declaration's quarantine
// stub (stage frontend-export) and the rest of the package exports; the
// decoder's check stays as the whole-wire backstop.
func makeOverBudget() int {
	b := make([][1024]byte, 1<<19)
	b[0][0] = 7
	if b[0][0] != 7 {
		panic("bad")
	}
	return len(b)
}
