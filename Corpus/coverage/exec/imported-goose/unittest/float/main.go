// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/float.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


const (
	a = 1.0
	b = 1e6
)

func useFloat() float64 {
	x := a
	x = (x + a) * 1.0
	return x
}

func compareIntFloat(x int) bool {
	return x < b
}

func compareFloatInt(x int) bool {
	return b < x
}

// --- GoLean harness ---
// Authored wrapper.

func goleanFloat() int {
	sum := 0
	if useFloat() == 2.0 {
		sum++
	}
	if compareIntFloat(3) {
		sum += 2
	}
	if compareFloatInt(3) {
		sum += 4
	}
	return sum
}

func main() {}
