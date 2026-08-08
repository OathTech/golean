// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/array.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type Foo [10]uint64

func takesArray(x [13]string) string {
	return x[3]
}

func takesPtr(x *string) {
	*x += "bar"
}

func usesArrayElemRef() {
	x := [...]string{
		"a",
		"b",
	}
	x[1] = "c"
	takesPtr(&x[1])
}

func sum(x [100]uint64) uint64 {
	sum := uint64(0)
	for i := uint64(0); i < uint64(len(x)); i++ {
		sum += x[i]
	}
	sum += uint64(cap(x))
	return sum
}

func arrayToSlice() []string {
	x := [...]string{
		"a",
		"b",
	}
	return x[:]
}

const (
	arrayA = 0
	arrayB = 10
)

func arrayLiteralKeyed() string {
	var x = [...]string{
		arrayB: "B",
		"1",
		"2",
		arrayA: "A",
		"3",
	}
	return x[0]
}

// --- GoLean harness ---
// Authored wrapper.

func goleanArray() int {
	var big [13]string
	big[3] = "three"
	sum := len(takesArray(big))
	usesArrayElemRef()
	var h [100]uint64
	h[0] = 7
	h[99] = 5
	sum += int(sum100(h))
	sum += len(arrayToSlice()) * 10
	sum += len(arrayLiteralKeyed())
	var f Foo
	sum += len(f) * 100
	return sum
}

func sum100(x [100]uint64) int {
	return int(sum(x))
}

func main() {}
