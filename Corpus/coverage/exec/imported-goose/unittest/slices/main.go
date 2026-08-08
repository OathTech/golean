// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/slices.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type SliceAlias []bool

func sliceOps() uint64 {
	x := make([]uint64, 10)
	v1 := x[2]
	v2 := x[2:3]
	v3 := x[:3]
	v4 := &x[2]
	return v1 + v2[0] + v3[1] + *v4 + uint64(len(x)) + uint64(cap(x))
}

func makeSingletonSlice(x uint64) []uint64 {
	return []uint64{x}
}

type thing struct {
	x uint64
}

type sliceOfThings struct {
	things []thing
}

func (ts sliceOfThings) getThingRef(i uint64) *thing {
	return &ts.things[i]
}

func makeAlias() SliceAlias {
	return make(SliceAlias, 10)
}

// --- GoLean harness ---
// Authored wrapper.

func goleanSlices() int {
	total := int(sliceOps())
	total += int(makeSingletonSlice(5)[0]) * 10
	ts := sliceOfThings{things: []thing{{x: 3}, {x: 4}}}
	ts.getThingRef(1).x = 9
	total += int(ts.things[1].x) * 100
	total += len(makeAlias()) * 1000
	return total
}

func main() {}
