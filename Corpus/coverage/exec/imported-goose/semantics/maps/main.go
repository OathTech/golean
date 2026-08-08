// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/maps.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func IterateMapKeys(m map[uint64]uint64) uint64 {
	var sum uint64
	for k := range m {
		sum = sum + k
	}
	return sum
}

func IterateMapValues(m map[uint64]uint64) uint64 {
	var sum uint64
	for _, v := range m {
		sum = sum + v
	}
	return sum
}

func testIterateMap() bool {
	var ok = true

	// make a map with some things in it
	m := make(map[uint64]uint64)
	m[0] = 1
	m[1] = 2
	m[3] = 4

	// iterate keys
	ok = ok && (IterateMapKeys(m) == 4)

	// iterate values
	ok = ok && (IterateMapValues(m) == 7)

	return ok
}

func testMapSize() bool {
	var ok = true

	m := make(map[uint64]uint64)
	ok = ok && (uint64(len(m)) == 0)

	m[0] = 1
	m[1] = 2
	m[3] = 4
	ok = ok && (uint64(len(m)) == 3)

	return ok
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestIterateMap() int {
	if testIterateMap() {
		return 1
	}
	return 0
}

func goleanTestMapSize() int {
	if testMapSize() {
		return 1
	}
	return 0
}

func main() {}
