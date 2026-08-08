// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/allocator.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// patterns that show up in in-memory allocators

type unit struct{}

func findKey(m map[uint64]unit) (uint64, bool) {
	var found uint64 = 0
	var ok bool = false
	for k := range m {
		if !ok {
			found = k
			ok = true
		}
		// TODO: goose doesn't support break in map iteration
	}
	return found, ok
}

func allocate(m map[uint64]unit) (uint64, bool) {
	k, ok := findKey(m)
	delete(m, k)
	return k, ok
}

func freeRange(sz uint64) map[uint64]unit {
	m := make(map[uint64]unit)
	for i := uint64(0); i < sz; i++ {
		m[i] = unit{}
	}
	return m
}

func testAllocateDistinct() bool {
	free := freeRange(4)
	a1, _ := allocate(free)
	a2, _ := allocate(free)
	return a1 != a2
}

func testAllocateFull() bool {
	free := freeRange(2)
	_, ok1 := allocate(free)
	_, ok2 := allocate(free)
	_, ok3 := allocate(free)
	return ok1 && ok2 && !ok3
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestAllocateDistinct() int {
	if testAllocateDistinct() {
		return 1
	}
	return 0
}

func goleanTestAllocateFull() int {
	if testAllocateFull() {
		return 1
	}
	return 0
}

func main() {}
