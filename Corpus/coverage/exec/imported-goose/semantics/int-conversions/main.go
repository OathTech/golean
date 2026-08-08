// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/int_conversions.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testU64ToU32() bool {
	var ok = true
	x := uint64(1230)
	y := uint32(1230)
	ok = ok && uint32(x) == y
	ok = ok && uint64(y) == x
	return ok
}

func testU32ToU64() bool {
	var ok = true
	x := uint32(1230)
	y := uint64(1230)
	ok = ok && uint64(x) == y
	ok = ok && uint32(y) == x
	return ok
}

func testU32Len() bool {
	s := make([]byte, 100)
	return uint32(len(s)) == uint32(100)
}

type Uint32 uint32

func testU32NewtypeLen() bool {
	s := make([]byte, 20)
	return Uint32(len(s)) == Uint32(20)
}

func testUint32Untyped() bool {
	x := Uint32(1230)
	return x == 1230
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestU64ToU32() int {
	if testU64ToU32() {
		return 1
	}
	return 0
}

func goleanTestU32ToU64() int {
	if testU32ToU64() {
		return 1
	}
	return 0
}

func goleanTestU32Len() int {
	if testU32Len() {
		return 1
	}
	return 0
}

func goleanTestU32NewtypeLen() int {
	if testU32NewtypeLen() {
		return 1
	}
	return 0
}

func goleanTestUint32Untyped() int {
	if testUint32Untyped() {
		return 1
	}
	return 0
}

func main() {}
