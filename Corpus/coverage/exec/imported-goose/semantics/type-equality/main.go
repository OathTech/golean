// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/type_equality.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func TypesEqual[T, U any]() bool {
	var t *T
	var u *U
	return any(t) == any(u)
}

func testPrimitiveTypesEqual() bool {
	return TypesEqual[int, int]() &&
		!TypesEqual[int, string]() &&
		!TypesEqual[int, uint32]() &&
		!TypesEqual[int, int64]() &&
		!TypesEqual[int, uint64]() &&
		TypesEqual[func() bool, func() bool]()
}

type DefinedStr string

type DefinedStr2 = DefinedStr

func testDefinedStrTypesEqual() bool {
	return !TypesEqual[DefinedStr, string]() &&
		TypesEqual[DefinedStr, DefinedStr2]()
}

type List[T any] struct {
	X    T
	Next *List[T]
}

func testListTypesEqual() bool {
	return TypesEqual[List[int], List[int]]() &&
		!TypesEqual[List[int], List[string]]()
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestPrimitiveTypesEqual() int {
	if testPrimitiveTypesEqual() {
		return 1
	}
	return 0
}

func goleanTestDefinedStrTypesEqual() int {
	if testDefinedStrTypesEqual() {
		return 1
	}
	return 0
}

func goleanTestListTypesEqual() int {
	if testListTypesEqual() {
		return 1
	}
	return 0
}

func main() {}
