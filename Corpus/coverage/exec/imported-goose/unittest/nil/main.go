// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/nil.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func AssignNilSlice() {
	s := make([][]byte, 4)
	s[2] = nil
}

func AssignNilPointer() {
	s := make([]*uint64, 4)
	s[2] = nil
}

func CompareSliceToNil() bool {
	s := make([]byte, 0)
	return s != nil
}

func ComparePointerToNil() bool {
	s := new(uint64)
	return s != nil
}

type containsPointer struct {
	s *uint64
}

func useNilField() *containsPointer {
	return &containsPointer{s: nil}
}

// --- GoLean harness ---
// Authored wrapper.

func goleanNil() int {
	AssignNilSlice()
	AssignNilPointer()
	sum := 0
	if CompareSliceToNil() {
		sum++
	}
	if ComparePointerToNil() {
		sum += 2
	}
	if useNilField().s == nil {
		sum += 4
	}
	return sum
}

func main() {}
