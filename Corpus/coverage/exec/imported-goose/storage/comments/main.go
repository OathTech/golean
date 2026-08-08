// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/comments/0consts.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// source: testdata/examples/comments/1doc.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


const ONE uint64 = 1
const TWO uint64 = 2

// comments tests package comments, like this one
//
// it has multiple files

type Foo struct {
	a bool
}

// --- GoLean harness ---
// Authored wrapper: the consts and the commented struct type.

func goleanComments() int {
	x := Foo{a: true}
	if x.a {
		return int(ONE + TWO*10)
	}
	return 0
}

func main() {}
