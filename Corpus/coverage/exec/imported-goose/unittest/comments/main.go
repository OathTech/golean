// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/comments.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main

// unittest is a package full of many independent and small translation examples

// This struct is very important.
//
// This is despite it being empty.
type importantStruct struct{}

// doSubtleThings does a number of subtle things:
//
// (actually, it does nothing)
func doSubtleThings() {}

// This comment starts a Coq comment (*
func hasStartComment() {}

// This comment *) ends a Coq comment
func hasEndComment() {}

// --- GoLean harness ---
// Authored wrapper.

func goleanComments() int {
	doSubtleThings()
	hasStartComment()
	hasEndComment()
	_ = importantStruct{}
	return 1
}

func main() {}
