package main

// BUG-063's lesser sibling, pinned AT ITS CURRENT CLASS (bug-fix arc
// audit fix round, 2026-08-19). `(*ap)[0:1]` with ap == nil: slicing an
// array requires an addressable operand and takes its address
// (spec#Slice_expressions), so the implicit &(*ap) is the same `&*`
// composition as BUG-063's receiver shapes — spec#Address_operators'
// eager panic clause applies and gc panics (artifacts/probe/a1-recv,
// scratch: recovered -> 100, expectation from `go run` at go1.26.5
// BEFORE the differential ran).
//
// The machine's emitAddressOf StarExpr collapse hands the slice node a
// nil base, and until 2026-10-27 execution went STUCK there — an honest
// fail-closed refusal, never a wrong answer, which is why this row was
// NOT on the BUG-063 Cases line: the receiver shapes lost the panic
// SILENTLY, this one lost it VISIBLY. Tracked as a coverage-disposition
// row in baselines/untriaged-ids until the S10 sweep entered it as
// BUG-227 (a `stuck` on a legal program is a misnamed refusal); FIXED
// the same day by lane core/fix-bug227-236-1027: applySlice's `.nil`
// base arm raises gc's recoverable nil dereference (the index arms'
// constructor, BUG-038), so this row is a strict PASS row now.
func nilArrayPtrSliceExpr() int {
	var ap *[4]int
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		s := (*ap)[0:1]
		r = len(s)
	}()
	return r
}

func main() {
	println(nilArrayPtrSliceExpr())
}
