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
// nil base and execution goes STUCK — an honest fail-closed refusal,
// never a wrong answer, which is why this row is NOT on the BUG-063
// Cases line: the receiver shapes lose the panic SILENTLY, this one
// loses it VISIBLY. Tracked as a coverage-disposition row in
// baselines/untriaged-ids; it flips green only when the slice-base
// path grows its own nil handling (fix only if it falls out of the
// BUG-063 movement naturally — it did not, by scope: the fix is
// receiver-position only, and this base position is a store-adjacent
// consumer where the five store-order pins live).
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
