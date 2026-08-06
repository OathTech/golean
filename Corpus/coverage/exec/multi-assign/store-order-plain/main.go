package main

// BUG-025 pin (delta-review D3, general half — pre-existing, not
// channel-specific): spec §Assignments phase 2 carries assignments out
// in LEFT-TO-RIGHT order, so the first target's store is observable
// even when a later target's store panics (the spec's own
// `x[1], x[3] = 4, 5 // set x[1] = 4, then panic setting x[3] = 5`).
// The machine's multi-assign apply stores all-or-nothing.

func plainTwo(vp *int, okp *int) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	*vp, *okp = 7, 9
	return 0
}

func plainSecondTargetPanicStoresFirst() int {
	v := 0
	var okp *int
	hit := plainTwo(&v, okp)
	return hit*100 + v
}

func main() {
	plainSecondTargetPanicStoresFirst()
}
