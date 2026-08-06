package main

// BUG-025 companion pin (convergence round): in a PLAIN multi-assign,
// a nil FIELD target's indirection is the assignment's own — spec
// §Assignments defers it to phase 2, so it fires AT THE STORE, after
// the first target's store landed (gc realizes exactly this). An
// eager address evaluation that checks it in phase 1 loses the first
// store.

type T struct{ b bool }

func plainFieldNilStoreTime() int {
	xs := []int{0}
	var p *T
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		xs[0], p.b = 3, true
	}()
	return hit*1000 + xs[0]*50
}

func main() {
	plainFieldNilStoreTime()
}
