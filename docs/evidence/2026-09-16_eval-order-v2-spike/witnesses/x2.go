package main

// Fragment extra: a guarded region (||) whose event is unordered against
// an outer read; an unexecuted region contributes nothing.
func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

func main() {
	x := 1
	z := false
	h := func() bool { x = 2; return true }
	v := b2i(z || h()) + x
	x, z = 1, true
	w := b2i(z || h()) + x
	println("x2", v, w)
}
