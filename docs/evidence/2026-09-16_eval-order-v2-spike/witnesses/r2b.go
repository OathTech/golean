package main

// R2 witness (completion anchoring): the || operation — its RHS read of b
// included — completes before the later call change(). Relation set {false}
// exactly; anchoring the later call at the guard's decision would admit true.
func main() {
	b, left := false, false
	change := func() int { b = true; return 0 }
	logical := func(v bool, n int) { println("logical", v, n) }
	logical(left || b, change())
}
