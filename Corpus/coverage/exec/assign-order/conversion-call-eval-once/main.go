package main

// BUG-047 pin (FIXED 2026-08-08): a conversion of a call as the WHOLE
// RHS of a define or assign must evaluate the call EXACTLY ONCE. The
// native frontend used to hoist the inner call in the conversion path
// and then re-emit the RHS on the generic path, running the callee
// twice; the assign-site guard now routes conversions through the
// generic single-emit path. Both rows pin the fixed once-only
// evaluation green. See docs/BUGS.md BUG-047.

var counter int

func bump() int {
	counter = counter + 1
	return counter
}

func convCallDefineOnce() int {
	x := int(bump())
	return x*100 + counter
}

func convCallAssignOnce() int {
	var y int
	y = int(bump())
	return y*100 + counter
}

func main() {
	convCallDefineOnce()
}
