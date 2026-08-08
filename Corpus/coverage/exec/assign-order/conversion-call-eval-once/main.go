package main

// BUG-047 pin: a conversion of a call as the WHOLE RHS of a define or
// assign must evaluate the call EXACTLY ONCE. The native frontend
// currently hoists the inner call in the conversion path and then
// re-emits the RHS on the generic path, so the callee runs twice
// (emit.go:2112 + the generic loop; see docs/BUGS.md BUG-047).

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
