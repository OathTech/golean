// noodler frontier probe — label on a simple statement (not a block/loop) as a forward goto target
package main

// A label on a plain statement, reached by a forward goto.
func labeledSimpleStatement(n int) int {
	x := 0
	if n > 0 {
		goto add
	}
	x = 100
add:
	x++
	return x
}

func main() {}
