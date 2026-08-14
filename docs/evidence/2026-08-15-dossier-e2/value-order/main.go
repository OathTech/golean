// E2 probe (value direction, no panic): callee mutates the target
// operand within range. Call-first => store lands at xs[2];
// operand-first => store lands at xs[0].
package main

var xs = []int{10, 11, 12}
var i = 0

func f() (int, int) { i = 2; return 42, 7 }

func main() {
	var j int
	xs[i], j = f()
	println(xs[0], xs[1], xs[2], j)
}
