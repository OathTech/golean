// E2 probe (index-panic direction): does gc read the target operand i
// BEFORE or AFTER the call? Call-first => i is read post-call as 5 =>
// index out of range. Operand-first => i is read as 0 => no panic.
package main

var xs = []int{10, 11, 12}
var i = 0

func f() (int, int) { i = 5; return 42, 7 }

func main() {
	defer func() {
		if r := recover(); r != nil {
			println("panic:", r.(error).Error())
		}
	}()
	var j int
	xs[i], j = f()
	println("no-panic", xs[0], j)
}
