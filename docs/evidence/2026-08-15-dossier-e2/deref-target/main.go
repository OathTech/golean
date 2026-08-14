// E2 probe (deref target): callee repoints the target's pointer.
// Call-first => the store goes through the NEW pointee (b);
// operand-first => through the old pointee (a).
package main

var a, b int
var p = &a

func f() (int, int) { p = &b; return 42, 7 }

func main() {
	var j int
	*p, j = f()
	println("a", a, "b", b, "j", j)
}
