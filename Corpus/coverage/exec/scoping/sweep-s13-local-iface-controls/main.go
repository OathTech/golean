package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the function-local
// interface forms that DO lower — a local named interface declared and held
// in a nil-compared variable (no dispatch), and a local empty interface
// asserted back. The dispatched form is scoping/sweep-s13-local-iface-dispatch
// (BUG-301). Expected = gc go1.26.5.

func localIfaceDeclOnly() int {
	type getter interface{ Get() int }
	var g getter
	if g == nil {
		return 1
	}
	return 2
}

func localIfaceEmpty() int {
	type e interface{}
	var x e = 4
	return x.(int) // 4
}

func main() { println(localIfaceDeclOnly(), localIfaceEmpty()) }
