package main

// The write side WITHOUT a conversion in the source: this program is lowered,
// then the wire is edited by hand so the literal on the right of `var b B`
// carries type A (a simulated frontend tagging fault). gc never sees the
// edited wire; the question is what the machine does with it.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	var b B = B{1, 2}
	var i any = b
	r := 0
	switch i.(type) {
	case A:
		r = 1
	case B:
		r = 2
	}
	if b == (B{1, 2}) {
		r += 10
	}
	return r
}

func main() { println(probe()) }
