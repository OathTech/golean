package main

func main() { run() }

var trace []int

func v(i int) int { trace = append(trace, i); return i }

func run() {
	x := 3
	switch x {
	case v(1), v(2):
		println("12")
	case v(3), v(4):
		println("34")
	case v(5):
		println("5")
	}
	println(len(trace), trace[0], trace[1], trace[2])
	trace = nil
	switch {
	case v(1) == 2:
		println("a")
	case v(2) == 2:
		println("b")
	case v(3) == 3:
		println("c")
	}
	println(len(trace))
	// duplicate non-constant cases are legal; first wins
	a, b := 7, 7
	switch 7 {
	case a:
		println("a first")
	case b:
		println("b second")
	}
	// fallthrough chains
	switch x {
	case 3:
		println("three")
		fallthrough
	case 4:
		println("four via fallthrough")
	case 5:
		println("five")
	}
	// interface tag with mixed-type cases
	var t any = "s"
	switch t {
	case 1:
		println("int")
	case "s":
		println("string")
	case nil:
		println("nil")
	}
	var tn any
	switch tn {
	case 0:
		println("zero")
	case nil:
		println("nil tag")
	}
	// switch on a pointer tag with nil case
	var p *int
	switch p {
	case nil:
		println("nil ptr")
	}
	// init statement scoping and no-tag with bool var
	switch y := x * 2; {
	case y > 5:
		println("y>5")
	}
	// switch with untyped constant tag
	switch 5 {
	case x + 2:
		println("x+2")
	}
}
