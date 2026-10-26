package main

// A true alias `type BB = B`: the conversion target spelled through the alias
// is B itself; the box's dynamic type is B.
type A struct{ X, Y int }
type B struct{ X, Y int }
type BB = B

func probe() int {
	a := A{1, 2}
	pb := (*BB)(&a)
	r := 0
	if *pb == (B{1, 2}) {
		r += 10
	}
	switch any(*pb).(type) {
	case A:
		r += 1
	case B:
		r += 2
	}
	return r
}

func main() { println(probe()) }
