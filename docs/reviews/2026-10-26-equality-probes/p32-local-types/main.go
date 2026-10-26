package main

func main() { run() }

func boxA() any {
	type T struct{ X int }
	return T{1}
}

func boxB() any {
	type T struct{ X int }
	return T{1}
}

func twoBlocks() (any, any) {
	var a, b any
	{
		type T struct{ X int }
		a = T{1}
	}
	{
		type T struct{ X int }
		b = T{1}
	}
	return a, b
}

func loopType() (any, any) {
	var vs [2]any
	for i := 0; i < 2; i++ {
		type T struct{ X int }
		vs[i] = T{1}
	}
	return vs[0], vs[1]
}

type Shadowed struct{ X int }

func shadow() any {
	type Shadowed struct{ X int }
	return Shadowed{1}
}

func run() {
	println(boxA() == boxA(), boxA() == boxB())
	a, b := twoBlocks()
	println(a == b, a == a)
	l0, l1 := loopType()
	println(l0 == l1)
	println(shadow() == any(Shadowed{1}), shadow() == shadow())
	m := map[any]int{}
	m[boxA()] = 1
	m[boxB()] = 2
	m[a] = 3
	m[b] = 4
	m[shadow()] = 5
	m[Shadowed{1}] = 6
	println(len(m))
	switch boxB().(type) {
	case Shadowed:
		println("Shadowed")
	default:
		println("default")
	}
	if _, ok := a.(Shadowed); ok {
		println("block T asserted as Shadowed")
	} else {
		println("block T is not Shadowed")
	}
}
