package main

// DC01 / BUG-133: the same identity defect with NO tags at all — two
// distinct named struct types with identical underlying types (the
// reviewer's second reproduction). Born RED at the base.

type namedA struct{ X int }
type namedB struct{ X int }

func namedAlias() bool {
	a := namedA{X: 1}
	b := (*namedB)(&a)
	return &a.X == &b.X
}

func namedMap() int {
	a := namedA{X: 1}
	b := (*namedB)(&a)
	m := map[*int]int{&a.X: 1}
	m[&b.X] = 2
	return 10*len(m) + m[&a.X]
}

func namedIface() bool {
	a := namedA{X: 1}
	b := (*namedB)(&a)
	return any(&a.X) == any(&b.X)
}

func main() { println(namedAlias(), namedMap(), namedIface()) }
