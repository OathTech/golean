package main

// DC01 / BUG-133: the alias through a NESTED field path — the static
// TypeId sits on an inner `.field` step (`&a.In.X` vs `&b.In.X`), and on
// the outer one for the inner struct's own address (`&a.In` vs `&b.In`,
// both `*inner`). Born RED at the base.

type inner struct{ X int }
type outerA struct{ In inner }
type outerB struct{ In inner }

func nestedLeaf() bool {
	a := outerA{In: inner{X: 3}}
	b := (*outerB)(&a)
	return &a.In.X == &b.In.X
}

func nestedStruct() bool {
	a := outerA{In: inner{X: 3}}
	b := (*outerB)(&a)
	return &a.In == &b.In
}

func nestedMap() int {
	a := outerA{In: inner{X: 3}}
	b := (*outerB)(&a)
	m := map[*inner]int{&a.In: 1}
	m[&b.In] = 2
	n := map[*int]int{&a.In.X: 1}
	n[&b.In.X] = 2
	return 100*len(m) + 10*len(n) + m[&a.In]
}

func main() { println(nestedLeaf(), nestedStruct(), nestedMap()) }
