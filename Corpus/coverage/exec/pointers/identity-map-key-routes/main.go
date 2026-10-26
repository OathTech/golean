package main

// DC01 / BUG-133: every map-key route that reaches pointer identity —
// `map[any]` with pointer DYNAMIC values, a struct key holding a pointer
// field, a `*keyA` key reached by converting back from the alias, and
// boxes of DIFFERENT pointer types (two entries: the dynamic-type rule).
// Map search is `valueEq` over the entries, so every route is the one
// pointer arm. Born RED at the base (the first three), the fourth a
// must-stay-two control.

type keyA struct{ X int }
type keyB struct{ X int }
type holdsPtr struct{ p *int }

func anyKeys() int {
	a := keyA{X: 1}
	b := (*keyB)(&a)
	m := map[any]int{any(&a.X): 1}
	m[any(&b.X)] = 2
	return 10*len(m) + m[any(&a.X)]
}

func structKeys() int {
	a := keyA{X: 1}
	b := (*keyB)(&a)
	m := map[holdsPtr]int{{p: &a.X}: 1}
	m[holdsPtr{p: &b.X}] = 2
	return 10*len(m) + m[holdsPtr{p: &a.X}]
}

func convertedBackKeys() int {
	a := keyA{X: 1}
	b := (*keyB)(&a)
	m := map[*keyA]int{&a: 1}
	m[(*keyA)(b)] = 2
	return 10*len(m) + m[&a]
}

func differentPointerTypes() int {
	a := keyA{X: 1}
	b := (*keyB)(&a)
	m := map[any]int{any(&a): 1}
	m[any(b)] = 2
	return 10*len(m) + m[any(&a)]
}

func main() { println(anyKeys(), structKeys(), convertedBackKeys(), differentPointerTypes()) }
