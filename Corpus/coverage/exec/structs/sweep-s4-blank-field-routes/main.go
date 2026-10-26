package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-129's shape — a blank
// field is never stored and never compared (spec#Comparison_operators:
// non-blank fields only) — at the routes beside structs/blank-field-equality
// and blank-field-map-key: a blank field inside an EMBEDDED struct compared
// through the outer (`==`, map key, `any` box), a blank field of ARRAY type
// (`_ [2]int`, `_ [0]int`), blank fields of POINTER and CHANNEL type holding
// two different references, arrays of blank-field structs as values and as a
// map key, and a blank-field struct RETURNED to the observer (the readout
// renders the zero value on the machine; gc's observer renders what the
// harness reads). Operands are plain variable reads where a literal or `&x`
// would be refused by name (BUG-130's ruling). gc agrees on every row
// (probed both sides first; .tmp/probes/bf-*).

type inner struct {
	_ int
	X int
}
type outer struct {
	inner
	Y int
}
type arrBlank struct {
	_ [2]int
	X int
	_ [0]int
}
type refBlank struct {
	_ *int
	X int
	_ chan int
}
type oneBlank struct {
	_ int
	X int
}

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

// Embedded blank fields through the outer: equal, promoted field equal,
// one map entry, equal boxes (gc 1 + 10 + 100 + 0 + 10000 + 200000 + 1000000).
func bfEmbedded() int {
	a := outer{inner{1, 7}, 3}
	b := outer{inner{2, 7}, 3}
	m := map[outer]int{a: 1}
	m[b] = 2
	var i, j any = a, b
	return bit(a == b, 1) + bit(a.inner == b.inner, 10) + bit(a.X == b.X, 100) + bit(a != b, 1000) +
		len(m)*10000 + m[outer{inner{9, 7}, 3}]*100000 + bit(i == j, 1000000)
}

// Blank fields of array type (gc 1 + 0 + 100).
func bfArrayTyped() int {
	z1 := [2]int{1, 2}
	z2 := [2]int{3, 4}
	var z0 [0]int
	a := arrBlank{z1, 7, z0}
	b := arrBlank{z2, 7, z0}
	m := map[arrBlank]int{a: 1}
	m[b] = 2
	return bit(a == b, 1) + bit(a != b, 10) + len(m)*100
}

// Blank pointer and channel fields holding different references: equal,
// one map entry, the lookup by a nil-referenced key finds it (gc 1 + 10 + 100 + 2000).
func bfReferenceTyped() int {
	x, y := 1, 2
	px, py := &x, &y
	ch := make(chan int)
	a := refBlank{px, 7, ch}
	b := refBlank{py, 7, nil}
	m := map[refBlank]int{a: 1}
	m[b] = 2
	return bit(a == b, 1) + bit(any(a) == any(b), 10) + len(m)*100 + m[refBlank{nil, 7, nil}]*1000
}

// Arrays of blank-field structs: elementwise equal, one array-key entry (gc 1 + 100 + 2000 + 10000).
func bfArrays() int {
	a := [1]oneBlank{{1, 7}}
	b := [1]oneBlank{{2, 7}}
	m := map[[1]oneBlank]int{a: 1}
	m[b] = 2
	s := [2]oneBlank{{1, 1}, {2, 2}}
	t := [2]oneBlank{{9, 1}, {8, 2}}
	return bit(a == b, 1) + len(m)*100 + m[[1]oneBlank{{3, 7}}]*1000 + bit(s == t, 10000)
}

// A blank-field struct returned to the observer.
func bfReadout() oneBlank {
	return oneBlank{5, 7}
}

func main() {
	println(bfEmbedded(), bfArrayTyped(), bfReferenceTyped(), bfArrays(), bfReadout().X)
}
