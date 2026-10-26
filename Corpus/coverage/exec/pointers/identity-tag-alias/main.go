package main

// DC01 / BUG-133 (deep-clean review 2026-10-26, semantics S1): pointer
// identity is PHYSICAL — the same memory cell is the same pointer whatever
// static spelling reached it. A pointer conversion between struct types
// that differ only in field tags is legal (spec#Conversions: identical
// underlying types ignoring tags), and `&a.X` and `&b.X` then name ONE
// `int` variable. The machine's `Loc` keeps the static struct TypeId on
// the field step (`.field base A "X"` vs `.field base B "X"`), so pointer
// `==`, interface equality on `*int` boxes and map search over pointer
// keys must compare CANONICAL locations (`Loc.canon`), never the
// representation. Born RED (the S1 reproduction: `false 21 false` against
// gc's `true 12 true`), flips to PASS with the fix.

type tagA struct {
	X int `json:"a"`
}
type tagB struct {
	X int `json:"b"`
}

// S1: direct pointer equality across the alias.
func pointerAlias() bool {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return &a.X == &b.X
}

// S1: the two spellings are ONE map key (len 1, the second insert
// overwrote the first: 10*1 + 2).
func pointerMap() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	m := map[*int]int{&a.X: 1}
	m[&b.X] = 2
	return 10*len(m) + m[&a.X]
}

// S1: boxed as `any`, both dynamic types are `*int`, so the payloads are
// compared and they are equal.
func pointerIface() bool {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return any(&a.X) == any(&b.X)
}

// `!=` is the negation of the same identity.
func pointerNeq() bool {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return &a.X != &b.X
}

// Go's dynamic-type rule stays: `*tagA` and `*tagB` are different types,
// so the boxes are unequal even though both point at the same cell.
func ifaceTypeDiffers() bool {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return any(&a) == any(b)
}

// Converting back yields the original pointer.
func convertBack() bool {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return (*tagA)(b) == &a
}

// Access through the alias already worked (the review's control): the
// write is visible through the original spelling.
func writeThrough() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	b.X = 9
	return a.X
}

// delete through the alias spelling removes the entry inserted through
// the original one.
func mapDeleteViaAlias() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	m := map[*int]int{&a.X: 1}
	delete(m, &b.X)
	return len(m)
}

// Control: the same spelling twice (already true before the fix).
func sameSpelling() bool {
	a := tagA{X: 7}
	p, q := &a.X, &a.X
	return p == q
}

// Control: two distinct variables with equal contents stay unequal.
func distinctVars() bool {
	a := tagA{X: 7}
	c := tagA{X: 7}
	return &a.X == &c.X
}

func main() {
	println(pointerAlias(), pointerMap(), pointerIface(), pointerNeq(), ifaceTypeDiffers(),
		convertBack(), writeThrough(), mapDeleteViaAlias(), sameSpelling(), distinctVars())
}
