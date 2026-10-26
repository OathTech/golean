package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-133's shape at every
// POINTEE KIND — the identity-* rows hold int, chan, nested struct and array
// fields; these hold a string, bool, float64, defined int, pointer, slice,
// map, func, interface and zero-size field reached under two spellings of
// one struct cell, by `==` and by the `any` box (same dynamic type, so the
// payloads compare), plus a map keyed by `*string` and a `map[any]` keyed by
// `*func() int` under both spellings. gc agrees on every row (probed both
// sides first; .tmp/probes/fk-kinds, fk-kinds-keys).

type kindA struct {
	S string  `json:"a"`
	B bool    `json:"a"`
	F float64 `json:"a"`
	D kInt    `json:"a"`
	P *int    `json:"a"`
	L []int   `json:"a"`
	M map[int]int
	G func() int
	I any
	Z kZero
}
type kindB struct {
	S string  `json:"b"`
	B bool    `json:"b"`
	F float64 `json:"b"`
	D kInt    `json:"b"`
	P *int    `json:"b"`
	L []int   `json:"b"`
	M map[int]int
	G func() int
	I any
	Z kZero
}
type kInt int
type kZero struct{}

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

func mkKind() (kindA, *kindB) {
	x := 1
	a := kindA{S: "s", B: true, F: 1.5, D: 2, P: &x, L: []int{1}, M: map[int]int{}, G: func() int { return 3 }, I: 4}
	return a, nil
}

func kindString() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	s := bit(&a.S == &b.S, 1) + bit(any(&a.S) == any(&b.S), 10)
	b.S = "t"
	return s + bit(a.S == "t", 100)
}

func kindBool() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	s := bit(&a.B == &b.B, 1) + bit(any(&a.B) == any(&b.B), 10)
	b.B = false
	return s + bit(!a.B, 100)
}

func kindFloat() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	s := bit(&a.F == &b.F, 1) + bit(any(&a.F) == any(&b.F), 10)
	b.F = 2.5
	return s + bit(a.F == 2.5, 100)
}

func kindDefinedInt() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	s := bit(&a.D == &b.D, 1) + bit(any(&a.D) == any(&b.D), 10)
	b.D = 9
	return s + bit(a.D == 9, 100)
}

// A pointer field: the field's address under both spellings, the boxed
// addresses, the pointer VALUES read through both and the pointees.
func kindPointer() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	return bit(&a.P == &b.P, 1) + bit(any(&a.P) == any(&b.P), 10) +
		bit(a.P == b.P, 100) + bit(*a.P == *b.P, 1000)
}

// A slice field: the header's address under both spellings, and the
// element address through both headers.
func kindSlice() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	return bit(&a.L == &b.L, 1) + bit(any(&a.L) == any(&b.L), 10) + bit(&a.L[0] == &b.L[0], 100)
}

func kindMap() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	b.M[1] = 5
	return bit(&a.M == &b.M, 1) + bit(any(&a.M) == any(&b.M), 10) + bit(a.M[1] == 5, 100)
}

// A func field: pointers to it are comparable (the pointee is not).
func kindFunc() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	return bit(&a.G == &b.G, 1) + bit(any(&a.G) == any(&b.G), 10) + bit(b.G() == a.G(), 100)
}

func kindIface() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	s := bit(&a.I == &b.I, 1) + bit(any(&a.I) == any(&b.I), 10) + bit(a.I == b.I, 100)
	b.I = 5
	return s + bit(a.I == any(5), 1000)
}

// A zero-size field reached under two spellings is ONE field (the same
// name on the same cell), unlike two zero-size fields (BUG-176).
func kindZeroSize() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	return bit(&a.Z == &b.Z, 1) + bit(any(&a.Z) == any(&b.Z), 10)
}

// `map[*string]` keyed under both spellings holds one entry (gc 1 2 2 → 122).
func kindStringKey() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	m := map[*string]int{&a.S: 1}
	m[&b.S] = 2
	return len(m)*100 + m[&a.S]*10 + m[&b.S]
}

// `map[any]` keyed by `*func() int` under both spellings: one entry,
// deleted through the alias (gc 1 2 0 → 120).
func kindFuncAnyKey() int {
	a, _ := mkKind()
	b := (*kindB)(&a)
	n := map[any]int{&a.G: 1}
	n[&b.G] = 2
	s := len(n)*100 + n[&a.G]*10
	delete(n, &b.G)
	return s + len(n)
}

func main() {
	println(kindString(), kindBool(), kindFloat(), kindDefinedInt(), kindPointer(), kindSlice(),
		kindMap(), kindFunc(), kindIface(), kindZeroSize(), kindStringKey(), kindFuncAnyKey())
}
