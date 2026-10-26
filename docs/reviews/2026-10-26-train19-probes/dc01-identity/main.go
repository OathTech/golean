package main

// Train-19 shake probes for BUG-133's local space: every route by which two
// spellings can name one cell, or two cells could canonicalize alike.

type tagA struct {
	X   int `json:"a"`
	Arr [3]int
	In  inner
}
type tagB struct {
	X   int `json:"b"`
	Arr [3]int
	In  inner
}
type inner struct{ Y int }

type host struct{ *tagA }

type elemA struct{ V int }
type elemB struct{ V int }

// switch on a pointer value reaches == too
func switchOnPointer() int {
	a := tagA{X: 1}
	b := (*tagB)(&a)
	p := &b.X
	switch p {
	case &a.X:
		return 1
	}
	return 0
}

// array of pointers as a map key: the element comparison reaches the pointer arm
func arrayKeyOfPointers() int {
	a := tagA{X: 1}
	b := (*tagB)(&a)
	m := map[[1]*int]int{}
	m[[1]*int{&a.X}] = 1
	m[[1]*int{&b.X}] = 2
	return 10*len(m) + m[[1]*int{&a.X}]
}

// pointer to the field of a struct that is itself an array ELEMENT, via the alias
func elemFieldThroughAlias() bool {
	arr := [2]elemA{{1}, {2}}
	p := (*elemB)(&arr[1])
	return &arr[1].V == &p.V
}

// slice views over DIFFERENT backing arrays never alias
func distinctBackings() bool {
	s := make([]int, 3)
	t := make([]int, 3)
	return &s[0] == &t[0]
}

// append without growth keeps the backing: &t[0] == &s[0]
func appendNoGrowth() bool {
	s := make([]int, 1, 4)
	t := append(s, 9)
	return &t[0] == &s[0]
}

// embedded POINTER: the promoted field through the host is the pointee's field
func embeddedPointerPromotion() bool {
	a := tagA{X: 1}
	h := host{&a}
	return &h.X == &a.X && &h.tagA.X == &a.X
}

// a struct copy is a fresh cell
func copyIsFresh() bool {
	a := tagA{X: 1}
	c := a
	return &c.X == &a.X
}

// pointers into the inner struct via the alias, compared at *inner and at *int
func innerThroughAlias() int {
	a := tagA{X: 1}
	b := (*tagB)(&a)
	r := 0
	if &a.In == &b.In {
		r += 1
	}
	if &a.In.Y == &b.In.Y {
		r += 10
	}
	if any(&a.In.Y) == any(&b.In.Y) {
		r += 100
	}
	return r
}

// different fields with the SAME NAME at different depths are different cells
func sameNameDifferentDepth() bool {
	type L struct{ Y int }
	type T struct {
		Y int
		L L
	}
	t := T{}
	return &t.Y == &t.L.Y
}

// pointer-typed struct key through the alias (field of key struct)
func structKeyThroughAlias() int {
	type K struct {
		P *int
		N int
	}
	a := tagA{X: 1}
	b := (*tagB)(&a)
	m := map[K]int{}
	m[K{&a.X, 0}] = 1
	m[K{&b.X, 0}] = 2
	return 10*len(m) + m[K{&a.X, 0}]
}

// interface box of a pointer-to-array-element through the alias
func ifaceElemThroughAlias() bool {
	a := tagA{}
	b := (*tagB)(&a)
	return any(&a.Arr[2]) == any(&b.Arr[2])
}

// comparing *tagA with *tagB after converting the alias back, inside a map[any]
func anyKeyConvertedBack() int {
	a := tagA{}
	b := (*tagB)(&a)
	m := map[any]int{}
	m[&a] = 1
	m[(*tagA)(b)] = 2
	m[b] = 3
	return 10*len(m) + m[&a]
}

func main() {
	println(switchOnPointer(), arrayKeyOfPointers(), elemFieldThroughAlias(), distinctBackings(),
		appendNoGrowth(), embeddedPointerPromotion(), copyIsFresh(), innerThroughAlias(),
		sameNameDifferentDepth(), structKeyThroughAlias(), ifaceElemThroughAlias(), anyKeyConvertedBack())
}
