package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// MAP KEYS of interface type take the untyped constant's DEFAULT type: `m[1]`
// and `m[1.0]` are different keys (int 1, float64 1) — at the literal, the
// store, the read, the comma-ok read, the compound assignment, `++`, `delete`,
// the blank comma-ok and a struct key with an interface field; a nil key; a
// `map[string]any` value store of every constant kind and nil; a comma-ok map
// read into an interface target; the two-call store `m[g()] = h()`.

type tDef int

type kAny struct{ A any }

func g() int { return 1 }

func h() string { return "h" }

func storeRead() (int, int, int, int, int) {
	m := map[any]int{}
	m[1] = 1
	m["a"] = 2
	m[2.5] = 3
	return m[1], m["a"], m[2.5], m[1.0], len(m)
}

func litKeysDefaultType() (int, int, int, int, int) {
	m := map[any]int{1: 10, 2.5: 20, 'c': 30}
	return m[1], m[1.0], m[2.5], m[99], m[len(m)]
}

func compound() (int, int) {
	m := map[any]int{}
	m[1] += 5
	m[1] += 5
	m[1.0] += 1
	return m[1], len(m)
}

func incDec() (int, int, int) {
	m := map[any]int{}
	m[1]++
	m[1]++
	m["a"]--
	m[1.0]++
	return m[1], m["a"], len(m)
}

func deleteDefaultType() (int, int) {
	m := map[any]int{1: 1, 2.5: 2}
	delete(m, 1.0)
	delete(m, 2.5)
	return len(m), m[1]
}

func commaOkRead() (int, bool, bool) {
	m := map[any]int{1: 1}
	v, ok := m[1]
	_, ok2 := m[1.0]
	return v, ok, ok2
}


func valueStore() (any, any, any, bool) {
	m := map[string]any{}
	m["i"] = 1
	m["f"] = 2.5
	m["d"] = tDef(3)
	m["n"] = nil
	return m["i"], m["f"], m["d"], m["n"] == nil
}

func nilKey() (int, bool, int) {
	m := map[any]int{}
	m[nil] = 7
	v, ok := m[nil]
	return v, ok, len(m)
}

func blankCommaOk() (bool, bool) {
	m := map[any]int{1: 1}
	var ok bool
	_, ok = m[1]
	var ok2 bool
	_, ok2 = m[1.0]
	return ok, ok2
}

func structKeyAnyField() (int, int, int) {
	m := map[kAny]int{}
	m[kAny{1}] = 1
	m[kAny{"a"}] = 2
	return m[kAny{A: 1}], m[kAny{1.0}], len(m)
}

func unseqMapStore() (any, int) {
	m := map[any]any{}
	m[g()] = h()
	return m[1], len(m)
}

func main() {
	storeRead()
}
