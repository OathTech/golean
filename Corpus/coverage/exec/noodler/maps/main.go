// noodler probes — map edges: compound assignment order, NaN inside
// composite keys, zero-size keys, nil inner maps, func values
// (spec#Map_types, spec#Index_expressions, spec#Assignment_statements).
package main

// m[k] op= f() where f mutates m[k]: the element is read once, after
// the call (calls first).
func mapCompoundCallMutates() int {
	m := map[int]int{1: 10}
	f := func() int { m[1] = 100; return 5 }
	m[1] += f()
	return m[1]
}

// a[i] op= f() where f mutates a[i].
func sliceCompoundCallMutates() int {
	a := []int{10}
	f := func() int { a[0] = 100; return 5 }
	a[0] += f()
	return a[0]
}

// m[k] op= f() where f DELETES the key: the element read after the call
// sees the zero value.
func mapCompoundCallDeletes() (int, int) {
	m := map[int]int{1: 10}
	f := func() int { delete(m, 1); return 5 }
	m[1] += f()
	return m[1], len(m)
}

// An array key containing NaN never matches: each insert is a new entry.
func arrayKeyWithNaN() (int, bool) {
	zero := 0.0
	nan := zero / zero
	m := map[[1]float64]int{}
	k := [1]float64{nan}
	m[k] = 1
	m[k] = 2
	_, ok := m[k]
	return len(m), ok
}

// A struct key containing NaN likewise.
func structKeyWithNaN() (int, bool) {
	type K struct {
		s string
		f float64
	}
	zero := 0.0
	nan := zero / zero
	m := map[K]int{}
	m[K{"a", nan}] = 1
	m[K{"a", nan}] = 2
	m[K{"a", 1}] = 3
	m[K{"a", 1}] = 4
	_, ok := m[K{"a", 1}]
	return len(m), ok
}

// delete with a NaN key deletes nothing.
func deleteNaNKey() int {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{}
	m[nan] = 1
	m[nan] = 2
	delete(m, nan)
	return len(m)
}

// Zero-size keys: every value is equal, so there is one entry.
func zeroSizeKeys() (int, int) {
	m := map[[0]int]int{}
	m[[0]int{}] = 1
	m[[0]int{}] = 2
	n := map[struct{}]int{}
	n[struct{}{}] = 5
	n[struct{}{}] = 6
	return len(m)*10 + m[[0]int{}], len(n)*10 + n[struct{}{}]
}

// Reading through a missing inner map is fine; writing panics.
func nilInnerMapRead() (int, bool) {
	m := map[string]map[string]int{}
	v, ok := m["a"]["b"]
	return v + len(m["a"]), ok
}

func nilInnerMapWrite() int {
	m := map[string]map[string]int{}
	m["a"]["b"] = 1
	return len(m)
}

// IncDec on a nil map panics with the assignment text.
func nilMapIncDec() int {
	var m map[string]int
	m["a"]++
	return len(m)
}

// Map of func values: present key calls; missing key is a nil func.
func mapOfFuncs() int {
	m := map[string]func(int) int{"double": func(x int) int { return 2 * x }}
	return m["double"](4)
}

func mapOfFuncsMissingKeyCall() int {
	m := map[string]func(int) int{}
	return m["nope"](4)
}

// Value-receiver method call on a map element is fine (a copy).
type counter struct{ n int }

func (c counter) Doubled() int { return c.n * 2 }

func methodOnMapElement() int {
	m := map[int]counter{1: {21}}
	return m[1].Doubled()
}

// String keys differing only in invalid bytes are distinct.
func invalidByteStringKeys() (int, int) {
	m := map[string]int{}
	m["\xff"] = 1
	m["\xc3\xbf"] = 2
	m["ÿ"] = 3
	return len(m), m["\xff"]
}

// A string key built from a []byte is independent of later mutation.
func stringKeyFromBytesIndependent() int {
	b := []byte("k")
	m := map[string]int{}
	m[string(b)] = 1
	b[0] = 'x'
	return m["k"]*10 + m["x"]
}

// Map element struct copy: modifying the copy does not change the map.
func mapElementCopy() int {
	m := map[int]counter{1: {5}}
	v := m[1]
	v.n = 99
	return m[1].n
}

// Swap two entries where one is missing.
func swapWithMissing() (int, int, int) {
	m := map[string]int{"a": 1}
	m["a"], m["b"] = m["b"], m["a"]
	return m["a"], m["b"], len(m)
}

// Two map-element targets in one tuple assignment.
func tupleAssignTwoMapTargets() int {
	m := map[string]int{}
	m["a"], m["b"] = 1, 2
	return m["a"]*10 + m["b"]
}

// A map-element target beside a plain variable target.
func tupleAssignMapAndVar() (int, int) {
	m := map[string]int{}
	var x int
	m["a"], x = 1, 2
	return m["a"], x
}

// Map of slices: append through the map value.
func mapOfSlicesAppend() (int, int) {
	m := map[int][]int{}
	for i := 0; i < 5; i++ {
		m[i%2] = append(m[i%2], i)
	}
	return len(m[0]), len(m[1])
}

// Extreme int keys are distinct.
func extremeIntKeys() int {
	m := map[int64]int{}
	m[-1<<63] = 1
	m[1<<63-1] = 2
	m[0] = 3
	m[-1] = 4
	return len(m)*10 + m[-1<<63]
}

// A single-entry map ranges deterministically.
func singleEntryRange() (string, int) {
	m := map[string]int{"only": 7}
	for k, v := range m {
		return k, v
	}
	return "", 0
}

// Map with interface keys holding NaN: inserts are distinct and never
// found.
func interfaceKeyNaN() (int, bool) {
	zero := 0.0
	nan := zero / zero
	m := map[any]int{}
	m[nan] = 1
	m[nan] = 2
	_, ok := m[nan]
	return len(m), ok
}

// Map of arrays: element read then whole-array replace.
func mapOfArrays() int {
	m := map[int][2]int{1: {3, 4}}
	x := m[1][1]
	a := m[1]
	a[0] = 9
	m[1] = a
	return x*100 + m[1][0]*10 + m[1][1]
}

func main() {}
