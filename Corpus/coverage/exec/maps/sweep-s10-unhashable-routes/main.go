package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the unhashable dynamic
// map key panic (spec#Map_types: «If the key type is an interface type, these
// comparison operators must be defined for the dynamic key values; failure will
// cause a run-time panic») at the dynamic types and routes the maps/*unhashable*
// rows (slice keys, struct and array wrappers) do not pin — a map-typed and a
// func-typed dynamic key, a NAMED slice type through a non-empty interface key
// type, the comma-ok read, a generic map at K = any, the recover route; and the
// no-panic controls: a pointer to an uncomparable struct and a nil interface key.

type uhList []int

func (uhList) M() {}

type uhM interface{ M() }

type uhBag struct{ items []int }

func uhPut[K comparable, V any](m map[K]V, k K, v V) { m[k] = v }

func mapKey() int {
	m := map[any]int{}
	m[map[int]int{1: 1}] = 1
	return len(m)
}

func funcKey() int {
	m := map[any]int{}
	m[func() {}] = 1
	return len(m)
}

func namedSliceThroughMethodIface() int {
	m := map[uhM]int{}
	m[uhList{1}] = 1
	return len(m)
}

func commaOkRead() int {
	m := map[any]int{1: 1}
	_, ok := m[[]int{1}]
	if ok {
		return 1
	}
	return 0
}

func genericAnyKey() int {
	m := map[any]int{}
	uhPut(m, any([]int{1}), 1)
	return len(m)
}

func pointerKeyOk() int {
	m := map[any]int{}
	b := &uhBag{items: []int{1}}
	m[b] = 1
	m[b] += 1
	return m[b]*10 + len(m)
}

func nilIfaceKeyOk() int {
	m := map[any]int{}
	var k any
	m[k] = 7
	v, ok := m[nil]
	if ok {
		return v
	}
	return 0
}

func unhashableRecovered() int {
	m := map[any]int{}
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		m[[]int{1}] = 1
	}()
	return r + len(m)
}

func main() {}
