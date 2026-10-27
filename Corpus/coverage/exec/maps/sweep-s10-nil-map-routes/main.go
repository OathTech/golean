package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the nil-map WRITE panic
// (spec#Index_expressions: «Assigning to an element of a nil map causes a
// run-time panic») at the routes maps/map-nil-assign and maps/multi-target do
// not pin — the IncDec and compound forms, the append idiom (a read then a
// write), struct-, slice- and map-valued elements, a write through a parameter
// and through a struct field, the recover route; and the ORDER against the
// unhashable-key hash (gc's mapassign checks the nil map before hashing).
// `clear` of a nil map is builtins/clear-delete-edge's.

type nmPair struct{ a, b int }

type nmHolder struct{ m map[string]int }

func nilMapIncdec() int {
	var m map[string]int
	m["k"]++
	return len(m)
}

func nilMapCompound() int {
	var m map[string]int
	m["k"] += 2
	return len(m)
}

func nilMapAppendIdiom() int {
	var m map[string][]int
	m["k"] = append(m["k"], 1)
	return len(m)
}

func nilMapStructValue() int {
	var m map[int]nmPair
	m[1] = nmPair{1, 2}
	return len(m)
}

func nilMapNestedMapValue() int {
	var m map[int]map[int]int
	m[1] = map[int]int{2: 3}
	return len(m)
}

func nilMapAssignUnhashableKey() int {
	var m map[any]int
	m[[]int{1}] = 1
	return len(m)
}

func nmWrite(m map[string]int) { m["k"] = 1 }

func nilMapThroughParam() int {
	var m map[string]int
	nmWrite(m)
	return len(m)
}

func nilMapThroughField() int {
	h := &nmHolder{}
	h.m["k"] = 1
	return len(h.m)
}

func nilMapRecovered() int {
	var m map[string]int
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		m["k"] = 1
	}()
	return r + len(m)
}

func main() {}
