package main

// Untyped `nil` flowing into a nilable-typed slot (slice/map/pointer)
// in EVERY assignable context the spec's Assignability rule names —
// not just the map-literal element position the corpus happened to pin
// (BUG-014's fix site). Each subject used to leave a RAW machine nil in
// the slot, and the first len/append/index on it went
// unsupported/stuck. The dominant real-Go shapes: `return nil` from a
// []T function (etcd-raft's log_unstable.nextEntries), nil literals in
// table-driven-test struct rows, [][]int{nil, {...}} grids. Arc-final
// audit F6 (2026-08-06), red-first.

type unsRow struct {
	name string
	in   []int
}

type unsNode struct {
	label string
	deps  []string
	index map[string]int
}

// struct-literal FIELD position.
func unsStructLitField() int {
	c := unsRow{"empty", nil}
	return len(c.in)
}

// struct-literal field then APPEND (the machine-stuck variant).
func unsStructLitAppend() int {
	c := unsRow{in: nil}
	c.in = append(c.in, 7, 8)
	return len(c.in)
}

// nil MAP field: range and index read on it.
func unsStructLitMapField() int {
	n := unsNode{label: "c", deps: nil, index: nil}
	total := len(n.index)
	for range n.index {
		total += 100
	}
	return total + n.index["missing"]
}

// slice-literal ELEMENT position.
func unsSliceLitElem() int {
	g := [][]int{nil, {1, 2}}
	return len(g[0])*10 + len(g[1])
}

// array-literal ELEMENT position.
func unsArrayLitElem() int {
	g := [2][]int{nil, {1, 2}}
	return len(g[0])*10 + len(g[1])
}

// RETURN statement (the ubiquitous shape).
func unsReturnNil(empty bool) []int {
	if empty {
		return nil
	}
	return []int{1, 2, 3}
}

func unsReturn() int {
	return len(unsReturnNil(true))*10 + len(unsReturnNil(false))
}

// CALL ARGUMENT position.
func unsLen(xs []int) int { return len(xs) }

func unsCallArg() int {
	return unsLen(nil)
}

// PLAIN ASSIGNMENT (var then =nil; and re-assignment of a live slice).
func unsPlainAssign() int {
	xs := []int{1}
	xs = nil
	var row unsRow
	row.in = nil
	return len(xs) + len(row.in)
}

// VARIADIC spread slot: nil as the packed variadic slice.
func unsSum(xs ...int) int {
	t := 0
	for _, x := range xs {
		t += x
	}
	return t
}

func unsVariadicSpread() int {
	return unsSum(nil...)
}

// nested: map-literal VALUE holding a struct whose field is nil.
func unsNestedMapValue() int {
	graph := map[string]unsNode{"c": {"c", nil, nil}}
	return len(graph["c"].deps)
}

// CONTROL: map-literal element position (BUG-014's fixed site).
func unsCtlMapLitValue() int {
	m := map[string][]int{"a": nil}
	return len(m["a"]) + 10
}

// CONTROL: zero-value declaration (a different, correct lowering).
func unsCtlZeroValue() int {
	var xs []int
	return len(xs)
}
