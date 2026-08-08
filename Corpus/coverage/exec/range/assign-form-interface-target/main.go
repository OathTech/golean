package main

// ASSIGN-form range (`for i, v = range X`) into INTERFACE-typed targets
// must box the key/value like any other assignment (spec §For statements:
// the iteration values are ASSIGNED to the iteration variables). BUG-050
// (codex-landing skeptical review, 2026-08-08, verifier-confirmed four-form
// matrix): emitRange's bind closure emitted `outer = $rangeKey/$rangeVal`
// with no wrapInterfaceConversion, so a raw value landed in the interface
// variable — a SILENT wrong answer (both sides status ok, observations
// differ), escalating to wrong-stuck on a later assertion. Same
// wrapInterfaceConversion-omission family as BUG-049's call-argument arm.
// All four forms + the escalation shape, single-iteration-deterministic.

// Slice VALUE form: v gets the element (int) — must box into any.
func rangeAssignSliceValue() any {
	var v any
	xs := []int{3, 4}
	for _, v = range xs {
	}
	return v // Go: interface-boxed int 4
}

// Map KEY form: k gets the map key (int) — must box into any.
func rangeAssignMapKey() any {
	m := map[int]string{7: "a"} // single entry: deterministic
	var k any
	for k = range m {
	}
	return k // Go: interface-boxed int 7
}

// INDEX form: i gets the index (int) — must box into any.
func rangeAssignIndex() any {
	var i any
	xs := []int{5, 6}
	for i = range xs {
	}
	return i // Go: interface-boxed int 1
}

// String RUNE form: r gets the rune (int32) — must box into any.
func rangeAssignStringRune() any {
	var r any
	for _, r = range "ab" {
	}
	return r // Go: interface-boxed int32 98
}

// Escalation shape: asserting the (unboxed) value inside the loop turns
// the silent wrong answer into a wrong-stuck.
func rangeAssignAssertEscalation() int {
	var v any
	sum := 0
	xs := []int{3, 4}
	for _, v = range xs {
		sum += v.(int)
	}
	return sum // Go: 7
}

func main() {
	rangeAssignSliceValue()
	rangeAssignMapKey()
	rangeAssignIndex()
	rangeAssignStringRune()
	rangeAssignAssertEscalation()
}
