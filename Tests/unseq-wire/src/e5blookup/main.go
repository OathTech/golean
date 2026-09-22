package main

// E5BLOOKUP (Stage E5 audit fix round F1, 2026-09-22 — lane core/unseq-stage-e5-0922): the
// `wide map-lookup` arm's POSITIVE CONTROL, which no tracked wire and no corpus row exercised
// before the round (the audit reached the arm through its own probe). `xs[f()], ok = m[1]` with
// m captured by f, which DELETES m[1] and returns 0: the comma-ok lookup is a RESIDUAL two-binder
// `wide` body (a read of the frozen map value, no E1 edge) unordered against f — before the
// delete (1, true): xs[0] = 1, ok → 11; after it (0, false) → 0 (gc's, call-first). The planned
// element target's index is f's result. Reference enumerate.py E5b5; {11, 0}.
func e5blookup() int {
	m := map[int]int{1: 1}
	xs := []int{0, 0}
	f := func() int { delete(m, 1); return 0 }
	var ok bool
	xs[f()], ok = m[1]
	if ok {
		return xs[0] + 10
	}
	return xs[0]
}

func main() { println(e5blookup()) }
