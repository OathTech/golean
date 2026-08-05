package main

// Composite-literal &T elision — spec §Composite literals: "elements or
// keys that are addresses of composite literals may elide the &T when
// the element or key type is *T." The frontend only handled the
// explicit &T{...} spelling (emitAddressOf's hoist); the elided form
// hit emitCompositeLit's default and quarantined. Includes the spec's
// own example shape ([2]*Point{{1.5, -3.5}, {}}). Arc-final audit F12
// (2026-08-06), red-first.

type pleP struct{ x, y int }

func elisionMapValue() int {
	m := map[string]*pleP{"a": {5, 6}}
	return m["a"].x*10 + m["a"].y
}

func elisionSliceElem() int {
	ps := []*pleP{{1, 2}, {3, 4}}
	return ps[0].x + ps[1].y
}

type plePoint struct{ x, y float64 }

// The spec's own example, verbatim shape.
func elisionSpecExample() float64 {
	ps := [2]*plePoint{{1.5, -3.5}, {}}
	return ps[0].x + ps[0].y + ps[1].x
}

func elisionMapKey() int {
	m := map[pleP]int{{7, 8}: 9}
	return m[pleP{7, 8}]
}

// Pointer KEY type: the key literal elides &pleP.
func elisionPtrKey() int {
	m := map[*pleP]int{{7, 8}: 9}
	total := 0
	for k, v := range m {
		total += k.x*100 + k.y*10 + v
	}
	return total
}

// CONTROL: the explicit &T{...} spelling, already supported.
func elisionCtlExplicit() int {
	m := map[string]*pleP{"a": &pleP{5, 6}}
	return m["a"].x*10 + m["a"].y
}
