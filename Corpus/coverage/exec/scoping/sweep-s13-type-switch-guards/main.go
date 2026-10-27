package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the type-switch
// guard's binding (spec#Type_switches: one variable PER CLAUSE, typed by a
// single-type case, else by the guard's interface type; go/types Implicits,
// typeSwitchClauseBody) — at each clause kind, shadowed in a clause, captured
// and mutated by a closure, addressed, with an init statement, nested under
// the same name, per iteration, shadowing a parameter.
// scoping/type-switch-guard-shadow holds the int clause under an outer v.
// Expected = gc go1.26.5.

func clauseKind(x any) int {
	switch v := x.(type) {
	case int:
		return v + 1
	case string:
		return len(v) * 10
	case bool, float64:
		if _, isB := v.(bool); isB { // v keeps the interface type
			return 100
		}
		return 200
	}
	return -1
}

// G1
func clauseTypes() int {
	return clauseKind(1) + clauseKind("abc") + clauseKind(true) + clauseKind(1.5) // 332
}

// G2
func defaultIface() int {
	var x any = int8(3)
	switch v := x.(type) {
	case int:
		return -1
	default:
		if b, ok := v.(int8); ok {
			return int(b) * 2 // 6
		}
	}
	return -2
}

// G3
func nilClause() int {
	var x any
	switch v := x.(type) {
	case nil:
		if v == nil {
			return 1
		}
		return 2
	default:
		return 3
	}
}

// G4 (a `v := v * 2` directly in the clause is REJECTED by gc — the guard's binding shares the
// clause's block: negative scoping/sweep-s13-ts-guard-clause-redefine; the shadow needs a block).
func clauseShadow() int {
	var x any = 5
	switch v := x.(type) {
	case int:
		{
			v := v * 2
			return v // 10
		}
	}
	return -1
}

// G5
func clauseCapture() int {
	var x any = 5
	switch v := x.(type) {
	case int:
		f := func() { v += 10 }
		f()
		f()
		return v // 25
	}
	return -1
}

// G6 / F5
func withInit() int {
	var y any = "hello"
	switch x := 2; v := y.(type) {
	case string:
		return len(v) * x // 10
	}
	return -1
}

// G7
func nestedSameName() int {
	var a any = 3
	var b any = "xy"
	switch v := a.(type) {
	case int:
		switch v := b.(type) {
		case string:
			return len(v) * 100 // 200
		}
		return v
	}
	return -1
}

// G9
func perIterationCapture() int {
	xs := []any{1, 2, 3}
	var fs []func() int
	for _, x := range xs {
		switch v := x.(type) {
		case int:
			fs = append(fs, func() int { return v })
		}
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 123
}

func guardShadowsParam(v int) int {
	var x any = "abcd"
	switch v := x.(type) {
	case string:
		return len(v) // 4
	}
	return v
}

// G10
func shadowsParam() int { return guardShadowsParam(9)*10 + guardShadowsParam(0) } // 44

// G12
func clauseAddr() int {
	var x any = 7
	switch v := x.(type) {
	case int:
		p := &v
		*p += 1
		return v // 8
	}
	return -1
}

func main() {
	println(clauseTypes(), defaultIface(), nilClause(), clauseShadow(), clauseCapture(), withInit(),
		nestedSameName(), perIterationCapture(), shadowsParam(), clauseAddr())
}
