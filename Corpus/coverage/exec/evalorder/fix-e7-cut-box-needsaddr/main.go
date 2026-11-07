package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), the train-31 pre-merge audit's finding B on BUG-311's
// scope: gc's order pass (walk/order.go OCONVIFACE) copies to a temp at its position EVERY
// non-addressable operand converted to an interface whose type goes by address (convert.go
// dataWordFuncName needsaddr: not 2/4/8 bytes pointer-free, not a sole-component string or slice) —
// a composite literal, a pointer literal, a comparison, a conversion — so it reads its operands before a
// later sibling call; the legacy path read them late (declined sweeps: the if-condition form). The
// by-value kinds (int16, int32, int, string, a slice, a one-int struct, a one-element array) stay late
// on both sides. Each subject answers 1 when the boxed value saw n before set() (gc's), 2 after.

type P struct{ a, b int }
type Q struct{ a int }
type R struct {
	p *int
	k int
}

var n int
var s = "ab"

func set() int { n = 5; s = "zz"; return 0 }
func val(x any) int {
	switch v := x.(type) {
	case bool:
		if v {
			return 1
		}
		return 0
	case int8:
		return int(v)
	case int16:
		return int(v)
	case int32:
		return int(v)
	case int:
		return v
	case string:
		return len(v)
	case []int:
		return v[0]
	case [2]int:
		return v[0]
	case [1]int:
		return v[0]
	case P:
		return v.a
	case Q:
		return v.a
	case R:
		return v.k
	case *P:
		return v.a
	}
	return -1
}
func sinkAny(x any, k int) int { return val(x)*100 + k }

// Each subject spells the audit's declined form (the boxing call inside an if-condition), so the
// legacy path realizes one member on both sides; a plain return or a call's call argument is a sweep
// the unseq grammar admits, where the machine enumerates both members instead.
func boolCmp() int {
	if sinkAny(n > 0, set()) == 0 {
		return 1
	}
	return 2
}
func int8Conv() int {
	if sinkAny(int8(n), set()) == 0 {
		return 1
	}
	return 2
}
func array2Lit() int {
	if sinkAny([2]int{n, 0}, set()) == 0 {
		return 1
	}
	return 2
}
func structLit() int {
	if sinkAny(P{n, 0}, set()) == 0 {
		return 1
	}
	return 2
}
func ptrStruct() int {
	if sinkAny(R{&n, n}, set()) == 0 {
		return 1
	}
	return 2
}
func ptrLit() int {
	if sinkAny(&P{n, 0}, set()) == 0 {
		return 1
	}
	return 2
}
func int16Conv() int {
	if sinkAny(int16(n), set()) == 0 {
		return 1
	}
	return 2
}
func int32Conv() int {
	if sinkAny(int32(n), set()) == 0 {
		return 1
	}
	return 2
}
func intArith() int {
	if sinkAny(n+0, set()) == 0 {
		return 1
	}
	return 2
}
func stringCat() int {
	if sinkAny(s+"", set()) == 0 {
		return 1
	}
	return 2
}
func sliceLit() int {
	if sinkAny([]int{n}, set()) == 0 {
		return 1
	}
	return 2
}
func array1Lit() int {
	if sinkAny([1]int{n}, set()) == 0 {
		return 1
	}
	return 2
}
func oneIntLit() int {
	if sinkAny(Q{n}, set()) == 0 {
		return 1
	}
	return 2
}

func main() {
	println(boolCmp(), int8Conv(), array2Lit(), structLit(), ptrStruct(), ptrLit(), int16Conv(), int32Conv(), intArith(), stringCat(), sliceLit(), array1Lit(), oneIntLit())
}
