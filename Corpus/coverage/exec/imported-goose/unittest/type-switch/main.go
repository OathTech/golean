// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/type_switch.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func typeAssertInt(x any) int {
	return x.(int)
}

func wrapUnwrapInt() int {
	return typeAssertInt(1)
}

func checkedTypeAssert(x any) uint64 {
	if v, ok := x.(uint64); ok {
		return v
	}
	return 3
}

func basicTypeSwitch(x any) int {
	switch x.(type) {
	case int:
		return 1
	case string:
		return 2
	}
	return 0
}

func fancyTypeSwitch(x any) int {
	var r int
	switch z := 0; y := x.(type) {
	case int:
		return y
	default:
		z = 3
		r = z
	case string:
		return 2
	case nil:
		return 4
	}
	return r
}

func multiTypeSwitch(x any) int {
	switch x.(type) {
	case int, string:
		return 1
	}
	return 0
}

// --- GoLean harness ---
// Authored wrapper.

func goleanTypeSwitch() int {
	sum := wrapUnwrapInt()
	sum += int(checkedTypeAssert(uint64(7)))*10 + int(checkedTypeAssert("s"))*100
	sum += basicTypeSwitch(1)*1000 + basicTypeSwitch("x")*10000 + basicTypeSwitch(1.5)*100000
	sum += fancyTypeSwitch(5) + fancyTypeSwitch("a")*7 + fancyTypeSwitch(nil)*11 + fancyTypeSwitch(true)*13
	return sum
}

func main() {}
