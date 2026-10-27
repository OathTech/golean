package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the uncomparable
// dynamic type panic under `==` (spec#Comparison_operators: «A comparison of
// two interface values with IDENTICAL dynamic types causes a run-time panic if
// that type is not comparable») at the routes interfaces/interface-compare-panic
// and generics/comparable-runtime-edge do not pin — the NO-panic controls where
// the dynamic types differ (uncomparable vs uncomparable, uncomparable vs
// comparable, vs nil), a boxed pointer to an uncomparable struct and a channel
// of slices (both comparable); the `!=` form and the recover route.

type ucBag struct{ items []int }

func differentDynamicTypes() int {
	var x any = []int{1}
	var y any = []string{"a"}
	if x == y {
		return 1
	}
	return 0
}

func mixedWithComparable() int {
	var x any = []int{1}
	var y any = 1
	if x == y {
		return 1
	}
	return 0
}

func vsNil() int {
	var x any = []int{1}
	if x == nil {
		return 1
	}
	return 0
}

func notEqual() int {
	var x any = []int{1}
	var y any = []int{1}
	if x != y {
		return 1
	}
	return 0
}

func pointerToUncomparableOk() int {
	b := &ucBag{items: []int{1}}
	var x any = b
	var y any = b
	if x == y {
		return 1
	}
	return 0
}

func chanOfSliceOk() int {
	c := make(chan []int)
	var x any = c
	var y any = c
	if x == y {
		return 1
	}
	return 0
}

func uncomparableRecovered() int {
	var x any = []int{1}
	var y any = []int{1}
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		if x == y {
			r = 1
		}
	}()
	return r + 1
}

func main() {}
