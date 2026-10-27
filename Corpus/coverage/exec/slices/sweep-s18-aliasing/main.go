package main

// S18 sweep — the realized capacity decides ALIASING: a := append(nil, x); b := append(a, y);
// a write through b is visible through a exactly when the first spill's capacity had room
// for the second append. gc's plain build takes the stack buffer (room), -race the heap
// point (no room at an 8/16-byte element); both are members of the machine's set, which
// the row pins by members=. Probe-verified go1.26.5, 2026-10-27.

// gc plain 9, -race 1: both members exhibited
func aliasInt() int {
	a := append([]int(nil), 1)
	b := append(a, 2)
	b[0] = 9
	return a[0]
}

// gc plain 1, -race 0
func aliasStr() int {
	a := append([]string(nil), "x")
	b := append(a, "y")
	b[0] = "z"
	if a[0] == "z" {
		return 1
	}
	return 0
}

// gc plain 2, -race 1
func aliasPtr() int {
	x, y := 1, 2
	a := append([]*int(nil), &x)
	b := append(a, &y)
	b[0] = &y
	return *a[0]
}

// gc plain 9 (cap 4 exactly), -race 1
func aliasIntThree() int {
	a := append([]int(nil), 1)
	b := append(a, 2, 3, 4)
	b[0] = 9
	return a[0]
}

// gc 9 on both builds; the machine also admits 1 (the floor)
func aliasByte() int {
	a := append([]byte(nil), 1)
	b := append(a, 2)
	b[0] = 9
	return int(a[0])
}
