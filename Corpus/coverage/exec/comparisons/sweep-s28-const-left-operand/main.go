// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). BUG-136's local space: an
// untyped constant on the LEFT of a comparison or an arithmetic operator at every kind
// (the entry measured them without rows), the parenthesised constant, and the shift
// forms; expected = gc go1.26.5.

package main

type myInt int

func constLeftComparisons() int {
	x := 1
	s := "a"
	f := 1.5
	b := true
	r := 'a'
	var m myInt = 3
	var i any = 1
	n := 0
	if 1 == x {
		n += 1
	}
	if "a" == s {
		n += 10
	}
	if 1.5 == f {
		n += 100
	}
	if true == b {
		n += 1000
	}
	if 'a' == r {
		n += 10000
	}
	if 3 == m {
		n += 100000
	}
	if 1 == i {
		n += 1000000
	}
	if 2 < x {
		n += 10000000
	}
	if "b" > s {
		n += 100000000
	}
	if (1) == x {
		n += 1000000000
	}
	return n // 1101111111
}

func constLeftArithmetic() int {
	x := 3
	n := 2
	var m myInt = 4
	r := 1 + x
	r += 10 * x
	r += 100 - x
	r += 1 << n
	r += n << 1
	r += 1 << (n)
	r += (1) << n
	r += int(2 * m)
	r += 7 % x
	r += 9 / x
	return r // 4+30+97+4+4+4+4+8+1+3 = 159
}

func main() {
	println("constLeftComparisons", constLeftComparisons())
	println("constLeftArithmetic", constLeftArithmetic())
}
