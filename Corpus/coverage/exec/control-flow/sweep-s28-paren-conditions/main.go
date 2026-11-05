// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised conditions, switch
// tags and cases, type-switch guards, and return operands; expected = gc go1.26.5.

package main

func one() int { return 1 }

func pair() (int, int) { return 3, 4 }

func parenIfConds() int {
	x := 1
	b := true
	n := 0
	if (b) {
		n += 1
	}
	if (x == 1) {
		n += 10
	}
	if (x) == 1 {
		n += 100
	}
	if y := (one()); (y) > 0 {
		n += 1000
	}
	if ((x)) == (1) {
		n += 10000
	}
	return n // 11111
}

func parenForConds() int {
	n := 0
	i := 0
	for (i < 3) {
		i++
		n++
	}
	for ; (i) < 6; (i)++ {
		n += 10
	}
	for j := (0); (j < 2); j++ {
		n += 100
	}
	return n // 233
}

func parenSwitchTags() int {
	x := 2
	n := 0
	switch (x) {
	case (1):
		n += 1
	case (2):
		n += 2
	}
	switch {
	case (x > 1):
		n += 10
	}
	switch (one()) {
	case 1:
		n += 100
	}
	switch y := (one()); (y) {
	case (1):
		n += 1000
	}
	switch (x) {
	case (1), (2), (3):
		n += 10000
	}
	return n // 11112
}

type shape interface{ area() int }
type sq struct{ s int }

func (q sq) area() int { return q.s * q.s }

func parenTypeSwitches() int {
	var x any = sq{3}
	n := 0
	switch v := (x).(type) {
	case (int):
		n += v
	case (sq):
		n += v.area()
	}
	switch (x).(type) {
	case (*sq):
		n += 100
	case (shape):
		n += 10
	}
	var y any
	switch (y).(type) {
	case (nil):
		n += 1000
	}
	switch v := (x).(type) {
	case (int), (string):
		_ = v
	case (sq), (int8):
		n += 10000
	}
	return n // 11019
}

func retParen() int { return (one()) }

func retParens() (int, int) { return (1), (2) }

func retDoubleParen() int { return ((one())) }

func parenReturns() int {
	a := retParen()
	b, c := retParens()
	d := retDoubleParen()
	return a*1000 + b*100 + c*10 + d // 1121
}

func main() {
	println("parenIfConds", parenIfConds())
	println("parenForConds", parenForConds())
	println("parenSwitchTags", parenSwitchTags())
	println("parenTypeSwitches", parenTypeSwitches())
	println("parenReturns", parenReturns())
}
