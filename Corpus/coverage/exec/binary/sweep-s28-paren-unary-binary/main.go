// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised unary and binary
// operands, address-of through parentheses, and a division panic through parentheses;
// expected = gc go1.26.5.

package main

type pt struct{ x, y int }

var trace []int

func rec(k int) int { trace = append(trace, k); return k }

func parenUnary() int {
	x := 3
	b := false
	p := &x
	ch := make(chan int, 1)
	ch <- 4
	s := []int{5}
	q := pt{6, 7}
	a := [2]int{8, 9}
	n := -(x) + 10
	if !(b) {
		n += 100
	}
	n += (^(x) + 4) * 1000 // ^3 = -4 → 0
	px := &(x)
	*px = 30
	n += *(p) * 10000 // 300000
	n += <-(ch)
	ps := &(s[0])
	*ps = 50
	pf := &(q.y)
	*pf = 70
	pl := &(pt{1, 2})
	pa := &(a[1])
	*pa = 90
	n += s[0] + q.y + pl.x + a[1] + (-(-(x))) + (+(x))
	return n // 7+100+0+300000+4+50+70+1+90+30+30 = 300382
}

func parenBinary() int {
	a, b, c := 2, 3, 4
	s, t := "ab", "cd"
	n := 0
	if (a) == (b) {
		n += 1000000
	}
	if (a) < (b) && (b) < (c) {
		n += 100000
	}
	n += ((a) + (b)) * c // 20
	n += (a + b) * (c) // 20
	n += (a) << (b) // 16
	n += len((s) + (t)) // 4
	n += (c) % (b) // 1
	n += (c) / (a) // 2
	return n // 100063
}

func parenBinaryOrder() int {
	trace = nil
	n := (rec(1)) + (rec(2))*(rec(3))
	for _, k := range trace {
		n = n*10 + k
	}
	return n // 7123
}

func parenDivZeroPanic() int {
	a, b := 1, 0
	return (a) / (b)
}

func main() {
	println("parenUnary", parenUnary())
	println("parenBinary", parenBinary())
	println("parenBinaryOrder", parenBinaryOrder())
	func() {
		defer func() { r := recover(); println("parenDivZeroPanic", "panic:", r.(error).Error()) }()
		println("parenDivZeroPanic", parenDivZeroPanic())
	}()
}
