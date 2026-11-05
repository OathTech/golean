package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-001's line): conversion SPELLINGS (the kernel arms are S2's,
// sweep/s2-conversions) — a parenthesised directional channel type, a
// parenthesised map type, the `interface{}` literal spelling, a conversion
// followed by a method call / a field / an index, and a conversion in a
// condition and a defer argument. Expected = gc go1.26.5.

var calls int

type pt struct{ x, y int }

func (p pt) sum() int { return p.x + p.y }

type raw struct{ x, y int }

type bytesT []byte

type flag bool

func take(x int64) { calls += int(x) }

// B10.2
func parenChanDir() int {
	ch := make(chan int, 1)
	r := (<-chan int)(ch)
	s := (chan<- int)(ch)
	s <- 3
	return <-r // 3
}

func parenMap() int {
	type m map[string]int
	x := m{"a": 4}
	y := (map[string]int)(x)
	return y["a"] // 4
}

func parenIfaceLiteral() int {
	v := interface{}(5)
	return v.(int) // 5
}

// B10.3
func convThenMethod() int {
	r := raw{1, 2}
	return pt(r).sum() // 3
}

func convThenField() int {
	r := raw{6, 7}
	return pt(r).x*10 + pt(r).y // 67
}

func convThenIndex() int {
	s := "ab"
	return int([]byte(s)[1])*1000 + int(bytesT(s)[0]) + len(string([]byte{'x', 'y'})[1:]) // 98000 + 97 + 1 = 98098
}

// B10.5
func convCond() int {
	var f flag = true
	x := 2.9
	r := 0
	if bool(f) && int(x) == 2 {
		r = 1
	}
	return r // 1
}

func convDeferArg() int {
	calls = 0
	x := 8
	func() {
		defer take(int64(x))
		x = 100
	}()
	return calls // 8
}

func main() {
	println(parenChanDir(), parenMap(), parenIfaceLiteral(), convThenMethod(), convThenField(), convThenIndex(),
		convCond(), convDeferArg())
}
