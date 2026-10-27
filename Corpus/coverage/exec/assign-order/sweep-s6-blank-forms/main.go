package main

// S6 sweep, group B: the blank identifier beside effects — a blank target
// still evaluates its right-hand side in phase 1 (its panic fires, its call
// runs); the other targets' checks stay phase 2.

func bRecover(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

func bWit(n int) int { println("wit", n); return n }

// B.1: `_ = a[9]` evaluates the read — it panics.
func bBlankIndexPanics() int {
	a := []int{0}
	_ = a[9]
	return 0
}

func bBoom2() (int, int) { panic("boom") }

// B.2: `_, x = f()` with f panicking — x keeps its value.
func bBlankCallPanicsNoStore() int {
	x := 5
	hit := bRecover(func() { _, x = bBoom2() })
	return hit*100 + x
}

func bBoom1() int { panic("boom") }

// B.3: an out-of-range first target beside a blank whose right-hand call
// panics: the call's panic (phase 1), never the bounds check (phase 2).
func bOobTargetVsBlankCallPanic() int {
	a := []int{0}
	a[9], _ = 1, bBoom1()
	return 0
}

// B.4: a blank first target's call runs, then the nil-map second target's
// store panics.
func bBlankThenNilMap() int {
	var m map[int]int
	_, m[1] = bWit(1), 2
	return 0
}

// B.6: a blank ok target on the comma-ok map read and on the receive.
func bBlankOkForms() int {
	m := map[int]int{1: 7}
	ch := make(chan int, 1)
	ch <- 3
	x, y := 0, 0
	x, _ = m[1]
	y, _ = <-ch
	return x*10 + y
}

// B.7: a blank FIRST target (with a call) and a later target whose index
// operand is an earlier target — the operand is the OLD i.
func bBlankFirstDepIndex() int {
	i := 0
	a := []int{10, 20, 30}
	_, i, a[i] = bWit(0), 2, 99
	return i*10000 + a[0]*100 + a[1]
}

// B.10: a blank target between two deref targets through one pointer — the
// left-to-right stores skip the blank.
func bBlankBetweenAliases() int {
	v := 0
	p := &v
	*p, _, *p = 1, 2, 3
	return v
}

// B.11: `_, ok = m[k]` with a key-operand panic (phase 1).
func bBlankCommaOkKeyPanic() int {
	m := map[int]int{}
	k := []int{0}
	ok := true
	hit := bRecover(func() { _, ok = m[k[9]] })
	if ok {
		return hit*100 + 10
	}
	return hit * 100
}

func main() {
	bBlankIndexPanics()
}
