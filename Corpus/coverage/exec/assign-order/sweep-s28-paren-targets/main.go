// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised TARGETS at every
// target kind and statement form: the canonical spelling lowers, so the parenthesised one
// must lower to the same store; expected = gc go1.26.5.

package main

type pt struct{ f, g int }

var garr [3]int

func parenLocalIncDecCompound() int {
	x := 1
	(x)++
	(x) += 10
	(x) <<= 1
	(x)--
	return x // 23
}

func parenSliceElemTargets() int {
	s := []int{1, 2, 3}
	(s[0]) = 10
	(s[1])++
	(s[2]) += 5
	return s[0]*100 + s[1]*10 + s[2] // 1038
}

func parenArrayElemTargets() int {
	var a [3]int
	(a[0]) = 4
	(a[1])++
	(garr[2]) = 9
	(garr[0]) += 2
	return a[0]*1000 + a[1]*100 + garr[2]*10 + garr[0] // 4192
}

func parenFieldTargets() int {
	p := &pt{}
	v := pt{}
	(p.f) = 3
	(p.g)++
	((p).f) += 10
	(p).g += 100
	(*p).f++
	((*p).g)++
	(v.f) = 7
	(v).g = 8
	return p.f*10000 + p.g*100 + v.f*10 + v.g // 140278
}

func parenDerefTargets() int {
	x := 5
	p := &x
	pp := &p
	(*p) = 6
	(*p) += 10
	(*(p))++
	(**pp) *= 2
	return x // 34
}

func two() (int, int) { return 40, 2 }

func parenMultiTargets() int {
	a, b := 1, 2
	(a), (b) = 3, 4
	(a), (b) = (b), (a)
	var c, d int
	(c), d = two()
	return a*1000 + b*100 + c + d // 4342
}

type boxI interface{ val() int }
type boxT struct{ n int }

func (b boxT) val() int { return b.n }

func parenCommaOkTargets() int {
	m := map[string]int{"a": 5}
	var v, ok1 int
	var ok bool
	(v), ok = m["a"]
	if !ok {
		return -1
	}
	ch := make(chan int, 1)
	ch <- 7
	var w int
	var ok2 bool
	(w), (ok2) = <-ch
	var i boxI = boxT{9}
	var t boxT
	var ok3 bool
	(t), (ok3) = i.(boxT)
	ok1 = 0
	if ok2 && ok3 {
		ok1 = 1
	}
	return v*1000 + w*100 + t.n*10 + ok1 // 5791
}

func parenSendRecv() int {
	ch := make(chan int, 2)
	(ch) <- 1
	ch <- 2
	<-(ch)
	v := <-(ch)
	(ch) <- 5
	var w int
	(w) = <-(ch)
	ch <- 6
	var ok bool
	var u int
	u, ok = <-(ch)
	if !ok {
		return -1
	}
	return v*100 + w*10 + u // 256
}

func parenSelectForms() int {
	ch := make(chan int, 1)
	out := make(chan int, 1)
	ch <- 3
	var v int
	select {
	case (v) = <-ch:
	}
	select {
	case (out) <- v*2:
	}
	var w int
	var ok bool
	select {
	case w = <-(out):
	}
	ch <- 4
	select {
	case (w), (ok) = <-ch:
	}
	ch <- 1
	select {
	case (<-ch):
		w += 100
	}
	if !ok {
		return -1
	}
	return v*10 + w // 134
}

func parenDeepNesting() int {
	x := 1
	((x)) = 5
	s := []int{1}
	((s[0]))++
	(((x)))++
	return x*10 + s[0] // 62
}

func main() {
	println("parenLocalIncDecCompound", parenLocalIncDecCompound())
	println("parenSliceElemTargets", parenSliceElemTargets())
	println("parenArrayElemTargets", parenArrayElemTargets())
	println("parenFieldTargets", parenFieldTargets())
	println("parenDerefTargets", parenDerefTargets())
	println("parenMultiTargets", parenMultiTargets())
	println("parenCommaOkTargets", parenCommaOkTargets())
	println("parenSendRecv", parenSendRecv())
	println("parenSelectForms", parenSelectForms())
	println("parenDeepNesting", parenDeepNesting())
}
