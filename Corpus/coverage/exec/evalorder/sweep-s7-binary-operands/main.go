package main

// Defect-neighbourhood campaign, shape S7 (ordered events reordered by the hoist),
// lane sweep/s7-hoist-order, 2026-10-27: plan docs/2026-10-27_defect-neighbourhood-campaign.md
// §4 ([USER]-approved 2026-10-27); the matrix is on the member entries' Neighbourhood lines
// in docs/BUGS.md (BUG-113/062/058/026/023/145/144). spec#Order_of_evaluation: function
// calls, method calls, receive operations and binary logical operations are evaluated in
// lexical left-to-right order. Each subject returns its event log (a closure appends the
// name of each event as it runs); where a receive is in play its VALUE attests its order
// against a call that non-blockingly swaps the buffered element ("r1" if the receive came
// first, "after" if the call did).
//
// BINARY OPERANDS: two calls, a call and a receive each way, chains, comparisons; the BUG-113
// axis — a `||`/`&&` beside a lexically later call that mutates its right operand — at the
// operand kinds the unseq grammar admits (pointer field, nested field, assertion, map read,
// method call, receive, slice element, string index, len, global pointer field, a generic
// body, nested logical, a call on the left, a method call on the right, len before a
// receive, a struct field, a named result, a method body, a map-of-any assertion); the
// BUG-062 axis — cap and max(len) before a growing call. All born green. The operand kinds
// the grammar declines are the red package evalorder/sweep-s7-logical-legacy-kinds
// (BUG-277); every func-literal body is evalorder/sweep-s7-logical-in-closures (BUG-276).

type S struct {
	f     bool
	inner Inner
}

type Inner struct{ f bool }

type X struct{ v bool }

func (x X) M() bool { return x.v }

type Rr struct{ b *bool }

func (r Rr) Set() int { *r.b = true; return 0 }

var left = false

var gp = &S{}

func show(x bool, n int) string {
	if x {
		return "true " + itoa(n)
	}
	return "false " + itoa(n)
}

func gen[T any](_ T) string {
	b := false
	change := func() int { b = true; return 0 }
	return show(left || b, change())
}

func d30() (b bool, out string) {
	change := func() int { b = true; return 0 }
	out = show(left || b, change())
	return
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	s := ""
	for n > 0 {
		s = string(rune('0'+n%10)) + s
		n /= 10
	}
	return s
}

type S2 struct{ b bool }

type Rcv struct {
	left bool
	b    bool
}

func (r *Rcv) change() int { r.b = true; return 0 }

func (r *Rcv) m2() string { return show(r.left || r.b, r.change()) }

func d1() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	r := a() + b()
	return log + r
}

func d2() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	a := func() string {
		log += "a "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "A"
	}
	r := a() + <-ch
	return log + r
}

func d3() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	a := func() string {
		log += "a "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "A"
	}
	r := <-ch + a()
	return log + r
}

func d4() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	c := func() string { log += "c "; return "C" }
	r := a() + b() + c()
	return log + r
}

func d4p() string {
	log := ""
	a := func() int { log += "a "; return 10 }
	b := func() int { log += "b "; return 7 }
	c := func() int { log += "c "; return 2 }
	r := a() - (b() - c())
	return log + itoa(r)
}

func d5() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "A" }
	if a() == b() {
		return log + "eq"
	}
	return log + "ne"
}

func d5r() string {
	log := ""
	ch := make(chan int, 2)
	ch <- 5
	a := func() int {
		log += "a "
		select {
		case <-ch:
			ch <- 1
		default:
		}
		return 3
	}
	if a() < <-ch {
		return log + "lt"
	}
	return log + "ge"
}

func d7() string {
	p := &S{}
	b := false
	change := func() int { b = true; return 0 }
	return show(p.f || b, change())
}

func d8() string {
	s := S{}
	b := false
	change := func() int { b = true; return 0 }
	return show(s.inner.f || b, change())
}

func d9() string {
	var i any = false
	b := false
	change := func() int { b = true; return 0 }
	return show(i.(bool) || b, change())
}

func d11() string {
	m := map[string]bool{"k": false}
	b := false
	change := func() int { b = true; return 0 }
	return show(m["k"] || b, change())
}

func d12() string {
	x := X{v: false}
	b := false
	change := func() int { b = true; return 0 }
	return show(x.M() || b, change())
}

func d13() string {
	ch := make(chan bool, 1)
	ch <- false
	b := false
	change := func() int { b = true; return 0 }
	return show(<-ch || b, change())
}

func d17() string {
	xs := []bool{false}
	b := false
	change := func() int { b = true; return 0 }
	return show(xs[0] || b, change())
}

func d18() string {
	str := "zzz"
	b := false
	change := func() int { b = true; return 0 }
	return show(str[0] == 'a' || b, change())
}

func d19() string {
	xs := []int{}
	b := false
	change := func() int { b = true; return 0 }
	return show(len(xs) > 0 || b, change())
}

func d20() string {
	b := false
	change := func() int { b = true; return 0 }
	return show(gp.f || b, change())
}

func d21() string { return gen(0) }

func d23() string {
	b1, b2, b3 := true, false, false
	change := func() int { b3 = true; return 0 }
	return show(b1 && b2 || b3, change())
}

func d24() string {
	f1 := func() bool { return false }
	b := false
	change := func() int { b = true; return 0 }
	return show(f1() || b, change())
}

func d25() string {
	b := false
	r := Rr{&b}
	return show(left || b, r.Set())
}

func d26() string {
	ch := make(chan int, 1)
	ch <- 7
	return show(left || len(ch) > 0, <-ch)
}

func d27n() string {
	s := S2{}
	change := func() int { s.b = true; return 0 }
	return show(left || s.b, change())
}

func d28() string {
	s := make([]int, 0, 2)
	grow := func() int { s = make([]int, 0, 16); return 0 }
	n := cap(s) + grow()
	return itoa(n)
}

func d29() string {
	s := []int{1}
	grow := func() int { s = []int{1, 2, 3, 4, 5}; return 0 }
	n := max(len(s), 1) + grow()
	return itoa(n)
}

func d30s() string { _, s := d30(); return s }

func d32() string {
	fb := func() bool { return true }
	b := false
	change := func() int { b = true; return 0 }
	return show(fb() && b, change())
}

func m2() string {
	r := &Rcv{}
	return r.m2()
}

func d11i() string {
	m := map[string]any{"k": false}
	b := false
	change := func() int { b = true; return 0 }
	return show(m["k"].(bool) || b, change())
}

func main() {
	d1()
	d2()
	d3()
	d4()
	d4p()
	d5()
	d5r()
	d7()
	d8()
	d9()
	d11()
	d12()
	d13()
	d17()
	d18()
	d19()
	d20()
	d21()
	d23()
	d24()
	d25()
	d26()
	d27n()
	d28()
	d29()
	d30s()
	d32()
	m2()
	d11i()
}
