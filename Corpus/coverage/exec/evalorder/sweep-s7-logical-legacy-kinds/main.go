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
// BUG-277 (found by this sweep, born RED/differential): BUG-113's wrong order — a binary logical
// operation evaluated AFTER a lexically later call that mutates its right operand — at the
// operand kinds the unseq grammar still declines by name (the census reasons): an array
// element (`index of a non-slice base`), an array through a pointer, a field of an array
// element, a conversion of a defined type (`conversion operand type outside the grammar`), a
// promoted field (`promoted field selector (embedded hops)`), an interface comparison
// (`interface comparison (may panic; outside the pilot)`), a type-parameter comparison
// (`binary operand type outside the pilot grammar`). The declined sweep takes the legacy ANF
// hoist, which runs the later call first: the machine answers true, gc false.

type E struct{ Base }

type Base struct{ promoted bool }

var left = false

func show(x bool, n int) string {
	if x {
		return "true " + itoa(n)
	}
	return "false " + itoa(n)
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

type PkgBool bool

func genCmp[T comparable](x, y T) string {
	b := false
	change := func() int { b = true; return 0 }
	return show(x == y || b, change())
}

func d10() string {
	arr := [2]bool{false, false}
	b := false
	change := func() int { b = true; return 0 }
	return show(arr[0] || b, change())
}

func d10p() string {
	arr := [2]bool{false, false}
	p := &arr
	b := false
	change := func() int { b = true; return 0 }
	return show(p[0] || b, change())
}

func d10f() string {
	arr := [1]S2{}
	b := false
	change := func() int { b = true; return 0 }
	return show(arr[0].b || b, change())
}

func d14() string {
	type MyBool bool
	x := MyBool(false)
	b := false
	change := func() int { b = true; return 0 }
	return show(bool(x) || b, change())
}

func d14p() string {
	x := PkgBool(false)
	b := false
	change := func() int { b = true; return 0 }
	return show(bool(x) || b, change())
}

func d14i() string {
	type MyInt int
	x := MyInt(0)
	b := false
	change := func() int { b = true; return 0 }
	return show(int(x) > 0 || b, change())
}

func d15() string {
	e := E{}
	b := false
	change := func() int { b = true; return 0 }
	return show(e.promoted || b, change())
}

func d16() string {
	var ifc any
	b := false
	change := func() int { b = true; return 0 }
	return show(ifc != nil || b, change())
}

func d16p() string {
	var p *S2
	var ifc any = p
	b := false
	change := func() int { b = true; return 0 }
	return show(ifc == nil || b, change())
}

func d21c() string { return genCmp(1, 2) }

func main() {
	d10()
	d10p()
	d10f()
	d14()
	d14p()
	d14i()
	d15()
	d16()
	d16p()
	d21c()
}
