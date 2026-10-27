// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// switch tags and case expressions — the tag once, the case expressions in order up to the
// match and never past it, never across a fallthrough, a case list, a default in first
// position, a tagless switch, a type switch whose guard is a call, a receive in a case
// expression and in the tag, in a closure and in a generic function.

package main

var cnt int

func f() int { cnt++; return 2 }
func g() int { cnt++; return 2 }
func h() int { cnt++; return 3 }
func k() int { cnt++; return 9 }

type I interface{ M() int }
type T struct{}

func (T) M() int { return 1 }

func fi() I { cnt++; return T{} }

func tagCasesFirst() int {
	cnt = 0
	r := 0
	switch f() {
	case g():
		r = 1
	case h():
		r = 2
	default:
		r = 3
	}
	return cnt*100 + r
}

func tagCasesSecond() int {
	cnt = 0
	r := 0
	switch h() {
	case g():
		r = 1
	case h():
		r = 2
	default:
		r = 3
	}
	return cnt*100 + r
}

func tagCasesNone() int {
	cnt = 0
	r := 0
	switch k() {
	case g():
		r = 1
	case h():
		r = 2
	default:
		r = 3
	}
	return cnt*100 + r
}

func taglessCalls() int {
	cnt = 0
	r := 0
	switch {
	case f() > 5:
		r = 1
	case g() > 1:
		r = 2
	case h() > 1:
		r = 3
	}
	return cnt*100 + r
}

func typeSwitchGuardCall() int {
	cnt = 0
	r := 0
	switch v := fi().(type) {
	case T:
		r = v.M()
	default:
		r = 9
	}
	return cnt*100 + r
}

func caseListCalls() int {
	cnt = 0
	r := 0
	switch f() {
	case k(), g(), h():
		r = 1
	default:
		r = 3
	}
	return cnt*100 + r
}

func fallthroughSkipsCase() int {
	cnt = 0
	r := 0
	switch f() {
	case g():
		r += 1
		fallthrough
	case h():
		r += 10
	case k():
		r += 100
	}
	return cnt*100 + r
}

func defaultFirst() int {
	cnt = 0
	r := 0
	switch f() {
	default:
		r = 3
	case g():
		r = 1
	}
	return cnt*100 + r
}

func closureSwitch() int {
	cnt = 0
	r := 0
	inner := func() {
		switch f() {
		case k():
			r = 1
		case g():
			r = 2
		case h():
			r = 3
		}
	}
	inner()
	return cnt*100 + r
}

func swGeneric[T comparable](tag func() T, a, b func() T) int {
	switch tag() {
	case a():
		return 1
	case b():
		return 2
	}
	return 3
}

func genericSwitch() int {
	cnt = 0
	r := swGeneric(f, k, g)
	s := swGeneric(func() string { cnt++; return "x" }, func() string { cnt++; return "x" }, func() string { cnt++; return "y" })
	return cnt*100 + r*10 + s
}

func recvInCase() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	r := 0
	switch {
	case <-ch == 5:
		r = 1
	case <-ch == 2:
		r = 2
	case <-ch == 3:
		r = 3
	}
	return len(ch)*100 + r
}

func recvInTagSwitch() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	r := 0
	switch <-ch {
	case <-ch:
		r = 1
	case 1:
		r = 2
	}
	return len(ch)*100 + r
}

func main() {
	tagCasesFirst()
	tagCasesSecond()
	tagCasesNone()
	taglessCalls()
	typeSwitchGuardCall()
	caseListCalls()
	fallthroughSkipsCase()
	defaultFirst()
	closureSwitch()
	genericSwitch()
	recvInCase()
	recvInTagSwitch()
}
