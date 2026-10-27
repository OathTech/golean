package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// TUPLES: a multi-value return into interface results, a forwarded return
// `return g()` whose typed-nil pointer component lands in an `error` result,
// tuple-forwarded CALLS `f(g())` beyond BUG-049's (int,string) matrix — a
// defined type, a typed-nil pointer and an interface component; two concrete
// values into two NARROWER interfaces; into a method; into an explicitly
// instantiated generic — and the two-call statement forms (the unseq
// lowering's atoms) where each operand owes a box: arguments, a slice literal,
// a struct literal, a send, a return.

type tDef int

type tPt struct{ X int }

type tErr struct{}

func (*tErr) Error() string { return "tErr" }

type tRW interface {
	R() int
	W() int
}

type tR interface{ R() int }

type tBoth struct{ n int }

func (b tBoth) R() int { return b.n }
func (b tBoth) W() int { return b.n * 2 }

type sPair struct {
	A any
	B any
}

type tRecv struct{}

func (tRecv) M2(a, b any) (any, any) { return a, b }

func g() int { return 1 }

func h() string { return "h" }

func twoInts() (int, string) { return 2, "two" }

func trip() (tDef, *tPt, error) { return 3, nil, &tErr{} }

func take3(a, b, c any) (any, any, any) { return a, b, c }

func take2(a, b any) (any, any) { return a, b }

func twoBoth() (tBoth, tBoth) { return tBoth{1}, tBoth{2} }

func takeRRW(r tR, rw tRW) int { return r.R() + rw.W() }

func pair[A, B any](a A, b B) (any, any) { return a, b }

func mkPair() (*tErr, int) { return nil, 1 }

func takeErr(e error, x any) (bool, any) { return e == nil, x }

func mkPair2() (int, *tErr) { return 1, nil }

func wrap() (any, error) { return mkPair2() }

func two() (any, any) { return 1, "a" }

func returnTuple() (any, any) { return two() }

func forwardDefinedPointerIface() int {
	a, b, c := take3(trip())
	r := 0
	if v, ok := a.(tDef); ok && v == 3 {
		r += 1
	}
	if v, ok := b.(*tPt); ok && v == nil {
		r += 10
	}
	if v, ok := c.(*tErr); ok && v != nil && v.Error() == "tErr" {
		r += 100
	}
	return r
}

func forwardNarrower() int { return takeRRW(twoBoth()) }

func forwardMethod() (any, any) { return tRecv{}.M2(twoInts()) }

func forwardGeneric() (any, any) { return pair[any, any](twoInts()) }

func forwardTypedNil() (bool, any) { return takeErr(mkPair()) }

func returnForwardTypedNil() (any, bool) {
	x, e := wrap()
	return x, e == nil
}

func unseqArgs() (any, any) { return take2(g(), h()) }

func unseqSliceLit() (any, any) {
	xs := []any{g(), h()}
	return xs[0], xs[1]
}

func unseqStructLit() sPair { return sPair{g(), h()} }

func unseqSend() any {
	ch := make(chan any, 1)
	ch <- g()
	return <-ch
}

func unseqReturn() (any, any) { return g(), h() }

func main() {
	returnTuple()
}
