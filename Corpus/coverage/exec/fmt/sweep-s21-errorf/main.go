package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group C: fmt.Errorf (the Errorf arm of emitFmtCall over goleanShimErrorsNew): texts, identity, Unwrap, AsType, the rendered
// forms, and the dynamic type's name through a failed INTERFACE assertion (BUG-236's second route, born red).
import (
	"errors"
	"fmt"
	"strconv"
)

type wrap struct{ inner error }

func (w wrap) Error() string { return "w(" + w.inner.Error() + ")" }
func (w wrap) Unwrap() error { return w.inner }

func verbs() string {
	return fmt.Errorf("%d|%x|%s|%v|%+v|%q|%t|%%|%5d", -1, uint8(255), "s", true, 2, "q\"", false, 42).Error()
}
func noVerbs() (string, string, int) {
	return fmt.Errorf("plain").Error(), fmt.Errorf("").Error(), len(fmt.Errorf("").Error())
}
func identityRoutes() (int, int, bool, bool) {
	a, b := fmt.Errorf("t%d", 1), fmt.Errorf("t%d", 1)
	m := map[error]int{a: 1, b: 2}
	s := []error{a, b, a}
	n := 0
	for _, e := range s {
		if e == a {
			n++
		}
	}
	return len(m), n, a != nil, a == b
}
func unwrap() (bool, bool, string) {
	e := fmt.Errorf("x%d", 1)
	w := wrap{e}
	return errors.Unwrap(e) == nil, errors.Unwrap(w) == e, errors.Unwrap(w).Error()
}
func asType() (bool, bool, string, string) {
	_, perr := strconv.ParseInt("zz", 10, 64)
	ne, ok := errors.AsType[*strconv.NumError](perr)
	_, ok2 := errors.AsType[*strconv.NumError](fmt.Errorf("x"))
	w := wrap{perr}
	ne3, ok3 := errors.AsType[*strconv.NumError](w)
	if !ok || !ok3 {
		return ok, ok2, "", ""
	}
	return ok, ok2, ne.Func + "/" + ne.Num, ne3.Num
}
func rendered() string {
	e := fmt.Errorf("r%d", 7)
	return fmt.Sprintf("%v|%s|%x|%q", e, e, e, e) + "#" + fmt.Sprint(e, 1) + "#" + fmt.Sprintln(e)
}
func inClosureAndMethod() string {
	g := func(n int) error { return fmt.Errorf("c%d", n) }
	return g(1).Error() + "|" + (&wrap{g(2)}).Error()
}
func assertIface() string {
	e := fmt.Errorf("x%d", 1)
	var a any = e
	s := a.(fmt.Stringer)
	return s.String()
}

func main() {
	verbs()
	noVerbs()
	identityRoutes()
	unwrap()
	asType()
	rendered()
	inClosureAndMethod()
	assertIface()
}
