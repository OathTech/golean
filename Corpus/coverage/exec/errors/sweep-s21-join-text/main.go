package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group G2: errors.joinError.Error through the errors/join.go:58 overlay (`unsafe.String(&b[0], len(b))` -> `string(b)`):
// the joined text with multibyte / NUL / embedded newlines, nested joins, through Errorf and Sprint, a panicking element.
import (
	"errors"
	"fmt"
	"strconv"
)

type boom struct{}

func (boom) Error() string { panic("elem boom") }

type withUnwrap struct{ in error }

func (w withUnwrap) Error() string { return "wu" }
func (w withUnwrap) Unwrap() error { return w.in }

func multibyteAndNul() (string, int) {
	j := errors.Join(errors.New("\u00e9\x00"), errors.New("\u65e5"), errors.New(""))
	return j.Error(), len(j.Error())
}
func newlinesInside() (string, int) {
	j := errors.Join(errors.New("a\nb"), errors.New("\n"), errors.New("c"))
	return j.Error(), len(j.Error())
}
func threeAndNested() string {
	in := errors.Join(errors.New("b"), errors.New("c"))
	j := errors.Join(errors.New("a"), in, nil, errors.New("d"))
	us := j.(interface{ Unwrap() []error }).Unwrap()
	return j.Error() + "|" + strconv.Itoa(len(us)) + "|" + strconv.FormatBool(us[1] == in)
}
func throughErrorfAndSprint() string {
	j := errors.Join(errors.New("x"), errors.New("y"))
	return fmt.Errorf("%v", j).Error() + "#" + fmt.Sprint(j, 1) + "#" + fmt.Sprintf("%s|%q", j, j)
}
func elemPanics() (out string) {
	defer func() {
		if r := recover(); r != nil {
			out = "R:" + r.(string)
		}
	}()
	j := errors.Join(errors.New("a"), boom{})
	return j.Error()
}
func singleAndUnwrapOfJoin() (bool, string, bool, bool) {
	e := errors.New("only")
	j1 := errors.Join(e)
	j2 := errors.Join(e, e)
	return j1.Error() == e.Error(), j2.Error(), errors.Unwrap(j2) == nil, errors.Unwrap(withUnwrap{j2}) == j2
}

func main() {
	multibyteAndNul()
	newlinesInside()
	threeAndNested()
	throughErrorfAndSprint()
	elemPanics()
	singleAndUnwrapOfJoin()
}
