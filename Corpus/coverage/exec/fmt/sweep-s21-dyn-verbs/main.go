package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group B: the DYNAMIC shim (goleanShimFmtDynVerb / DynInt / DynUint / SprintfDyn) over every verb × dynamic kind it admits.
import (
	"errors"
	"fmt"
)

func f(format string, v ...any) string { return fmt.Sprintf(format, v...) }

type vS struct{ n int }

func (v vS) String() string { return "vS" }

type pS struct{ n int }

func (p *pS) String() string { return "pS" }

type vE struct{}

func (vE) Error() string { return "vE" }

type pE struct{}

func (*pE) Error() string { return "pE" }

type boom struct{}

func (boom) Error() string { panic("boom") }

func dKinds() string {
	return f("%d|%d|%d|%d|%d|%d|%d|%d|%v|%v|%v|%v", int8(-128), int16(-32768), int32(-5), int64(-6), uint8(255), uint16(65535), uint32(7), uint(8), int8(1), uint16(2), int32(3), uint32(4))
}
func xKinds() string {
	return f("%x|%x|%x|%x|%x|%x|%x", uint8(255), uint16(0xabcd), uint32(0xdeadbeef), uint64(18446744073709551615), uint(1), 255, int8(0))
}
func xString() string { return f("%x|%x|%x", "hi", "", "é") }
func bytesVerbs() string {
	var nb []byte
	return f("%s|%v|%d|%q", []byte("ab"), []byte("ab"), []byte("ab"), []byte("a\"b")) + "#" + f("%s|%v|%d|%q", nb, nb, nb, nb)
}
func sliceKinds() string {
	var ni []int
	return f("%v|%v|%v|%d|%s|%v", []uint64{}, ni, []string{"a", "b c"}, []int{-1, 2}, []string{"x"}, []uint64{18446744073709551615})
}
func boolVerbs() string { return f("%v|%t|%v|%t", true, true, false, false) }
func nilSpread() string { return f("%v|%v", nil, nil) }
func errorKinds() string {
	return f("%s|%v|%x|%q", errors.New("e"), errors.New("e"), errors.New("e"), errors.New("e")) + "#" +
		f("%s|%v|%x|%q", fmt.Errorf("f%d", 1), fmt.Errorf("f%d", 1), fmt.Errorf("f%d", 1), fmt.Errorf("f%d", 1)) + "#" +
		f("%s|%v|%x|%q", vE{}, vE{}, vE{}, vE{}) + "#" + f("%s|%v|%x|%q", &pE{}, &pE{}, &pE{}, &pE{})
}
func stringerKinds() string {
	return f("%s|%v|%x|%q", vS{}, vS{}, vS{}, vS{}) + "#" + f("%s|%v|%x|%q", &pS{}, &pS{}, &pS{}, &pS{})
}
func errorPanic() string     { return f("[%v]|[%s]", boom{}, boom{}) }
func dynPlusV() string       { return f("%+v|%+v|%+v", 5, vS{}, "s") }
func percentRuntime() string { return f("%%|%d%%|%%%%", 5) }
func emptyFormat() string    { return f("") + "|" + f("abc") + "|" + f("é%dé", 1) }

type hS struct{ n int }

func (p *hS) String() string {
	if p == nil {
		return "HNIL"
	}
	return "h"
}

type hE struct{}

func (p *hE) Error() string {
	if p == nil {
		return "ENIL"
	}
	return "e"
}

func nilPtrHandled() string {
	var p *hS
	var q *hE
	return fmt.Sprint(p, q) + "|" + f("%v|%s|%x|%q", p, p, p, p) + "|" + f("%v|%s", q, q)
}
func namedStringFormat() string {
	type fs string
	h := func(fo fs, v ...any) string { return fmt.Sprintf(string(fo), v...) }
	k := func(fo fs, v ...any) string { return fmt.Sprintf(string(fo), v...) }
	return h("%d|%s", 1, "a") + k("", []any{}...)
}
func errorBeforeStringer() string {
	type bothT struct{}
	return f("%v", vE{}) // an error whose dynamic type has no String: Error() wins over nothing
}

func main() {
	dKinds()
	xKinds()
	xString()
	bytesVerbs()
	sliceKinds()
	boolVerbs()
	nilSpread()
	errorKinds()
	stringerKinds()
	errorPanic()
	dynPlusV()
	percentRuntime()
	emptyFormat()
	errorBeforeStringer()
	namedStringFormat()
	nilPtrHandled()
}
