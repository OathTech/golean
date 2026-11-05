package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group A (A4/A9): the Stringer / error RENDER helpers (goleanShimFmtRender*, FmtError*, PanicValue, StringVerb).
import (
	"errors"
	"fmt"
)

type errPanicsError struct{}

func (errPanicsError) Error() string { panic(errors.New("inner")) }

type strPanicsErrorf struct{}

func (strPanicsErrorf) String() string { panic(fmt.Errorf("e%d", 1)) }

type outer struct{ in inner }
type inner int

func (i inner) String() string { return fmt.Sprintf("<%d>", int(i)) }
func (o outer) String() string { return fmt.Sprintf("O%v", o.in) }

type quoty struct{}

func (quoty) String() string { return "a\"b\n\t\\c" }

type multi struct{}

func (multi) Error() string { return "é日" }

type valErr struct{ n int }

func (v valErr) Error() string { return "VE" }

func errorPanicErrorPayload() string     { return fmt.Sprintf("[%v]", errPanicsError{}) }
func stringerPanicErrorfPayload() string { return fmt.Sprintf("[%s]", strPanicsErrorf{}) }
func nestedStringer() string             { return fmt.Sprintf("%v|%s", outer{inner(3)}, outer{inner(-1)}) }
func qStringerEscapes() string           { return fmt.Sprintf("%q", quoty{}) }
func xErrorMultibyte() string            { return fmt.Sprintf("%x|%s", multi{}, multi{}) }
func valueErrorAtErrorIface() string {
	var e error = valErr{1}
	return fmt.Sprintf("%v|%s|%x|%q", e, e, e, e)
}
func errorsNewAtEveryVerb() string {
	e := errors.New("n\"x")
	return fmt.Sprintf("%v|%s|%x|%q", e, e, e, e)
}

type hE struct{}

func (p *hE) Error() string {
	if p == nil {
		return "ENIL"
	}
	return "e"
}

func typedNilErrorHandled() string {
	var e error = (*hE)(nil)
	return fmt.Sprintf("%v|%s|%x|%q", e, e, e, e)
}
func panicRenderDropsWidthFlag() string {
	// the PANIC render uses the verb char only: %+v renders as %!v(...)
	return fmt.Sprintf("%+v", strPanicsErrorf{})
}

func main() {
	errorPanicErrorPayload()
	stringerPanicErrorfPayload()
	nestedStringer()
	qStringerEscapes()
	xErrorMultibyte()
	valueErrorAtErrorIface()
	errorsNewAtEveryVerb()
	panicRenderDropsWidthFlag()
	typedNilErrorHandled()
}
