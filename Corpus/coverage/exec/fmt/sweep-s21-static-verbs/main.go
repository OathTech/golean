package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group A: the STATIC desugar's verb × static-kind matrix (fmtdesugar.go fmtVerbArg / parseFmtFormat).
import "fmt"

type k32 int32
type ku8 uint8
type ne int

func (ne) Error() string { return "E" }

type ns string
type nb bool
type both struct{ n int }

func (b both) Error() string  { return "err" }
func (b both) String() string { return "str" }

type hS struct{ n int }

func (p *hS) String() string {
	if p == nil {
		return "HNIL"
	}
	return "h"
}

func dKinds() string {
	return fmt.Sprintf("%d|%d|%d|%d|%d|%d|%d|%d|%d|%d|%d|%d|%d", int8(-128), int16(-32768), int32(-2147483648), int64(-9223372036854775808),
		int(9223372036854775807), uint8(255), uint16(65535), uint32(4294967295), uint64(18446744073709551615), uint(1), uintptr(12345), k32(-7), ku8(200))
}
func dNamedError() string { return fmt.Sprintf("%d", ne(5)) }
func xUnsignedKinds() string {
	return fmt.Sprintf("%x|%x|%x|%x|%x|%x|%x|%x", uint8(0), uint8(255), uint16(0xabcd), uint32(0xdeadbeef), uint64(18446744073709551615), uint(1), uintptr(0x10), ku8(0xff))
}
func vKindsAll() string {
	return fmt.Sprintf("%v|%v|%v|%v|%v|%v|%v|%v|%v|%v|%v|%v|%v|%v", int8(-1), int16(-2), int32(-3), int64(-4), uint8(1), uint16(2), uint32(3), uintptr(4), k32(-9), ku8(9), true, false, "s", ns("n"))
}
func vNamedBool() string             { return fmt.Sprintf("%v|%+v", nb(true), nb(false)) }
func dGenericBody() string           { return showD(5) + "|" + showD(int8(-3)) + "|" + showV("s") }
func showD[T int | int8](x T) string { return fmt.Sprintf("%d|%v", x, x) }
func showV[T any](x T) string        { return fmt.Sprintf("%v", x) }
func plusVScalars() string {
	return fmt.Sprintf("%+v|%+v|%+v|%+v|%+v|%+v", 5, -5, uint8(7), true, "s", k32(3))
}
func vErrorAndStringer() string { b := both{1}; return fmt.Sprintf("%v|%s|%x|%q", b, b, b, b) }
func vNilPtrHandled() string    { var p *hS; return fmt.Sprintf("%v|%s|%+v", p, p, p) }
func tNamedBool() string        { return fmt.Sprintf("%t|%t", nb(true), nb(false)) }
func widthKinds() string {
	return fmt.Sprintf("[%5d][%5d][%5d][%5d][%1d][%20d][%5d]", int8(-42), uint8(7), 123456, k32(-3), 12345, -1, uint64(18446744073709551615))
}
func constExprFormat() string {
	const f = "a=%d"
	return fmt.Sprintf(f, 1) + "|" + fmt.Sprintf("b="+"%d", 2) + "|" + fmt.Sprintf(f+"/%s", 3, "c")
}
func literalBytes() (string, int) { s := fmt.Sprintf("x\x00y\xffz%%é"); return s, len(s) }
func percentAdjacent() string     { return fmt.Sprintf("%%%d%%|%%%%|%d%%%d", 5, 1, 2) }
func stringerUnderEveryVerb() string {
	var p = &hS{1}
	return fmt.Sprintf("%v|%s|%x|%q|%+v", p, p, p, p, p)
}

func main() {
	dKinds()
	dNamedError()
	xUnsignedKinds()
	vKindsAll()
	plusVScalars()
	vErrorAndStringer()
	vNilPtrHandled()
	tNamedBool()
	vNamedBool()
	dGenericBody()
	widthKinds()
	constExprFormat()
	literalBytes()
	percentAdjacent()
	stringerUnderEveryVerb()
}
