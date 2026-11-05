package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H6: FormatBool, the Append* family into nil and a prefix, Itoa vs FormatInt.
import "strconv"

func formatBool() string { return strconv.FormatBool(true) + strconv.FormatBool(false) }
func appendFamily() string {
	a := strconv.AppendInt(nil, -255, 16)
	b := strconv.AppendInt([]byte("p:"), 255, 2)
	c := strconv.AppendUint([]byte("u:"), 18446744073709551615, 36)
	d := strconv.AppendBool([]byte("b:"), true)
	e := strconv.AppendUint(nil, 0, 10)
	f := strconv.AppendInt([]byte{}, 7, 36)
	return string(a) + "|" + string(b) + "|" + string(c) + "|" + string(d) + "|" + string(e) + "|" + string(f) + "|" + strconv.Itoa(len(a)+len(b)+len(c)+len(d)+len(e)+len(f))
}
func itoaVsFormatInt() (bool, bool, bool) {
	return strconv.Itoa(-7) == strconv.FormatInt(-7, 10), strconv.FormatInt(255, 16) == "ff", strconv.FormatUint(255, 2) == "11111111"
}
func appendAliasing() string {
	buf := make([]byte, 0, 16)
	a := strconv.AppendInt(buf, 1, 10)
	b := strconv.AppendInt(buf, 2, 10)
	return string(a) + string(b) + "|" + string(buf[:1])
}

func main() {
	formatBool()
	appendFamily()
	itoaVsFormatInt()
	appendAliasing()
}
