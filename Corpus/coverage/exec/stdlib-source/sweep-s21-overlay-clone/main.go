package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group G1: the internal/stringslite.Clone overlay (strings.go:149, `unsafe.String(&b[0], len(b))` -> `string(b)`) through
// strings.Clone and every strconv error constructor that reaches it (syntaxError / rangeError / baseError / bitSizeError).
import (
	"strconv"
	"strings"
)

func stringsClone() (string, int, string, int, bool, bool) {
	a := strings.Clone("")
	b := strings.Clone("h\u00e9llo\x00!")
	big := strings.Clone(strings.Repeat("ab", 8192))
	sub := strings.Clone("xh\u00e9llo"[1:4])
	return b, len(b), sub, len(big), big == strings.Repeat("ab", 8192), a == "" && len(a) == 0
}

type sbb struct {
	s    string
	base int
	bits int
}

func parseIntErrors() string {
	out := ""
	for _, c := range []sbb{{"", 10, 64}, {"x", 10, 64}, {"-", 10, 64}, {"+", 10, 64}, {"1_0", 10, 64}, {"0x1f", 16, 64}, {"128", 10, 8}, {"-129", 10, 8}, {"65536", 10, 16}, {"2147483648", 10, 32}, {"-2147483649", 10, 32}, {"9223372036854775808", 10, 64}, {"-9223372036854775809", 10, 64}, {"7", 1, 64}, {"7", 37, 64}, {"7", 10, 65}, {"7", 10, -1}, {"1__0", 0, 64}, {"_1", 0, 64}, {"0x", 0, 64}, {"+-1", 10, 64}, {"\u00e9", 10, 64}, {"a\"b", 10, 64}} {
		v, err := strconv.ParseInt(c.s, c.base, c.bits)
		ne, ok := err.(*strconv.NumError)
		out += strconv.FormatInt(v, 10) + ":" + err.Error() + ":"
		if ok {
			out += ne.Func + "/" + strconv.FormatBool(ne.Num == c.s) + "/" + strconv.FormatBool(ne.Err == strconv.ErrSyntax) + "/" + strconv.FormatBool(ne.Err == strconv.ErrRange) + "/" + ne.Err.Error()
		}
		out += ";"
	}
	return out
}
func atoiErrors() string {
	out := ""
	for _, s := range []string{"", "x", "99999999999999999999", "-99999999999999999999", "+", "-", " 7", "7 ", "1e3", "0x10", "٣"} {
		v, err := strconv.Atoi(s)
		ne, _ := err.(*strconv.NumError)
		out += strconv.Itoa(v) + ":" + err.Error() + ":" + ne.Func + "/" + strconv.FormatBool(ne.Num == s) + "/" + strconv.FormatBool(errIs(ne.Err)) + ";"
	}
	return out
}
func errIs(e error) bool { return e == strconv.ErrSyntax || e == strconv.ErrRange }
func parseBoolErrors() string {
	out := ""
	for _, s := range []string{"yes", "", "TrUe", "2", "t ", "\u00e9"} {
		v, err := strconv.ParseBool(s)
		ne, ok := err.(*strconv.NumError)
		out += strconv.FormatBool(v) + ":" + err.Error() + ":" + strconv.FormatBool(ok && ne.Num == s && ne.Err == strconv.ErrSyntax) + ";"
	}
	return out
}
func parseUintBaseBitErrors() string {
	out := ""
	for _, c := range []sbb{{"7", 1, 64}, {"7", 37, 64}, {"7", 10, 65}, {"7", 10, -1}, {"-1", 10, 64}, {"256", 10, 8}, {"4294967296", 10, 32}} {
		v, err := strconv.ParseUint(c.s, c.base, c.bits)
		out += strconv.FormatUint(v, 10) + ":" + err.Error() + ";"
	}
	return out
}

func main() {
	stringsClone()
	parseIntErrors()
	atoiErrors()
	parseBoolErrors()
	parseUintBaseBitErrors()
}
