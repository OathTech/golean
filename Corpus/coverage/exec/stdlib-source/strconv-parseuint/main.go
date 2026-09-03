package main

// strconv.ParseUint — the RETAINED shim with the REAL *strconv.NumError
// (stdlib source-through slice 1, 2026-09-03; stdlibshim.go's ParseUint
// block has the argument). The digit loop is the shim's; the error VALUE
// is the library's own `&strconv.NumError{Func, Num, Err}` with the
// library's ErrSyntax/ErrRange sentinels, rendered by the library's own
// NumError.Error and Quote (source-through). godoc:strconv.ParseUint@go1.26.5
// / godoc:strconv.ParseInt@go1.26.5: "The errors that ParseInt returns
// have concrete type *NumError and include err.Num = s. If s is empty or
// contains invalid digits, err.Err = ErrSyntax and the returned value is
// 0; if the value corresponding to s cannot be represented by a signed
// integer of the given size, err.Err = ErrRange and the returned value is
// the maximum magnitude integer of the appropriate bitSize and sign."
// Rows observe exactly those clauses: the dynamic TYPE (a type assertion
// to *strconv.NumError — the shape the pre-slice shim answered FALSE to),
// the Func/Num fields, the sentinel IDENTITY through Unwrap, and the
// rendered text for ASCII and non-ASCII inputs (Quote's escaping).
// Non-ASCII text is written as \u escapes.

import "strconv"

func parseUintNumErrorType() (bool, string, string, bool, bool) {
	_, err := strconv.ParseUint("12x", 10, 64)
	ne, ok := err.(*strconv.NumError)
	if !ok {
		return false, "", "", false, false
	}
	return true, ne.Func, ne.Num, ne.Err == strconv.ErrSyntax, ne.Unwrap() == strconv.ErrSyntax
}

func parseUintRangeSentinel() (uint64, bool, bool, string) {
	v, err := strconv.ParseUint("18446744073709551616", 10, 64)
	ne, ok := err.(*strconv.NumError)
	return v, ok, ok && ne.Err == strconv.ErrRange, err.Error()
}

func parseUintErrorTexts() string {
	out := ""
	for _, s := range []string{"", "-1", "1_0", "0x1f", "zz", " 7", "18446744073709551616"} {
		_, err := strconv.ParseUint(s, 10, 64)
		out += err.Error() + ";"
	}
	return out
}

// Quote's escaping in the rendered error: a quote, a backslash, a
// control byte, a non-ASCII rune, invalid UTF-8.
func parseUintErrorQuoting() string {
	out := ""
	for _, s := range []string{"a\"b", "a\\b", "a\tb", "é", "\xff", "日"} {
		_, err := strconv.ParseUint(s, 16, 64)
		out += err.Error() + ";"
	}
	return out
}

func parseUintHappyBases() (uint64, uint64, uint64, uint64, bool) {
	a, e1 := strconv.ParseUint("zz", 36, 64)
	b, e2 := strconv.ParseUint("FF", 16, 8)
	c, e3 := strconv.ParseUint("777", 8, 16)
	d, e4 := strconv.ParseUint("1111", 2, 4)
	return a, b, c, d, e1 == nil && e2 == nil && e3 == nil && e4 == nil
}

func parseUintBitSizeSaturation() (uint64, uint64, uint64, uint64, string) {
	a, _ := strconv.ParseUint("256", 10, 8)
	b, _ := strconv.ParseUint("65536", 10, 16)
	c, _ := strconv.ParseUint("4294967296", 10, 32)
	d, e := strconv.ParseUint("16", 10, 4)
	return a, b, c, d, e.Error()
}

func main() {
	println(parseUintNumErrorType())
	println(parseUintRangeSentinel())
	println(parseUintErrorTexts())
	println(parseUintErrorQuoting())
	println(parseUintHappyBases())
	println(parseUintBitSizeSaturation())
}
