package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H9: cmp.Compare / Less / Or at the kinds the cmp-compare rows omit (ints of every width, uints, strings, named,
// Or over zero / non-zero values of several comparable kinds and no arguments).
import (
	"cmp"
	"strconv"
)

type named int8
type ns string
type pt struct{ x, y int }

func i(v int) string  { return strconv.Itoa(v) }
func b(v bool) string { return strconv.FormatBool(v) }

func compareKinds() string {
	return i(cmp.Compare(int8(-128), int8(127))) + i(cmp.Compare(uint64(18446744073709551615), uint64(0))) + i(cmp.Compare(uint8(1), uint8(1))) + i(cmp.Compare("a", "ab")) + i(cmp.Compare("b", "ab")) + i(cmp.Compare("", "")) + i(cmp.Compare(named(-1), named(1))) + i(cmp.Compare(ns("\xff"), ns("a"))) + i(cmp.Compare(uintptr(2), uintptr(1))) + i(cmp.Compare(int64(-9223372036854775808), int64(9223372036854775807)))
}
func lessKinds() string {
	return b(cmp.Less(int16(-1), int16(0))) + b(cmp.Less(uint32(1), uint32(0))) + b(cmp.Less("a", "a")) + b(cmp.Less(ns("a"), ns("b"))) + b(cmp.Less(named(5), named(5)))
}
func orKinds() string {
	return i(cmp.Or(0, 0, 3, 4)) + i(cmp.Or(0, 0)) + cmp.Or("", "", "x") + cmp.Or("", "") + b(cmp.Or(false, true)) + b(cmp.Or(false)) + "|" + i(cmp.Or(pt{}, pt{1, 2}).x) + i(cmp.Or(pt{0, 1}, pt{1, 2}).y) + "|" + i(cmp.Or[int]()) + cmp.Or[string]() + "|" + string(cmp.Or(ns(""), ns("n")))
}

func main() {
	compareKinds()
	lessKinds()
	orKinds()
}
