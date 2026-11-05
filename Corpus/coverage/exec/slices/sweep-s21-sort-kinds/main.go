package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group K2: the slices.Sort INTERCEPT (the sortSlice op at integer kinds) at the element kinds the slices-sort-* rows omit,
// with IsSorted and BinarySearch over the op's result.
import (
	"slices"
	"strconv"
)

func render[E int8 | uint8 | int16 | uint16 | int32 | uint32](s []E) string {
	out := ""
	for i, v := range s {
		if i > 0 {
			out += ","
		}
		out += strconv.FormatInt(int64(v), 10)
	}
	return out
}
func sortInt8() (string, bool) {
	s := []int8{3, -128, 127, 0, -1, 3}
	slices.Sort(s)
	return render(s), slices.IsSorted(s)
}
func sortUint8() (string, bool) {
	s := []uint8{255, 0, 128, 1, 255}
	slices.Sort(s)
	return render(s), slices.IsSorted(s)
}
func sortInt16() (string, bool) {
	s := []int16{-32768, 32767, 0, 5, -5}
	slices.Sort(s)
	return render(s), slices.IsSorted(s)
}
func sortUint16() (string, bool) {
	s := []uint16{65535, 1, 0, 32768}
	slices.Sort(s)
	return render(s), slices.IsSorted(s)
}
func sortInt32() (string, int, bool) {
	s := []int32{-2147483648, 2147483647, 7, -7, 0}
	slices.Sort(s)
	i, found := slices.BinarySearch(s, 7)
	return render(s), i, found
}
func sortUint32() (string, int, bool) {
	s := []uint32{4294967295, 2147483648, 0, 9}
	slices.Sort(s)
	i, found := slices.BinarySearch(s, 10)
	return render(s), i, found
}
func sortRuneAndByte() (string, string) {
	r := []rune("h\u00e9z\u0000a")
	slices.Sort(r)
	b := []byte("zebra\xff\x00")
	slices.Sort(b)
	return string(r), string(b)
}

func main() {
	sortInt8()
	sortUint8()
	sortInt16()
	sortUint16()
	sortInt32()
	sortUint32()
	sortRuneAndByte()
}
