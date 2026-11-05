package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H8: the slices editing family — Delete / DeleteFunc clear the tail, Clone, Compact, Grow / Clip (len only: the
// capacity is latitude), Reverse, Concat, Repeat, Insert where no spare capacity exists (the `overlaps` path is refused).
import (
	"slices"
	"strconv"
)

func r(s []int) string {
	out := ""
	for k, v := range s {
		if k > 0 {
			out += ","
		}
		out += strconv.Itoa(v)
	}
	return "[" + out + "]"
}
func deleteFuncClearedTail() string {
	backing := []int{1, 2, 3, 4, 5}
	s := backing[:5]
	s = slices.DeleteFunc(s, func(x int) bool { return x%2 == 0 })
	t := slices.Delete([]int{1, 2, 3, 4}, 1, 3)
	full := []int{9, 8, 7}
	u := slices.Delete(full, 0, 0)
	return r(s) + r(backing) + "|" + r(t) + "|" + r(u) + r(full)
}
func cloneNilEmpty() string {
	var ns []int
	c := slices.Clone(ns)
	e := slices.Clone([]int{})
	f := slices.Clone([]int{1, 2})
	f[0] = 9
	return strconv.FormatBool(c == nil) + strconv.FormatBool(e != nil) + strconv.Itoa(len(e)) + r(f)
}
func compactFamily() string {
	a := slices.Compact([]int{1, 1, 2, 2, 2, 3, 1, 1})
	b := slices.Compact([]int{})
	var ns []int
	c := slices.Compact(ns)
	d := slices.CompactFunc([]string{"a", "A", "b", "B", "b"}, func(x, y string) bool { return x == y || x == y+" " || true && (x[0]|0x20) == (y[0]|0x20) })
	return r(a) + r(b) + strconv.FormatBool(c == nil) + "|" + strconv.Itoa(len(d)) + d[0] + d[1]
}
func growClipReverse() string {
	g := slices.Grow([]int{1, 2}, 10)
	c := slices.Clip(make([]int, 2, 10))
	rv := []int{1, 2, 3, 4}
	slices.Reverse(rv)
	ro := []int{1, 2, 3}
	slices.Reverse(ro)
	var ns []int
	slices.Reverse(ns)
	return r(g) + strconv.Itoa(len(g)) + "|" + strconv.FormatBool(cap(c) == len(c)) + strconv.Itoa(len(c)) + "|" + r(rv) + r(ro) + r(ns)
}
func concatRepeat() string {
	var ns []int
	a := slices.Concat(ns, []int{1}, []int{}, []int{2, 3})
	b := slices.Concat[[]int]()
	c := slices.Concat(ns, ns)
	d := slices.Repeat([]int{1, 2}, 3)
	e := slices.Repeat([]int{1}, 0)
	return r(a) + "|" + strconv.FormatBool(b == nil) + strconv.FormatBool(c == nil) + "|" + r(d) + "|" + strconv.FormatBool(e != nil) + strconv.Itoa(len(e))
}
func replaceNoSpare() string {
	full := []int{1, 2, 3}
	a := slices.Replace(full, 0, 1, 7, 8)
	b := slices.Replace([]int{1, 2, 3}, 1, 3)
	c := slices.Replace([]int{1, 2, 3}, 3, 3, 4)
	return r(a) + "|" + r(b) + "|" + r(c)
}
func insertNoSpare() string {
	full := []int{1, 3}
	a := slices.Insert(full, 1, 2)
	b := slices.Insert([]int{1, 2}, 2, 3, 4)
	c := slices.Insert([]int{1, 2}, 1)
	var ns []int
	d := slices.Insert(ns, 0, 5)
	return r(a) + r(full) + "|" + r(b) + "|" + r(c) + "|" + r(d)
}

func main() {
	deleteFuncClearedTail()
	cloneNilEmpty()
	compactFamily()
	growClipReverse()
	concatRepeat()
	insertNoSpare()
	replaceNoSpare()
}
