package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H8: the slices search / compare / order family at ints and strings (the generic stencils per element type).
import (
	"slices"
	"strconv"
)

func i(v int) string  { return strconv.Itoa(v) }
func b(v bool) string { return strconv.FormatBool(v) }

func indexContains() string {
	var ns []int
	return i(slices.Index([]int{1, 2, 3, 2}, 2)) + i(slices.Index([]int{1}, 9)) + i(slices.Index(ns, 0)) + i(slices.Index([]string{"a", "b"}, "b")) + "|" +
		i(slices.IndexFunc([]int{1, 2, 3}, func(x int) bool { return x > 1 })) + i(slices.IndexFunc(ns, func(x int) bool { return true })) + "|" +
		b(slices.Contains([]string{"x", "y"}, "y")) + b(slices.Contains(ns, 1)) + b(slices.ContainsFunc([]int{1, 2}, func(x int) bool { return x == 2 }))
}
func equalCompare() string {
	var ns []int
	return b(slices.Equal(ns, []int{})) + b(slices.Equal([]int{1, 2}, []int{1, 2})) + b(slices.Equal([]int{1}, []int{1, 2})) + b(slices.Equal([]string{"a"}, []string{"a"})) + "|" +
		b(slices.EqualFunc([]int{1, 2}, []string{"1", "2"}, func(a int, s string) bool { return strconv.Itoa(a) == s })) + "|" +
		i(slices.Compare([]int{1, 2}, []int{1, 3})) + i(slices.Compare([]int{1, 2}, []int{1, 2})) + i(slices.Compare([]int{1, 2, 3}, []int{1, 2})) + i(slices.Compare([]int{1}, []int{1, 0})) + i(slices.Compare(ns, []int{})) + i(slices.Compare([]string{"b"}, []string{"a"})) + "|" +
		i(slices.CompareFunc([]int{1}, []string{"1"}, func(a int, s string) int { return 0 }))
}
func binarySearch() string {
	s := []int{1, 3, 5, 7}
	out := ""
	for _, t := range []int{0, 1, 4, 7, 8} {
		idx, found := slices.BinarySearch(s, t)
		out += i(idx) + b(found) + ";"
	}
	type rec struct{ k string }
	rs := []rec{{"a"}, {"c"}, {"e"}}
	idx, found := slices.BinarySearchFunc(rs, "c", func(r rec, k string) int {
		if r.k < k {
			return -1
		}
		if r.k > k {
			return 1
		}
		return 0
	})
	idx2, found2 := slices.BinarySearch([]string{"a", "b"}, "bb")
	return out + "|" + i(idx) + b(found) + "|" + i(idx2) + b(found2)
}
func isSorted() string {
	var ns []int
	return b(slices.IsSorted([]int{1, 2, 2, 3})) + b(slices.IsSorted([]int{2, 1})) + b(slices.IsSorted(ns)) + b(slices.IsSorted([]string{"a", "ab", "b"})) + b(slices.IsSortedFunc([]int{3, 2, 1}, func(a, c int) int { return c - a }))
}
func minMax() string {
	return i(slices.Min([]int{3, -1, 2})) + i(slices.Max([]int{3, -1, 2})) + slices.Min([]string{"b", "a", "ab"}) + slices.Max([]string{"b", "a", "ab"}) + "|" +
		i(slices.MinFunc([]int{3, -1, 2}, func(a, c int) int { return c - a })) + i(slices.MaxFunc([]int{3, -1, 2}, func(a, c int) int { return c - a })) + i(slices.Min([]int{7}))
}

func main() {
	indexContains()
	equalCompare()
	binarySearch()
	isSorted()
	minMax()
}
