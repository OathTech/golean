package main

import (
	"bytes"
	"cmp"
	"slices"
	"strings"
)

func main() { run() }

func run() {
	zero := 0.0
	nan := zero / zero
	fs := []float64{3, nan, 1, -zero, zero, 2, nan}
	slices.Sort(fs)
	for _, f := range fs {
		if f != f {
			print("NaN ")
		} else if f == 0 {
			if 1/f < 0 {
				print("-0 ")
			} else {
				print("+0 ")
			}
		} else {
			print(int(f), " ")
		}
	}
	println("end")
	ss := []string{"b", "é", "a", "", "Z", "\xff"}
	slices.Sort(ss)
	println(ss[0] == "", ss[1] == "Z", ss[2] == "a", ss[3] == "b", ss[4] == "é", ss[5] == "\xff")
	println(slices.Equal([]int{1, 2}, []int{1, 2}), slices.Equal([]int{}, nil), slices.Equal([]float64{nan}, []float64{nan}))
	println(slices.Index([]float64{1, nan, 2}, nan), slices.Contains([]float64{nan}, nan), slices.Index([]string{"a", "b"}, "b"))
	println(cmp.Compare(nan, 1), cmp.Compare(1, nan), cmp.Compare(nan, nan), cmp.Compare(-zero, zero), cmp.Compare("a", "b"), cmp.Compare(2, 1))
	println(cmp.Less(nan, 1), cmp.Less(1, nan), cmp.Less(nan, nan))
	println(strings.Compare("a", "b"), strings.Compare("b", "a"), strings.Compare("a", "a"), strings.Compare("", "a"))
	println(bytes.Equal([]byte("a"), []byte("a")), bytes.Equal(nil, []byte{}), bytes.Equal([]byte("a"), []byte("b")))
	println(strings.EqualFold("Go", "GO"), strings.EqualFold("é", "É"), strings.EqualFold("a", "b"))
	println(slices.Compare([]int{1, 2}, []int{1, 3}), slices.Compare([]int{1}, []int{1, 0}))
	println(slices.Max([]float64{1, nan, 2}) != slices.Max([]float64{1, nan, 2}), slices.Min([]int{3, 1, 2}))
	ints := []int{3, 1, 2}
	slices.Sort(ints)
	println(ints[0], ints[1], ints[2], slices.IsSorted(ints))
	bi, bf := slices.BinarySearch([]int{1, 3, 5}, 3)
	println(bi, bf)
	println(strings.Contains("abc", "bc"), strings.HasPrefix("abc", "ab"), strings.Index("abc", "c"))
	println(min("a", "b") == "a", slices.Equal([]string{"a"}, []string{"a"}))
}
