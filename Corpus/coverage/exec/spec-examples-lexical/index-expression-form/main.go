// spec#Index_expressions block Index_expressions-1-366168ca
// The a[x] form across the operand kinds the surrounding prose
// enumerates: array, slice, string (yields a byte), and map. Distinct
// element values make each indexing load-bearing in the returned sum.
package main

func indexForms() int {
	a := [3]int{10, 20, 30}
	s := []int{5, 6, 7}
	str := "abc"
	m := map[int]int{4: 40}
	x := 1
	return a[x] + s[x] + int(str[x]) + m[4] // 20 + 6 + 98 + 40 = 164
}

func main() {
	indexForms()
}
