package main

// E5COPY (Stage E5, family E5a): `d[0] + copy(d, s)` with d = [0, 0], s = [7, 8]. copy is an EFFECTFUL
// E1 participant (RATIFIED reading (a)) writing d; the sibling checked read d[0] is unordered against
// it: before the copy 0 + 2 = 2, after 7 + 2 = 9 (gc's: OCOPY is in order.go's call class). Reference
// enumerate.py E5a3; {2, 9}.
func e5copy() int {
	d := []int{0, 0}
	s := []int{7, 8}
	return d[0] + copy(d, s)
}

func main() { println(e5copy()) }
