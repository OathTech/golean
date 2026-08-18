// spec#Slice_expressions block Slice_expressions-4-5e36e5ff
// The spec's three default-index equivalences over its own
// a := [5]int{1, 2, 3, 4, 5}:
//
//	a[2:]  == a[2 : len(a)]
//	a[:3]  == a[0 : 3]
//	a[:]   == a[0 : len(a)]
//
// Pins len, cap, and element identity of each defaulted form against
// its written-out counterpart.
package main

func sliceDefaultIndices() int {
	a := [5]int{1, 2, 3, 4, 5}
	score := 0
	s1 := a[2:] // same as a[2 : len(a)]
	t1 := a[2:len(a)]
	if len(s1) == len(t1) && s1[0] == t1[0] && s1[2] == t1[2] {
		score += 1
	}
	if len(s1) == 3 && cap(s1) == 3 && s1[0] == 3 {
		score += 2
	}
	s2 := a[:3] // same as a[0 : 3]
	t2 := a[0:3]
	if len(s2) == 3 && cap(s2) == 5 && s2[0] == 1 && s2[2] == t2[2] {
		score += 4
	}
	s3 := a[:] // same as a[0 : len(a)]
	t3 := a[0:len(a)]
	if len(s3) == 5 && cap(s3) == 5 && s3[4] == t3[4] {
		score += 8
	}
	return score
}

func main() {
	sliceDefaultIndices()
}
