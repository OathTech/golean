package main

// spec#Slice_expressions block Slice_expressions-5-891e8f16: reslicing does
// not copy — s1 := a[3:7] and s2 := s1[1:4] share array a, so s2[1] = 42
// makes s2[1] == s1[2] == a[5] == 42 (checked by address identity too); and
// slicing a NIL slice with s[:0] yields a nil slice (s3 == nil).

func sliceAliasing() int {
	var a [10]int
	s1 := a[3:7]  // underlying array of s1 is a; &s1[2] == &a[5]
	s2 := s1[1:4] // underlying array of s2 is a; &s2[1] == &a[5]
	s2[1] = 42    // s2[1] == s1[2] == a[5] == 42
	n := 0
	if s1[2] == 42 && a[5] == 42 {
		n = 1
	}
	if &s2[1] == &a[5] && &s1[2] == &a[5] {
		n += 2
	}
	var s []int
	s3 := s[:0] // s3 == nil
	if s3 == nil {
		n += 4
	}
	return n // 7
}
