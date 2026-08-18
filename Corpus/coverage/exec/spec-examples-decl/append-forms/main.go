package main

// spec#Appending_and_copying_slices block Appending_and_copying_slices-2-7f95cfda:
// append appends single elements, multiple elements, a whole slice (s0...),
// an OVERLAPPING slice of the destination, mixed values to []interface{}, and
// string contents to []byte. Results are checked with a hand-rolled equality
// (the slices import was the case's only frontend blocker — de-imported at
// the P3 audit S5 so the overlapping append, the block's one semantically
// interesting row, reaches the differential).

func eqInts(a, b []int) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func appendInts() int {
	s0 := []int{0, 0}
	// Each slice is checked IMMEDIATELY after its construction: after the
	// overlapping s4 append, the earlier slices' contents are capacity-
	// latitude-dependent (an in-place overlapping append may legally
	// rewrite s3's tail — appendSpillWidth envelope, latitude inventory
	// §0), and the spec asserts only the values PRODUCED. The original
	// post-hoc s3 check observed that latitude and correctly tripped the
	// nondet lane under adversarial streams (P3 audit S5 follow-on).
	s1 := append(s0, 2) // s1 is []int{0, 0, 2}
	if !eqInts(s1, []int{0, 0, 2}) {
		return -1
	}
	s2 := append(s1, 3, 5, 7) // s2 is []int{0, 0, 2, 3, 5, 7}
	if !eqInts(s2, []int{0, 0, 2, 3, 5, 7}) {
		return -2
	}
	s3 := append(s2, s0...) // s3 is []int{0, 0, 2, 3, 5, 7, 0, 0}
	if !eqInts(s3, []int{0, 0, 2, 3, 5, 7, 0, 0}) {
		return -3
	}
	s4 := append(s3[3:6], s3[2:]...) // s4 is []int{3, 5, 7, 2, 3, 5, 7, 0, 0}
	n := 0
	for _, v := range s4 {
		n = n*10 + v
	}
	return n // 357235700
}

func appendInterface() int {
	var t []interface{}
	t = append(t, 42, 3.1415, "foo") // t is []interface{}{42, 3.1415, "foo"}
	n := 0
	if v, ok := t[0].(int); ok && v == 42 {
		n++
	}
	if v, ok := t[1].(float64); ok && v == 3.1415 {
		n++
	}
	if v, ok := t[2].(string); ok && v == "foo" {
		n++
	}
	return len(t)*10 + n // 33
}

func appendString() string {
	var b []byte
	b = append(b, "bar"...) // b is []byte{'b', 'a', 'r'}
	return string(b)
}
