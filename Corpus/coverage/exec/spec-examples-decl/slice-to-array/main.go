package main

// spec#Conversions_from_slice_to_array_or_array_pointer block
// Conversions_from_slice_to_array_or_array_pointer-1-2861064a: converting a
// slice to an array copies the elements of the slice's underlying array;
// converting to an array POINTER aliases it (&s1[0] == &s[1]); if the slice
// is shorter than the array a run-time panic occurs; nil slices convert to
// zero-length arrays, to nil zero-length array pointers, and panic for
// longer array pointers; an empty non-nil slice converts to a NON-nil
// zero-length array pointer.

func sliceToArrayOk() int {
	s := make([]byte, 2, 4)
	s[0], s[1] = 10, 20
	a0 := [0]byte(s)
	a1 := [1]byte(s[1:]) // a1[0] == s[1]
	a2 := [2]byte(s)     // a2[0] == s[0]
	if len(a0) != 0 || a1[0] != 20 || a2[0] != 10 || a2[1] != 20 {
		return 1
	}
	s0 := (*[0]byte)(s)     // s0 != nil
	s1 := (*[1]byte)(s[1:]) // &s1[0] == &s[1]
	s2 := (*[2]byte)(s)     // &s2[0] == &s[0]
	if s0 == nil || &s1[0] != &s[1] || &s2[0] != &s[0] {
		return 2
	}
	s2[0] = 99 // aliasing is visible through the slice
	if s[0] != 99 {
		return 3
	}
	var t []string
	t0 := [0]string(t)    // ok for nil slice t
	t1 := (*[0]string)(t) // t1 == nil
	if len(t0) != 0 || t1 != nil {
		return 4
	}
	u := make([]byte, 0)
	u0 := (*[0]byte)(u) // u0 != nil
	if u0 == nil {
		return 5
	}
	return 0
}

// sliceToArrayShort: [4]byte(s) with len(s) == 2 panics.
func sliceToArrayShort() int {
	s := make([]byte, 2, 4)
	a4 := [4]byte(s) // panics: len([4]byte) > len(s)
	return int(a4[0])
}

// sliceToArrayPtrShort: (*[4]byte)(s) with len(s) == 2 panics.
func sliceToArrayPtrShort() int {
	s := make([]byte, 2, 4)
	s4 := (*[4]byte)(s) // panics: len([4]byte) > len(s)
	return int(s4[0])
}

// nilSliceToArrayPtr: (*[1]string)(t) for nil t panics.
func nilSliceToArrayPtr() int {
	var t []string
	t2 := (*[1]string)(t) // panics: len([1]string) > len(t)
	return len(t2[0])
}
