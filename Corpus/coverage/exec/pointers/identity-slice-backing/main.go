package main

// DC01 neighbourhood: SLICE VIEWS are another route to one cell —
// `&s[1]` and `&t[0]` after `t := s[1:]` share the backing array. The
// machine's `sliceIndexLoc` builds the ABSOLUTE index (`offset + i`) on the
// backing array's location, so these agreed before the fix; the rows pin
// that route beside the fixed ones. Distinct elements stay distinct.

func sliceReslice() bool {
	s := []int{1, 2, 3}
	t := s[1:]
	return &s[1] == &t[0]
}

func sliceDistinct() bool {
	s := []int{1, 2, 3}
	t := s[1:]
	return &s[0] == &t[0]
}

func sliceOfArray() bool {
	var arr [3]int
	s := arr[:]
	return &arr[2] == &s[2]
}

func sliceElemMap() int {
	s := []int{1, 2, 3}
	t := s[1:]
	m := map[*int]int{&s[1]: 1}
	m[&t[0]] = 2
	m[&t[1]] = 3
	return 10*len(m) + m[&s[1]]
}

func main() { println(sliceReslice(), sliceDistinct(), sliceOfArray(), sliceElemMap()) }
