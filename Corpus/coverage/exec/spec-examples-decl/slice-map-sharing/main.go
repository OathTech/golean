package main

// spec#Assignment_statements block Assignment_statements-8-bcd96992:
// assignment of slices and maps copies the DESCRIPTOR, not the elements:
// after s2 = s1, writing s2[0] changes s1[0]; after m2 = m1, writing
// m1["foo"] is visible through m2. (The block's fmt.Println observations are
// returned instead of printed.)

func sliceDescriptorSharing() int {
	var s1 = []int{1, 2, 3}
	var s2 = s1 // s2 stores the slice descriptor of s1
	s1 = s1[:1] // s1 shares its underlying array with s2
	s2[0] = 42  // setting s2[0] changes s1[0] as well
	// spec: prints [42] [42 2 3]
	return len(s1)*100000 + s1[0]*1000 + s2[0]*10 + s2[1] + s2[2] // 142425
}

func mapDescriptorSharing() int {
	var m1 = make(map[string]int)
	var m2 = m1      // m2 stores the map descriptor of m1
	m1["foo"] = 42   // setting m1["foo"] changes m2["foo"] as well
	return m2["foo"] // spec: prints 42
}
