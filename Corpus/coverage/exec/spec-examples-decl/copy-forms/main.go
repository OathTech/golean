package main

// spec#Appending_and_copying_slices block Appending_and_copying_slices-4-820d26f7:
// copy returns the number of elements copied (minimum of the two lengths),
// handles OVERLAPPING source and destination (n2), and copies from a string
// into []byte (n3). Asserted: n1 == 6 with s = [0 1 2 3 4 5]; n2 == 4 with
// s = [2 3 4 5 4 5]; n3 == 5 with b = "Hello".

func digitsOf(s []int) string {
	r := ""
	for _, v := range s {
		r += string(rune('0' + v))
	}
	return r
}

func copyForms() string {
	var a = [...]int{0, 1, 2, 3, 4, 5, 6, 7}
	var s = make([]int, 6)
	var b = make([]byte, 5)
	n1 := copy(s, a[0:]) // n1 == 6, s is []int{0, 1, 2, 3, 4, 5}
	r := string(rune('0'+n1)) + "-" + digitsOf(s)
	n2 := copy(s, s[2:]) // n2 == 4, s is []int{2, 3, 4, 5, 4, 5}
	r += "|" + string(rune('0'+n2)) + "-" + digitsOf(s)
	n3 := copy(b, "Hello, World!") // n3 == 5, b is []byte("Hello")
	r += "|" + string(rune('0'+n3)) + "-" + string(b)
	return r
}
