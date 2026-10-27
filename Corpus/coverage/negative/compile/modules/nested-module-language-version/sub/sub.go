package sub

func F() int {
	n := 0
	for i := range 3 {
		n += i
	}
	return n
}
