package main

func smoke() int {
	z := 0
	z = 2 + 3
	if z > 4 {
		z = z * 10
	} else {
		z = 0
	}
	return z
}
