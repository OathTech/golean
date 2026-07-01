package main

func closureShare() int {
	x := 0
	inc := func() {
		x++
	}
	read := func() int {
		return x
	}
	inc()
	inc()
	return read()
}
