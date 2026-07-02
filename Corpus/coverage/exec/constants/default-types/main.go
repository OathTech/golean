package main

func constantDefaultTypes() int {
	var r = 'a'
	var i = 3
	var f = 3.0
	var c = 3i
	var pr *rune = &r
	var pi *int = &i
	var pf *float64 = &f
	var pc *complex128 = &c
	_, _, _, _ = pr, pi, pf, pc
	return int(r) + i + int(f) + int(imag(c))
}

func main() {
	constantDefaultTypes()
}
