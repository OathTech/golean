package main

func arrayNilPointerLenCap() int {
	var p *[4]int
	return len(p)*10 + cap(p)
}

func main() {
	arrayNilPointerLenCap()
}
