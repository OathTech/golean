package main

func switchInitShadow() int {
	x := 4
	result := 0
	switch x := x + 1; x {
	case 5:
		result = x
	default:
		result = 1
	}
	return x*10 + result
}

func main() {
	switchInitShadow()
}
