package main

type signal complex128

func definedComplexOps() int {
	a := signal(2 + 3i)
	b := signal(1 - 2i)
	sum := a + b
	product := a * b
	score := int(real(complex128(sum)))*1000 + int(imag(complex128(sum)))*100
	score += int(real(complex128(product)))*10 + int(imag(complex128(product)))
	if sum == signal(3+1i) {
		score += 10000
	}
	return score
}

func main() {
	definedComplexOps()
}
