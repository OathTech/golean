package main

func complexConstant() int {
	const z = 2 + 3i
	const w = z * (1 - 1i)
	return int(real(w))*10 + int(imag(w))
}

func main() {
	complexConstant()
}
