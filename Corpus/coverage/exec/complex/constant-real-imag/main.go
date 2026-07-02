package main

func complexConstantRealImag() int {
	const z = (2 + 3i) * (4 - 1i)
	const r = real(z)
	const i = imag(z)
	const w = complex(r-1, i+2)
	return int(real(w))*100 + int(imag(w))
}

func main() {
	complexConstantRealImag()
}
