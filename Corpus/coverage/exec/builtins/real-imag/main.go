package main

func builtinRealImag() int {
	z := complex(float32(2), float32(3))
	return int(real(z))*10 + int(imag(z))
}

func main() {
	builtinRealImag()
}
