package main

type smallComplex complex64

func typedComplexBinaryConstant() int {
	const base smallComplex = 1 + 2i
	var z smallComplex = base + 3i
	return int(real(z))*10 + int(imag(z))
}
