package main

func untypedComplexContext() int {
	const z = 1.5 + 2.5i
	var c64 complex64 = z
	var c128 complex128 = z + 1i
	return int(real(c64))*1000 + int(imag(c64))*100 + int(real(c128))*10 + int(imag(c128))
}
