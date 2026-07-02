package main

func complexCompoundAssign() int {
	z := complex(1.0, 2.0)
	z += complex(3.0, -5.0)
	z *= complex(0.0, 1.0)
	z -= complex(1.0, 1.0)
	return int(real(z))*100 + int(imag(z))
}

func main() {
	complexCompoundAssign()
}
