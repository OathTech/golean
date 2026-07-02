package main

func complexBasic() int {
	z := complex(2.0, 3.0)
	w := complex(1.0, -1.0)
	sum := z + w
	product := z * w
	return int(real(sum))*1000 + int(imag(sum))*100 + int(real(product))*10 + int(imag(product))
}

func main() {
	complexBasic()
}
