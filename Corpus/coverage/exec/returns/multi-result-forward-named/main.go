package main

func srcNamed() (int, int) {
	return 4, 9
}

func fwdNamed() (p int, q int) {
	return srcNamed()
}

func multiResultForwardNamed() int {
	a, b := fwdNamed()
	return a*10 + b
}

func main() {
	multiResultForwardNamed()
}
