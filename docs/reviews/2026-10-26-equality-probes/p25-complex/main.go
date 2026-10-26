package main

func main() { run() }

func run() {
	var a complex128 = complex(1, 2)
	b := complex(1, 2)
	println(a == b, a != b, real(a) == 1)
}
