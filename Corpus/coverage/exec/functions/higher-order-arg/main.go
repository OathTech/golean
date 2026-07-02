package main

func applyTwice(f func(int) int, x int) int {
	return f(f(x))
}

func higherOrderArg() int {
	inc := func(x int) int {
		return x + 1
	}
	double := func(x int) int {
		return x * 2
	}
	return applyTwice(inc, 3)*100 + applyTwice(double, 3)
}
