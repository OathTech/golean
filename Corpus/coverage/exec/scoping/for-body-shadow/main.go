package main

func forBodyShadow() int {
	x := 1
	sum := 0
	for i := 0; i < 3; i++ {
		x := i + 10
		sum += x
	}
	return x*100 + sum
}

func main() {
	forBodyShadow()
}
