package main

func forInitScope() int {
	i := 10
	sum := 0
	for i := 0; i < 3; i++ {
		sum += i
	}
	return i*10 + sum
}

func main() {
	forInitScope()
}
