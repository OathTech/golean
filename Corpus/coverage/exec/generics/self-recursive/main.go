package main

type selfCounted int

func selfSum[T ~int](n T) T {
	if n <= 0 {
		return 0
	}
	return n + selfSum(n-1)
}

func genericSelfRecursive() int {
	return int(selfSum(4))*100 + int(selfSum(selfCounted(3)))
}

func main() {
	genericSelfRecursive()
}
