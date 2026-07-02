package main

func infiniteLoopReturn() int {
	n := 0
	for {
		n++
		if n == 4 {
			return n * 10
		}
	}
}

func main() {
	infiniteLoopReturn()
}
