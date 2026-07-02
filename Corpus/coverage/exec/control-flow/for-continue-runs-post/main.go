package main

func forContinueRunsPost() int {
	post := 0
	sum := 0
	step := func(i int) int {
		post = post*10 + i + 1
		return i + 1
	}
	for i := 0; i < 4; i = step(i) {
		if i%2 == 0 {
			continue
		}
		sum += i
	}
	return post*10 + sum
}

func main() {
	forContinueRunsPost()
}
