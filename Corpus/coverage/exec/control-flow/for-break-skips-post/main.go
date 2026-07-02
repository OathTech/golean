package main

func forBreakSkipsPost() int {
	post := 0
	body := 0
	step := func(i int) int {
		post = post*10 + i + 1
		return i + 1
	}
	for i := 0; i < 5; i = step(i) {
		body++
		if i == 2 {
			break
		}
	}
	return post*10 + body
}

func main() {
	forBreakSkipsPost()
}
