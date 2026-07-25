package main

func forLoopvarEscape() int {
	var a, b func() int
	for i := 0; i < 2; i++ {
		if i == 0 {
			a = func() int { return i }
		} else {
			b = func() int { return i }
		}
	}
	return a()*10 + b()
}

func main() {
	forLoopvarEscape()
}
