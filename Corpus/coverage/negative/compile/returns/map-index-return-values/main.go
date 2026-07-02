package main

func f() (int, bool) {
	m := map[string]int{"x": 1}
	return m["x"]
}

func main() {
	_, _ = f()
}
