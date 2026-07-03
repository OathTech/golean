package main

func main() {
	bad := func(yield func(int) bool) int {
		_ = yield
		return 0
	}
	for range bad {
	}
}
