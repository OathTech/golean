package main

func main() {
	bad := func(yield func(int, string, bool) bool) {
		_ = yield
	}
	for range bad {
	}
}
