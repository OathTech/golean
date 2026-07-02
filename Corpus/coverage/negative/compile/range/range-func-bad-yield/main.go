package main

func main() {
	bad := func(yield func(int)) {
		yield(1)
	}
	for range bad {
	}
}
