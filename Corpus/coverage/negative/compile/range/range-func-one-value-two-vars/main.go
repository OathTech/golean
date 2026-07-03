package main

func main() {
	seq := func(yield func(int) bool) {
		yield(1)
	}
	for _, _ = range seq {
	}
}
