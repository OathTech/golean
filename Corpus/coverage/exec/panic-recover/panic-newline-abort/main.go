package main

func panicNewlineAbort() {
	panic("first line\nsecond line")
}

func main() {
	panicNewlineAbort()
}
