package main

func panicNilAbort() {
	panic(nil)
}

func main() {
	panicNilAbort()
}
