package main

func panicBoolAbort() {
	panic(true)
}

func main() {
	panicBoolAbort()
}
