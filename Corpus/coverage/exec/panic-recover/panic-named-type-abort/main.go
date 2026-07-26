package main

type panicCode int

func panicNamedTypeAbort() {
	panic(panicCode(7))
}

func main() {
	panicNamedTypeAbort()
}
