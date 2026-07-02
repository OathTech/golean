package main

func deferNilFunctionPanic() {
	var f func()
	defer f()
}

func main() {
	deferNilFunctionPanic()
}
