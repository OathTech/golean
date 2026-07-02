package main

func nilFunctionCallPanic() int {
	var f func() int
	return f()
}

func main() {
	nilFunctionCallPanic()
}
