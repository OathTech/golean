package main

func initPanicBoom() int {
	panic("init boom")
}

var initPanicVal = initPanicBoom()

func initPanic() int {
	return initPanicVal
}

func main() {
	initPanic()
}
