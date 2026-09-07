package main

func panicNUL()             { panic("a\x00b") }
func panicSOH()             { panic("a\x01b") }
func panicTAB()             { panic("a\tb") }
func panicCR()              { panic("a\rb") }
func panicControlsNewline() { panic("a\x00\x01\t\r\nsecond") }
func panicControlsRecovered() {
	defer func() {
		_ = recover()
		panic("other")
	}()
	panic("a\x00\x01\t\r\nsecond")
}
func panicControlsOutput() {
	print("out\x00\x01\t\r\n")
	panic("a\x00\x01b")
}
func controlsOutput() int {
	print("out\x00\x01\t\r\n")
	return 7
}

func panicControlsChild() int {
	go func() { panic("a\x00\x01\t\r\nsecond") }()
	<-make(chan int)
	return 0
}

func main() {}
