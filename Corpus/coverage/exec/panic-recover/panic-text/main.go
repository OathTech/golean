package main

func panicUnicodeTwo()      { panic("é") }
func panicUnicodeThree()    { panic("界") }
func panicUnicodeFour()     { panic("😀") }
func panicUnicodeMixed()    { panic("aé界😀z") }
func panicUnicodeNewline()  { panic("é\n界") }
func panicTrailingNewline() { panic("first\n") }

func panicRecoveredNewline() {
	defer func() {
		_ = recover()
		panic("other")
	}()
	panic("first\nsecond")
}

func panicRecoveredUnicode() {
	defer func() {
		_ = recover()
		panic("other")
	}()
	panic("é")
}

func panicPrintUnicode() {
	print("before\n")
	panic("é")
}

func main() {}
