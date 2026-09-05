package main

// A mixed println: every admitted kind in one statement, gc's printsp
// between operands, printnl after; a rune constant prints as its int32
// default type (spec: untyped rune constants default to rune).
func printMixed() int {
	println("a", 1, true, uint8(2), 'x', -3, "end")
	return 0
}
