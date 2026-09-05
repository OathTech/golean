package main

// println's separator/terminator discipline against print's: one space
// BETWEEN operands (none before the first, none after the last), one
// newline after the last — a single operand gets no space at all.
func printlnSpacing() int {
	println("a", "b")
	println("c")
	println(" ", "")
	println("", "")
	print("d", "e")
	print("\n")
	return 0
}
