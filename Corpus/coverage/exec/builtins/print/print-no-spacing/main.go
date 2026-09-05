package main

// print writes the operands' bytes with NO separators and NO newline.
func printNoSpacing() int {
	print(1, 2, "x", true, -4)
	print("\n")
	return 0
}
