package main

// The prefix before a RUNTIME panic (index out of range).
func printThenRuntimePanic(n int) int {
	println("idx", n)
	var s []int
	return s[n]
}
