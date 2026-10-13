package main

// BUG-127 fix round: a //go:noinline at the end of the file has no
// declaration to consume it — «misplaced compiler directive» in gc.
func main() { println(1) }

//go:noinline
