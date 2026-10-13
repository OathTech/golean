package main

// A body-less function is a gc rejection in a package of Go files only
// (cmd/go passes -complete), unless it is //go:linkname'd (BUG-126).
func f(x int)

func g() int { return 7 }

func main() { println(g()) }
