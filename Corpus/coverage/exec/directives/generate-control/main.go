package main

// //go:generate is on the directive allowlist: a command line for
// `go generate`, never read by the compiler.
//
//go:generate echo generated
func generateControl() int { return 1 }

func main() { println(generateControl()) }
