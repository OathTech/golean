package main

// //go:noinline is on the directive allowlist: an inlining hint with no
// semantic effect (ten other corpus files carry it).
//
//go:noinline
func noinlineControl() int { return 1 }

func main() { println(noinlineControl()) }
