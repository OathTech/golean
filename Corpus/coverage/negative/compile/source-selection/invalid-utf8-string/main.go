package main

// S20 sweep (lane sweep/s20-admission, 2026-10-27): the string literal below holds
// the byte 0xff, which is not UTF-8 (gc: invalid UTF-8 encoding; go/parser: illegal).
func main() { println(len("aÿb")) }
