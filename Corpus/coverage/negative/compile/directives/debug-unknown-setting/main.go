//go:debug nonexistentSetting=1
package main

// BUG-128: the go command rejects an unknown //go:debug setting; the
// frontend exported the program and the model answered 7 before the
// directive refusal.
func main() { println(7) }
