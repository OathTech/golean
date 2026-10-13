package main

// [8192]int is exactly 65536 bytes: gc rejects at width >= 1<<16.
func main() {
	var c chan [8192]int
	println(c == nil)
}
