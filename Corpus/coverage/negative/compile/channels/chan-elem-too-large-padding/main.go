package main

// 1 + 7 (padding) + 65528 = 65536 bytes.
func main() {
	var c chan struct {
		a byte
		b [8191]int64
	}
	println(c == nil)
}
