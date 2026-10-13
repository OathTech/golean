package main

// Uninstantiated, f is accepted; f[byte] (9000 bytes) too; f[int] is not.
func f[T any]() {
	var c chan [9000]T
	_ = c
}

func main() { f[int]() }
