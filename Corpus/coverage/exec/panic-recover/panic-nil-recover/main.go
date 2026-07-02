package main

func panicNilRecover() (result int) {
	// Go 1.21+: panic(nil) recovers a non-nil value.
	defer func() {
		if recover() != nil {
			result = 1
		}
	}()
	panic(nil)
}

func main() {
	panicNilRecover()
}
