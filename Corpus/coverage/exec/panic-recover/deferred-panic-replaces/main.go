package main

func deferredPanicReplaces() {
	defer func() {
		panic("second")
	}()
	panic("first")
}

func main() {
	deferredPanicReplaces()
}
