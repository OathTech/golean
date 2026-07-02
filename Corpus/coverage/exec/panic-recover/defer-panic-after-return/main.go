package main

func deferPanicAfterReturn() int {
	defer func() {
		panic("defer boom")
	}()
	return 7
}
