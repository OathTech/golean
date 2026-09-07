package main

func main() {
	defer func() {
		_ = recover()
		panic("other")
	}()
	panic("first\nsecond")
}
