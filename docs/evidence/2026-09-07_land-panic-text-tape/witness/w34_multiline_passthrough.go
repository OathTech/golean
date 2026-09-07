package main

func main() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic("first\nsecond")
}
