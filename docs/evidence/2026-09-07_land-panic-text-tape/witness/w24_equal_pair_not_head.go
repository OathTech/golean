package main

func main() {
	defer func() {
		r := recover()
		panic(r)
	}()
	defer func() {
		_ = recover()
		panic("b")
	}()
	panic("a")
}
