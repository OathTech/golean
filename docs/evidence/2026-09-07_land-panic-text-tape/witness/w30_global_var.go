package main

var g = "orig"

func main() {
	defer func() {
		_ = recover()
		panic(g)
	}()
	panic(g)
}
