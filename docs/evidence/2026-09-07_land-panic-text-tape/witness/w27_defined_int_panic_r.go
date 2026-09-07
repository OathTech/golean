package main

type Code int

func main() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(Code(7))
}
