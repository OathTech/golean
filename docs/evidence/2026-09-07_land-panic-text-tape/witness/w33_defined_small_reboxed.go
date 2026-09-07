package main

type Code int

func main() {
	defer func() {
		r := recover()
		panic(r.(Code))
	}()
	panic(Code(7))
}
