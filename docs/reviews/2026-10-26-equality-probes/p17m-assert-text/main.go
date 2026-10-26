package main

func main() { run() }

type A int
type B int

func run() {
	var v any = B(3)
	println("before")
	_ = v.(A)
}
