package main

func main() { run() }

type I1 interface{ M() }
type B int

func run() {
	var v any = B(3)
	_ = v.(I1)
}
