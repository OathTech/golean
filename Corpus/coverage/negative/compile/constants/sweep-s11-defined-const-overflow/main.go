package main

type cI8 int8

func main() {
	const k cI8 = -128
	x := k - 1
	_ = x
}
