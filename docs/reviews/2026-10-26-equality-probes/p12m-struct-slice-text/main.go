package main

func main() { run() }

type WithSlice struct{ S []int }

func run() {
	a := any(WithSlice{})
	b := any(WithSlice{})
	println(a == b)
}
