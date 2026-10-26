package main

func main() { run() }

func run() {
	a := any([]int{})
	b := any([]int{})
	println("before")
	println(a == b)
}
