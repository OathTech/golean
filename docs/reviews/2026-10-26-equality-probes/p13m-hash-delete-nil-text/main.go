package main

func main() { run() }

func run() {
	var m map[any]int
	delete(m, map[int]int{})
	println("unreachable")
}
