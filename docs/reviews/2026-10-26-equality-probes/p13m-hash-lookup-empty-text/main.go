package main

func main() { run() }

func run() {
	m := map[any]int{}
	println(m[[]int{}])
}
