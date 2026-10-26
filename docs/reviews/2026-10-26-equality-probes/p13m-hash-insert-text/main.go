package main

func main() { run() }

func run() {
	m := map[any]int{1: 1}
	m[[]int{}] = 1
	println(len(m))
}
