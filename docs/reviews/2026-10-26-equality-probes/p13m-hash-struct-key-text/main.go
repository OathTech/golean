package main

func main() { run() }

type KI struct{ I any }

func run() {
	m := map[KI]int{{1}: 1}
	println(m[KI{[]int{}}])
}
