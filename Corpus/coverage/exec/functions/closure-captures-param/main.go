package main

func bumpBy(n int) int {
	acc := n
	add := func(d int) { acc = acc + d }
	add(5)
	add(7)
	return acc
}

func closureCapturesParam() int {
	return bumpBy(3)
}

func main() {
	closureCapturesParam()
}
