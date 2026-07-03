package main

func f[M ~map[int]int](m M) {
	delete(m, "x")
}

func main() {}
