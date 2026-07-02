package main

func f() {
	m := map[int]int{}
	delete(m, "bad")
}
