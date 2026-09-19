package main

// R4: old := a; a[0] += mut() with mut rebinding a to b — the frozen header keeps
// one identity for the read and the store. {"old 11 20 / a 100 200", "old 10 20 / a 101 200"}.
func r4() {
	a := make([]int, 2)
	a[0] = 10
	a[1] = 20
	b := make([]int, 2)
	b[0] = 100
	b[1] = 200
	old := a
	mut := func() int { a = b; return 1 }
	a[0] += mut()
	println("old", old[0], old[1])
	println("a", a[0], a[1])
}

func main() { r4() }
