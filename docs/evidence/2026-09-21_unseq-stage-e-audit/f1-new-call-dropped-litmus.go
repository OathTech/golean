package main

func m() int  { println("m"); return 7 }
func g() int  { println("g"); return 1 }

func newCallDropped() int {
	x := 1
	h := func() int { x = 2; return 100 }
	return *new(m()) + x + h() + g()
}

func main() { println(newCallDropped()) }
