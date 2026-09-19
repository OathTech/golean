package main

// W5: println(a[0] + mut()) twice in a loop, mut nils a: per-activation cells —
// {panic at iteration 0; "7" then panic at iteration 1}; no third member.
func w5() {
	a := make([]int, 1)
	a[0] = 7
	mut := func() int { a = nil; return 0 }
	n := 0
	for n < 2 {
		println(a[0] + mut())
		n++
	}
}

func main() { w5() }
