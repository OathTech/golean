package main

// E3RECV (Stage E, family E3 — receives and method calls; lane core/unseq-stage-e-0921,
// 2026-09-21): `x[f()] += <-ch` — the v2.1 spike's X3 as ordinary Go: f (prints nothing,
// returns 9) is E1-ordered BEFORE the receive; the target plan on f's result and its
// checked load `[9]` are unordered against the receive; the deferred witness prints
// len(ch) on the panic path: the receive never happened (len 1 — the load's panic first)
// or drained the channel (len 0, gc's — calls first). Reference: enumerate.py X3 / E3c's
// shape; {panic [9] · len 1, panic [9] · len 0}. The slice is declared LAST so the
// hand-built wire keeps every setup statement through it (build.py's splice rule).
func f() int { return 9 }

func e3recv() int {
	ch := make(chan int, 1)
	defer func() { println("len", len(ch)) }()
	ch <- 5
	x := make([]int, 1)
	x[f()] += <-ch
	return x[0]
}

func main() { println(e3recv()) }
