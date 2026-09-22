package main

// E5BRECV2 (Stage E5, family E5b): `xs[a[9]], ok = <-ch` — the comma-ok RECEIVE (a two-binder
// `recv` body) with a PLANNED target whose index read (a = [1]) panics: before the receive the
// channel still holds 3 (the deferred witness prints `len 1`), after it the channel is drained
// (`len 0` — gc's, the receive first). Reference enumerate.py E5b3. The defer precedes `ok`'s
// declaration so the hand-built wire keeps it as a setup statement (build.py's splice rule).
func e5brecv2() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	a := []int{1}
	defer func() { println("len", len(ch)) }()
	var ok bool
	xs[a[9]], ok = <-ch
	_ = ok
	return xs[0]
}

func main() { println(e5brecv2()) }
