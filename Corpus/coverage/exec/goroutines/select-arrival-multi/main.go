package main

// L2 ARRIVAL-PATH envelope pin (slice 4): an arriving select whose
// waiter-extended readiness sees TWO ready clauses (two workers parked
// at unbuffered sends). The L2 pick chooses the clause; the chosen
// clause's L4 waiter pick then chooses the partner (a singleton here).
// The admitted set is {10, 20}: every schedule commits exactly one
// send, and the loser goroutine is discarded at main's exit (D6 —
// observably nothing, matching gc's exit-0 leak). Which member commits
// is L1 latitude (which worker parks first / arrives) plus the L2
// clause pick on both-parked schedules.

func selectArrivalMulti() int {
	a := make(chan int)
	b := make(chan int)
	got := 0
	go func() {
		a <- 10
	}()
	go func() {
		b <- 20
	}()
	select {
	case v := <-a:
		got = v
	case v := <-b:
		got = v
	}
	return got
}

func main() {
	println(selectArrivalMulti())
}
