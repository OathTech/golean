package main

// SCHEDULE-DEPENDENT observables — deliberately RED-PINNED for slice 4
// (charter: the membership lane's enumerator over schedules). The
// observation genuinely varies with the schedule (which sender commits
// first is pure L1 latitude), so the strict lane's three-stream
// invariance check must refuse it; the membership lane will own it.

func schedFirstCome() int {
	ch := make(chan int, 2)
	done := make(chan int)
	go func() {
		ch <- 1
		done <- 0
	}()
	go func() {
		ch <- 2
		done <- 0
	}()
	<-done
	<-done
	first := <-ch
	second := <-ch
	return first*10 + second // 12 or 21, by schedule
}

func main() {
	schedFirstCome()
}
