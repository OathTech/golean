// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Read-modify-write targets (op=, ++/--) whose address computation contains a channel
// RECEIVE and no call — BUG-286 (born red): the lowering's pure-lvalue path emits the
// target and the read separately and each emission hoists its own receive, so the
// receive runs twice (a wrong value; with one buffered value a wrong deadlock). The
// map-key form (emitMapCompound) and the plain read/store controls are green: once.

package main

type pt struct{ x int }

func sliceRecvIndex() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	s := []int{10, 20, 30}
	s[<-ch] += 1
	return len(ch)*100 + s[1] + s[2] - 30
}

func derefRecv() int {
	a, b := 10, 20
	pch := make(chan *int, 2)
	pch <- &a
	pch <- &b
	*(<-pch) += 1
	return len(pch)*100 + a + b - 30
}

func recvPtrField() int {
	p1, p2 := &pt{x: 10}, &pt{x: 20}
	chp := make(chan *pt, 2)
	chp <- p1
	chp <- p2
	(<-chp).x++
	return len(chp)*100 + p1.x + p2.x - 30
}

func arrayRecvIndex() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	arr := [3]int{10, 20, 30}
	arr[<-ch]++
	return len(ch)*100 + arr[1] + arr[2] - 30
}

func mapRecvKey() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	m := map[int]int{1: 20, 2: 30}
	m[<-ch]++
	return len(ch)*100 + m[1] + m[2] - 30
}

func sliceRecvIndexCompound() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	s := []int{10, 20, 30}
	s[<-ch] *= 2
	return len(ch)*100 + s[1] + s[2] - 30
}

func sliceRecvIndexSingle() int {
	ch := make(chan int, 1)
	ch <- 1
	s := []int{10, 20, 30}
	s[<-ch] += 1
	return len(ch)*100 + s[1]
}

func sliceRecvIndexReadControl() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	s := []int{10, 20, 30}
	v := s[<-ch]
	return len(ch)*100 + v
}

func sliceRecvIndexStoreControl() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	s := []int{10, 20, 30}
	s[<-ch] = 5
	return len(ch)*100 + s[1] + s[2] - 30
}

func derefRecvStoreControl() int {
	a, b := 10, 20
	pch := make(chan *int, 2)
	pch <- &a
	pch <- &b
	*(<-pch) = 5
	return len(pch)*100 + a + b - 30
}

func main() {
	sliceRecvIndex()
	derefRecv()
	recvPtrField()
	arrayRecvIndex()
	mapRecvKey()
	sliceRecvIndexCompound()
	sliceRecvIndexSingle()
	sliceRecvIndexReadControl()
	sliceRecvIndexStoreControl()
	derefRecvStoreControl()
}
