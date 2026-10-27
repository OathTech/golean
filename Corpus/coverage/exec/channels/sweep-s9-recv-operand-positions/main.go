// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// A channel RECEIVE (not a call) as the operand in the other once-only positions — the
// conversion whole right-hand side, make sizes, len / min operands, an append element, the
// map-assign key and value, a multi-assign target, the receive statement forms, two
// receives in one define and one literal, a struct-field store target, a compound right-
// hand side — each receive exactly once (BUG-286's siblings that agree).

package main

func mk(vals ...int) chan int {
	ch := make(chan int, len(vals))
	for _, v := range vals {
		ch <- v
	}
	return ch
}

func convOfRecv() int {
	ch := mk(7, 8)
	x := int64(<-ch)
	return len(ch)*100 + int(x)
}

func makeMapHintRecv() int {
	ch := mk(2, 3)
	m := make(map[int]int, <-ch)
	m[1] = 1
	return len(ch)*100 + len(m)
}

func makeSliceLenRecv() int {
	ch := mk(2, 3)
	s := make([]int, <-ch)
	return len(ch)*100 + len(s)
}

func lenOfRecv() int {
	chs := make(chan []int, 2)
	chs <- []int{1, 2, 3}
	chs <- []int{1}
	n := len(<-chs)
	return len(chs)*100 + n
}

func minOfRecvs() int {
	ch := mk(5, 3, 9)
	x := min(<-ch, <-ch)
	return len(ch)*100 + x
}

func appendRecv() int {
	ch := mk(5, 6)
	s := []int{1}
	s = append(s, <-ch)
	return len(ch)*100 + len(s)*10 + s[1]
}

func mapAssignRecvKeyValue() int {
	ch := mk(1, 2, 3)
	m := map[int]int{}
	m[<-ch] = <-ch
	return len(ch)*100 + len(m)*10 + m[1]
}

func multiAssignRecvTarget() int {
	ch := mk(1, 2)
	s := []int{0, 0, 0}
	x := 0
	x, s[<-ch] = 5, 6
	return len(ch)*100 + s[1]*10 + x
}

func recvStmtIndexRecvTarget() int {
	ch := mk(1, 2)
	ch2 := mk(9)
	s := []int{0, 0, 0}
	s[<-ch] = <-ch2
	return len(ch)*100 + s[1]
}

func defineTwoRecvs() int {
	ch := mk(1, 2, 3)
	a, b := <-ch, <-ch
	return len(ch)*100 + a*10 + b
}

func sliceLitRecvs() int {
	ch := mk(1, 2, 3)
	s := []int{<-ch, <-ch}
	return len(ch)*100 + s[0]*10 + s[1]
}

func structFieldRecvTarget() int {
	type T struct{ n int }
	ts := []T{{}, {}}
	ch := mk(1, 2)
	ts[<-ch].n = 4
	return len(ch)*100 + ts[1].n
}

func compoundRecvRhs() int {
	ch := mk(1, 2)
	x := 10
	x += <-ch
	return len(ch)*100 + x
}

func main() {
	convOfRecv()
	makeMapHintRecv()
	makeSliceLenRecv()
	lenOfRecv()
	minOfRecvs()
	appendRecv()
	mapAssignRecvKeyValue()
	multiAssignRecvTarget()
	recvStmtIndexRecvTarget()
	defineTwoRecvs()
	sliceLitRecvs()
	structFieldRecvTarget()
	compoundRecvRhs()
}
