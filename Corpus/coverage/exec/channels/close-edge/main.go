package main

// Close-semantics corners from the ground-truth probes (p06, p21, p24-class
// recoverability): drain order and comma-ok flags across a close, and the
// channel panics being ordinary RECOVERABLE Go panics.

func channelDrainZeroAfterClose() int {
	ch := make(chan int, 3)
	ch <- 10
	ch <- 20
	close(ch)
	score := 0
	v1, ok1 := <-ch
	if ok1 {
		score += v1
	}
	v2, ok2 := <-ch
	if ok2 {
		score += v2
	}
	v3, ok3 := <-ch
	if !ok3 {
		score += 100 + v3
	}
	v4, ok4 := <-ch
	if !ok4 {
		score += 200 + v4
	}
	return score*100 + len(ch)*10 + cap(ch)
}

func channelRecoverNegativeMake(n int) (out int) {
	defer func() {
		if recover() != nil {
			out = 42
		}
	}()
	ch := make(chan int, n)
	return len(ch)
}

func channelRecoverSendClosed() (out int) {
	defer func() {
		if recover() != nil {
			out = 42
		}
	}()
	ch := make(chan int, 1)
	close(ch)
	ch <- 5
	return 0
}

func channelRecoverCloseClosed() (out int) {
	defer func() {
		if recover() != nil {
			out = 42
		}
	}()
	ch := make(chan int)
	close(ch)
	close(ch)
	return 0
}

func channelRecoverCloseNil() (out int) {
	defer func() {
		if recover() != nil {
			out = 42
		}
	}()
	var ch chan int
	close(ch)
	return 0
}

func main() {
	channelDrainZeroAfterClose()
}
