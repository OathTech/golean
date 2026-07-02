package main

func channelSelectDefaultOnly() int {
	x := 0
	select {
	default:
		x = 7
	}
	return x
}

func channelSelectClosedBufferedReceive() int {
	ch := make(chan int, 1)
	ch <- 5
	close(ch)
	v := 0
	ok := false
	picked := 0
	select {
	case v, ok = <-ch:
		picked = 1
	default:
		picked = 2
	}
	if ok {
		return picked*1000 + v*10 + len(ch)
	}
	return picked*1000 + v*10 + len(ch) + 1
}

func channelSelectClosedDrainedReceive() int {
	ch := make(chan int)
	close(ch)
	v := 9
	ok := true
	picked := 0
	select {
	case v, ok = <-ch:
		picked = 1
	default:
		picked = 2
	}
	if ok {
		return picked*100 + v
	}
	return picked*100 + v + 10
}

func channelSelectClosedReceiveDeclare() int {
	ch := make(chan int, 1)
	ch <- 6
	close(ch)
	total := 0
	select {
	case v, ok := <-ch:
		if ok {
			total = v
		} else {
			total = 100 + v
		}
	default:
		total = 200
	}
	return total
}

func channelSelectNilAndReadyReceive() int {
	var nilCh chan int
	ready := make(chan int, 1)
	ready <- 4
	picked := 0
	select {
	case <-nilCh:
		picked = 1
	case v := <-ready:
		picked = 10 + v
	default:
		picked = 100
	}
	return picked + len(ready)
}

func channelSelectNilAndReadySend() int {
	var nilCh chan int
	ready := make(chan int, 1)
	picked := 0
	select {
	case nilCh <- 1:
		picked = 1
	case ready <- 8:
		picked = 10
	default:
		picked = 100
	}
	return picked + <-ready
}

func channelSelectSendClosedPanic() {
	ch := make(chan int)
	close(ch)
	select {
	case ch <- 1:
	default:
	}
}

func selectMarkInt(p *int, tag int) int {
	*p = *p*10 + tag
	return tag
}

func selectMarkNilChan(p *int, tag int) chan int {
	*p = *p*10 + tag
	return nil
}

func selectMarkChan(p *int, tag int, ch chan int) chan int {
	*p = *p*10 + tag
	return ch
}

func channelSelectSendRhsEvalUnselected() int {
	var nilCh chan int
	ready := make(chan int, 1)
	ready <- 5
	score := 0
	select {
	case nilCh <- selectMarkInt(&score, 1):
		score = score*10 + 2
	case v := <-ready:
		score = score*10 + v
	}
	return score
}

func channelSelectChanOperandsEvalOrder() int {
	ready := make(chan int, 1)
	ready <- 7
	score := 0
	select {
	case <-selectMarkNilChan(&score, 1):
		score = score*10 + 2
	case v := <-selectMarkChan(&score, 3, ready):
		score = score*10 + v
	}
	return score
}

func channelSelectUnselectedReceiveLhsNotEval() int {
	var nilCh chan int
	ready := make(chan int, 1)
	ready <- 4
	xs := []int{0}
	score := 0
	select {
	case xs[selectMarkInt(&score, 1)] = <-nilCh:
		score = score*10 + 2
	case v := <-ready:
		score = score*10 + v
	}
	return score*10 + xs[0]
}

func channelSelectSelectedReceiveLhsEval() int {
	ready := make(chan int, 1)
	ready <- 8
	xs := []int{0, 0}
	score := 0
	select {
	case xs[selectMarkInt(&score, 1)] = <-selectMarkChan(&score, 2, ready):
		score = score*10 + 3
	default:
		score = 100
	}
	return score*100 + xs[1]
}

func channelSelectSendRhsPanicBeforeDefault() int {
	var nilCh chan int
	select {
	case nilCh <- panicIntForSelect():
		return 1
	default:
		return 2
	}
}

func panicIntForSelect() int {
	panic("select send rhs")
}

func channelSelectRecvChanPanicBeforeDefault() int {
	select {
	case <-panicChanForSelect():
		return 1
	default:
		return 2
	}
}

func panicChanForSelect() chan int {
	panic("select receive channel")
}
