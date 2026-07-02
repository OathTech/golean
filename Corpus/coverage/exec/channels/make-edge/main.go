package main

func channelMakeZeroBuffer() int {
	ch := make(chan int)
	return len(ch)*10 + cap(ch)
}

func channelMakeLenExpression() int {
	n := 1
	ch := make(chan int, channelMakeBump(&n))
	ch <- 9
	return n*100 + len(ch)*10 + cap(ch)
}

func channelMakeBump(p *int) int {
	*p = *p + 2
	return *p
}

func channelMakeNegativePanic() {
	n := -1
	_ = make(chan int, n)
}

func channelLenCapDirectionalValues() int {
	ch := make(chan int, 3)
	ch <- 1
	var sendOnly chan<- int = ch
	var recvOnly <-chan int = ch
	return len(sendOnly)*1000 + cap(sendOnly)*100 + len(recvOnly)*10 + cap(recvOnly)
}

func channelCloseDoesNotDrain() int {
	ch := make(chan int, 2)
	ch <- 3
	ch <- 4
	close(ch)
	before := len(ch)
	first, okFirst := <-ch
	middle := len(ch)
	second, okSecond := <-ch
	after := len(ch)
	score := before*10000 + first*1000 + middle*100 + second*10 + after
	if okFirst {
		score += 100000
	}
	if okSecond {
		score += 200000
	}
	return score
}

func channelBufferedFifo() int {
	ch := make(chan int, 3)
	ch <- 2
	ch <- 5
	ch <- 8
	return (<-ch)*100 + (<-ch)*10 + <-ch
}

func channelReceiveCommaOkOpen() int {
	ch := make(chan int, 1)
	ch <- 6
	v, ok := <-ch
	if ok {
		return v*10 + len(ch)
	}
	return 100 + v
}

func channelOrdinarySendEvalOrder() int {
	ch := make(chan int, 1)
	score := 0
	channelEvalChan(&score, 1, ch) <- channelEvalValue(&score, 2)
	return score*10 + <-ch
}

func channelOrdinaryReceiveEvalOrder() int {
	ch := make(chan int, 1)
	ch <- 7
	score := 0
	return channelEvalValue(&score, 1)*100 + (<-channelEvalChan(&score, 2, ch))*10 + score
}

func channelCloseEvalOrder() int {
	ch := make(chan int, 1)
	ch <- 5
	score := 0
	close(channelEvalChan(&score, 3, ch))
	v, ok := <-ch
	if ok {
		return score*100 + v
	}
	return score*100 + 10 + v
}

func channelEvalChan(p *int, tag int, ch chan int) chan int {
	*p = *p*10 + tag
	return ch
}

func channelEvalValue(p *int, tag int) int {
	*p = *p*10 + tag
	return tag
}
