package main

// spec#Receive_operator block Receive_operator-1-fc6a6263: the value
// of <-ch is the value received from ch, usable as an initializer
// (v1 := <-ch), an assignment source (v2 = <-ch), a call argument
// (f(<-ch)), and as a bare expression statement whose value is
// discarded (<-strobe). The expression blocks until a value is
// available. Adaptation: buffered channels are preloaded in the same
// goroutine so every receive finds a value ready (single-goroutine,
// deterministic; channels are FIFO). Expected: v1 == 11, v2 == 22,
// f(<-ch) == 66 (f doubles 33), and the strobe value is consumed
// (len(strobe) drops 1 -> 0).

func receiveForms() (int, int, int, int) {
	ch := make(chan int, 3)
	ch <- 11
	ch <- 22
	ch <- 33
	strobe := make(chan int, 1)
	strobe <- 1

	f := func(v int) int { return v * 2 }

	v1 := <-ch
	var v2 int
	v2 = <-ch
	r := f(<-ch)
	<-strobe // wait until clock pulse and discard received value
	return v1, v2, r, len(strobe)
}

func main() {
	receiveForms()
}
