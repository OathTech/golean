package main

// spec#Receive_operator block Receive_operator-2-5d49b546: a receive in a
// two-value form yields (value, ok) in all four declared forms — including
// var x, ok T = <-ch, where BOTH x and ok are declared with type T (which
// therefore must be bool, over a chan bool). ok is false after the channel
// is closed and drained, with x the element zero value.

func receiveCommaOk() int {
	ch := make(chan int, 3)
	ch <- 4
	ch <- 5
	var x int
	var ok bool
	x, ok = <-ch
	x2, ok2 := <-ch
	close(ch)
	var x3, ok3 = <-ch // closed and drained: 0, false
	n := 0
	if ok {
		n++
	}
	if ok2 {
		n++
	}
	if ok3 || x3 != 0 {
		n = -100
	}
	return x*100 + x2*10 + n // 452
}

func receiveCommaOkTyped() int {
	ch := make(chan bool, 1)
	ch <- true
	var x, ok bool = <-ch // the spec's `var x, ok T = <-ch` with T = bool
	if x && ok {
		return 1
	}
	return 0
}
