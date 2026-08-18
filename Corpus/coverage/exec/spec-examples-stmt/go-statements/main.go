package main

// spec#Go_statements block Go_statements-2-c0556425: a go statement
// "starts the execution of a function call as an independent
// concurrent thread of control"; "the function value and parameters
// are evaluated as usual in the calling goroutine". The block's two
// shapes: go Server() (named call) and
// go func(ch chan<- bool) { for { ... ch <- true } }(c) (a function
// literal with an unending send loop, invoked with an argument).
// Adaptation: Server/sleep are undefined in the spec — here the named
// server sends 42 once, and the literal's sleep is dropped (its loop
// still sends forever; the receiver takes three values and returns,
// leaving the sender parked — program exit does not wait for it).
// All observables are fixed by channel rendezvous, schedule-
// independent (cf. goroutines/pipeline's strict rows).
// Expected: named -> 42; literal-loop -> 3 trues received; the
// param-evaluation subject -> 7 (x was evaluated AT the go statement,
// before the later x = 99 write in the same calling goroutine).

func gsServer(done chan<- int) {
	done <- 42
}

func goStatementNamedCall() int {
	done := make(chan int)
	go gsServer(done)
	return <-done
}

func goStatementFuncLiteral() int {
	c := make(chan bool)
	go func(ch chan<- bool) {
		for {
			ch <- true
		}
	}(c)
	got := 0
	for i := 0; i < 3; i++ {
		if <-c {
			got++
		}
	}
	return got
}

func goStatementParamsEvaluatedAtGo() int {
	res := make(chan int)
	x := 7
	go func(v int) { res <- v }(x) // x is read here, in the calling goroutine
	x = 99                         // same goroutine, after the go statement
	_ = x
	return <-res
}

func main() {
	goStatementNamedCall()
}
