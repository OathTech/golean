package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-024's line): send statements at the channel-operand and value
// shapes the corpus did not hold — a channel that is a map element, a
// struct field, an array element, a slice element, a dereference or a
// parenthesised name; a value that is a receive, a conversion, a struct
// literal, a func literal or the empty struct; a send inside a closure and
// a generic body. Expected = gc go1.26.5.

type holder struct{ ch chan int }

type pt struct{ x, y int }

type id int

// A4.3
func sendMapElem() int {
	m := map[string]chan int{"a": make(chan int, 1)}
	m["a"] <- 1
	return <-m["a"] // 1
}

func sendField() int {
	s := holder{ch: make(chan int, 1)}
	s.ch <- 2
	return <-s.ch // 2
}

func sendArrayElem() int {
	var chs [2]chan int
	chs[1] = make(chan int, 1)
	chs[1] <- 3
	return <-chs[1] // 3
}

func sendSliceElem() int {
	chs := []chan int{make(chan int, 1)}
	chs[0] <- 4
	return <-chs[0] // 4
}

func sendDeref() int {
	ch := make(chan int, 1)
	pch := &ch
	*pch <- 5
	return <-ch // 5
}

func sendParen() int {
	ch := make(chan int, 1)
	(ch) <- 6
	return <-ch // 6
}

// A4.4
func sendOfReceive() int {
	ch := make(chan int, 1)
	ch2 := make(chan int, 1)
	ch2 <- 7
	ch <- <-ch2
	return <-ch + len(ch2)*10 // 7
}

func sendConversion() int {
	ch := make(chan id, 1)
	x := 8
	ch <- id(x)
	return int(<-ch) // 8
}

func sendStructLit() int {
	ch := make(chan pt, 1)
	ch <- pt{1, 2}
	p := <-ch
	return p.x*10 + p.y // 12
}

func sendFunclit() int {
	ch := make(chan func() int, 1)
	ch <- func() int { return 9 }
	return (<-ch)() // 9
}

// A4.7
func sendEmptyStruct() int {
	ch := make(chan struct{}, 1)
	ch <- struct{}{}
	n := len(ch)
	<-ch
	return n*10 + len(ch) // 10
}

// A4.8
func sendInClosure() int {
	ch := make(chan int, 1)
	f := func(v int) { ch <- v }
	f(10)
	return <-ch // 10
}

func sendG[T any](ch chan T, v T) { ch <- v }

func sendInGeneric() int {
	ch := make(chan int, 1)
	sendG(ch, 11)
	cs := make(chan string, 1)
	sendG(cs, "ab")
	return <-ch*10 + len(<-cs) // 112
}

func main() {
	println(sendMapElem(), sendField(), sendArrayElem(), sendSliceElem(), sendDeref(), sendParen(), sendOfReceive(),
		sendConversion(), sendStructLit(), sendFunclit(), sendEmptyStruct(), sendInClosure(), sendInGeneric())
}
