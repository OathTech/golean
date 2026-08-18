package main

// spec#Function_literals block Function_literals-2-a0dfaa1c (a function
// literal value) + block Function_literals-3-0b0ad6e6: a function literal
// may be assigned to a variable or INVOKED DIRECTLY —
// func(ch chan int){ ch <- ACK }(replyChan). ACK and replyChan are realized
// as a constant and a buffered channel.

const ACK = 1

func functionLiterals() int {
	lit := func(a, b int, z float64) bool { return a*b < int(z) } // block -2
	f := func(x, y int) int { return x + y }
	replyChan := make(chan int, 1)
	func(ch chan int) { ch <- ACK }(replyChan) // invoked directly
	v := <-replyChan
	n := 0
	if lit(2, 3, 7.5) { // 6 < 7
		n = 1
	}
	return f(10, 20)*100 + v*10 + n // 3011
}
