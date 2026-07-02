package main

func selectClauseScope() int {
	ch := make(chan int, 1)
	ch <- 4
	x := 10
	result := 0
	select {
	case x := <-ch:
		result = x
	default:
		x := 99
		result = x
	}
	return x*10 + result
}

func main() {
	selectClauseScope()
}
