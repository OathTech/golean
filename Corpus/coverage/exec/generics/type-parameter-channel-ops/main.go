package main

type genericChan chan int

func useBuffered[C ~chan int](ch C) int {
	ch <- 4
	ch <- 5
	x := <-ch
	return len(ch)*100 + cap(ch)*10 + x
}

func genericTypeParameterChannelOps() int {
	ch := make(genericChan, 2)
	return useBuffered(ch)
}
