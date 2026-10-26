package main

func main() { println(run()) }

func run() int {
	x := 0
	p := &x
	q := p
	done := make(chan int)
	go func() { *p = 1; done <- 1 }()
	v := *q
	<-done
	return v + x
}
