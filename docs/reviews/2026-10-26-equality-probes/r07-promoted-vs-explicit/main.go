package main

func main() { println(run()) }

type Inner struct{ X int }
type Outer struct {
	Inner
	Y int
}

func run() int {
	var o Outer
	done := make(chan int)
	go func() { o.X = 1; done <- 1 }()
	v := o.Inner.X
	<-done
	return v + o.X
}
