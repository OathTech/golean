package main

func main() { println(run()) }

type Inner struct{ X, Z int }
type Outer struct {
	Inner
	Y int
}

func run() int {
	var o Outer
	done := make(chan int)
	go func() { o.X = 1; done <- 1 }()
	o.Inner.Z = 3
	<-done
	return o.X + o.Z
}
