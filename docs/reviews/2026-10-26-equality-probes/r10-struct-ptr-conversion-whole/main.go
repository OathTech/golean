package main

func main() { println(run()) }

type A struct{ X, Y int }
type B struct{ X, Y int }

func run() int {
	a := A{}
	pb := (*B)(&a)
	done := make(chan int)
	go func() { pb.X = 1; done <- 1 }()
	t := a
	<-done
	return t.Y + a.X
}
