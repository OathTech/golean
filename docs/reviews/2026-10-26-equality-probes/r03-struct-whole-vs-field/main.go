package main

func main() { println(run()) }

type S struct{ X, Y int }

func run() int {
	var s S
	done := make(chan int)
	go func() { s.X = 1; done <- 1 }()
	t := s
	<-done
	return t.Y
}
