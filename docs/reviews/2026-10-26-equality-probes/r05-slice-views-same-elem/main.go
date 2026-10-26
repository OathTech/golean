package main

func main() { println(run()) }

func run() int {
	s := make([]int, 3)
	t := s[1:]
	done := make(chan int)
	go func() { t[0] = 1; done <- 1 }()
	v := s[1]
	<-done
	return v + s[1]
}
