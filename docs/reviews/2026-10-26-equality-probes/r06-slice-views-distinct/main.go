package main

func main() { println(run()) }

func run() int {
	s := make([]int, 3)
	t := s[1:]
	done := make(chan int)
	go func() { t[0] = 1; done <- 1 }()
	s[0] = 2
	<-done
	return s[0] + s[1]
}
