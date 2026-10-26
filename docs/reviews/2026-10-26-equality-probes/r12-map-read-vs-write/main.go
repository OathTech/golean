package main

func main() { println(run()) }

func run() int {
	m := map[int]int{}
	done := make(chan int)
	go func() { m[1] = 1; done <- 1 }()
	v := m[2]
	<-done
	return v + len(m)
}
