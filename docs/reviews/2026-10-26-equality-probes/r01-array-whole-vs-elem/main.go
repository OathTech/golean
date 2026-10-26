package main

func main() { println(run()) }

func run() int {
	var arr [2]int
	done := make(chan int)
	go func() { arr[0] = 1; done <- 1 }()
	b := arr
	<-done
	return b[1]
}
