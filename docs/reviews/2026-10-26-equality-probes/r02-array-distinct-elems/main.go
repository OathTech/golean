package main

func main() { println(run()) }

func run() int {
	var arr [2]int
	done := make(chan int)
	go func() { arr[0] = 1; done <- 1 }()
	arr[1] = 2
	<-done
	return arr[0] + arr[1]
}
