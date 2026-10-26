package main

func main() { println(run()) }

func run() int {
	var arr [2]bool
	done := make(chan int)
	go func() { arr[0] = true; done <- 1 }()
	arr[1] = true
	<-done
	if arr[0] && arr[1] {
		return 1
	}
	return 0
}
