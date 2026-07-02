package main

func main() {
	ch := make(chan int)
	defer <-ch
}

