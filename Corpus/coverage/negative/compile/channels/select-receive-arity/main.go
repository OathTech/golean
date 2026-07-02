package main

func main() {
	ch := make(chan int, 1)
	a, b, c := <-ch
	_, _, _ = a, b, c
}
