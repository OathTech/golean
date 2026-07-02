package main

func main() {
	ch := make(chan int)
	for i, v := range ch {
		_, _ = i, v
	}
}
