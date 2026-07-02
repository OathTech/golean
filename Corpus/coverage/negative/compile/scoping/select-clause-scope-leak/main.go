package main

func main() {
	ch := make(chan int)
	select {
	case x := <-ch:
		_ = x
	default:
	}
	_ = x
}
