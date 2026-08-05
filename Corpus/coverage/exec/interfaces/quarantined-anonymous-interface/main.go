package main

func poisonAnonIfaceHelper() int {
	var x interface {
		Ready() <-chan int
	}
	_ = x
	ch := make(chan int, 1)
	_ = ch
	return 0
}

func quarantinedAnonymousInterface() int {
	return 23
}

func main() {
	quarantinedAnonymousInterface()
}
