package main

func b4BlockingRecv() int {
	ch := make(chan int)
	x := 1
	m := func() int { x = 2; return 0 }
	return <-ch + x + m()
}

func main() { println(b4BlockingRecv()) }
