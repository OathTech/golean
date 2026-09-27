package main

func worker(ch chan int, n int) (out int) {
	defer func() { ch <- out }()
	for i := 0; i < n; i++ {
		out += i
	}
	return
}

func probe() int {
	ch := make(chan int)
	go worker(ch, 4)
	v := <-ch
	r := 0
	func() {
		defer func() { recover() }()
		p := &r
		*p = v
		var arr [2]int
		idx := 5
		arr[idx%3+2] = 1
	}()
	println(v, r)
	return v*100 + r
}

func main() { println(probe()) }
