package main

// Delta-review pin (D1): TWO functions each containing `defer close(ch)`
// — the synthetic closer names must not collide across functions (the
// per-function lift counter resets), and an unrelated function in the
// same package must stay runnable.

func deferCloseFirst() int {
	ch := make(chan int, 1)
	func() {
		defer close(ch)
		ch <- 7
	}()
	v, _ := <-ch
	return v
}

func deferCloseSecond() int {
	ch := make(chan string, 1)
	func() {
		defer close(ch)
		ch <- "ab"
	}()
	s, _ := <-ch
	return len(s)
}

func deferCloseUnrelated() int { return 42 }

func main() {
	deferCloseFirst()
}
