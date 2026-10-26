package main

// A whole-struct store through the alias in a goroutine, synchronised by a
// channel; the original observes it.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	done := make(chan bool)
	go func() {
		*pb = B{9, 8}
		done <- true
	}()
	<-done
	return a.X*10 + a.Y
}

func main() { println(probe()) }
