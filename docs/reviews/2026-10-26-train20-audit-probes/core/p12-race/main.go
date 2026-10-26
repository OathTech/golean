package main

// A whole-struct store through the alias in one goroutine against a whole
// read of the original in another, unsynchronised: gc -race reports it; the
// machine's detector keys are canonical (BUG-111/133) and must still say race.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	pb := (*B)(&a)
	done := make(chan bool)
	go func() {
		*pb = B{9, 9}
		done <- true
	}()
	x := a
	<-done
	return x.X + a.X
}

func main() { println(probe()) }
