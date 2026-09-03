// noodler probe — init() blocks forever on a channel with no other
// goroutine: the runtime's deadlock detector fires during initialization.
package main

var ch = make(chan int)

func init() {
	<-ch
}

func afterInit() int { return 1 }

func main() {}
