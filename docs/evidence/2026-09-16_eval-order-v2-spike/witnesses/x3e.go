package main

// X3's empty-channel branch: the receive would BLOCK — in the model a `blocked`
// refusal outside the terminating domain, distinct from the index-panic member
// (which an execution reading the target first still reaches). gc's draw is the
// runtime's deadlock report when it receives first.
func main() {
	ch := make(chan int, 1)
	x := []int{1}
	f := func() int { return 9 }
	x[f()] += <-ch
	println("x3e unreachable")
}
