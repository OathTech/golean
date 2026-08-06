package main

// Audit pin (channels-arc-s1 audit S3/S8): a bare receive in STATEMENT
// position — spec §Expression statements: "function and method calls
// and receive operations can appear in statement context", examples
// `<-ch` and `(<-ch)` — is receive-and-discard. Idiomatic Go
// (`<-done`); the parenthesized form is pinned too.

func recvStmtDrain() int {
	ch := make(chan int, 2)
	ch <- 7
	ch <- 8
	<-ch
	(<-ch)
	return len(ch)
}

func main() {
	recvStmtDrain()
}
