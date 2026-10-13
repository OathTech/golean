package main

// calcStructOffset: a field end offset >= MaxWidth (1<<50); gc go1.26.5
// reports it as an internal compiler error (typePos on an unnamed struct).
type S struct {
	a [1 << 49]byte
	b [1 << 49]byte
}

func main() {}
