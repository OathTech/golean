package main

type reader interface{ Read() int }

func main() {
	var r reader
	p := &r
	_ = p.Read() // *reader is a pointer to an interface, not an interface
}
