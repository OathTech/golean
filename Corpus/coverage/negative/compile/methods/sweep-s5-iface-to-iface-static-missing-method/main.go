package main

type reader interface{ Read() int }

type readWriter interface {
	Read() int
	Write(int)
}

func main() {
	var r reader
	var rw readWriter = r // reader lacks Write: a static rejection, no assertion
	_ = rw
}
