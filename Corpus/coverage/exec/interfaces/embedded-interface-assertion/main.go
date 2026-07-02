package main

type embeddedAssertReader interface {
	read() int
}

type embeddedAssertWriter interface {
	write() int
}

type embeddedAssertReadWriter interface {
	embeddedAssertReader
	embeddedAssertWriter
}

type embeddedAssertDevice struct {
	n int
}

func (d embeddedAssertDevice) read() int {
	return d.n
}

func (d embeddedAssertDevice) write() int {
	return d.n + 1
}

func embeddedInterfaceAssertion() int {
	var x any = embeddedAssertDevice{n: 4}
	rw, okRW := x.(embeddedAssertReadWriter)
	r, okReader := any(rw).(embeddedAssertReader)
	score := 0
	if okRW {
		score += rw.read()*10 + rw.write()
	}
	if okReader {
		score += r.read() * 100
	}
	return score
}

func main() {
	embeddedInterfaceAssertion()
}
