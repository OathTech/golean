package main

type assertInterfaceReader interface {
	read() int
}

type assertInterfaceWriter interface {
	write() int
}

type assertInterfaceDevice struct {
	n int
}

func (d assertInterfaceDevice) read() int {
	return d.n
}

func typeAssertInterface() int {
	var x any = assertInterfaceDevice{n: 5}
	reader, okReader := x.(assertInterfaceReader)
	_, okWriter := x.(assertInterfaceWriter)
	score := 0
	if okReader {
		score += reader.read()
	}
	if okWriter {
		score += 100
	}
	return score
}
