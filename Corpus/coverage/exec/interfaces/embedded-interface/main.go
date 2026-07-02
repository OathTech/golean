package main

type interfaceReader interface {
	Read() int
}

type interfaceCloser interface {
	Close() int
}

type interfaceReadCloser interface {
	interfaceReader
	interfaceCloser
}

type interfaceDevice struct{}

func (interfaceDevice) Read() int {
	return 2
}

func (interfaceDevice) Close() int {
	return 3
}

func embeddedInterface() int {
	var x interfaceReadCloser = interfaceDevice{}
	return x.Read()*10 + x.Close()
}

func main() {
	embeddedInterface()
}
