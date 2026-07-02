package main

type switchBindingReader interface {
	read() int
}

type switchBindingDevice struct {
	n int
}

func (d switchBindingDevice) read() int {
	return d.n
}

func typeSwitchInterfaceBinding() int {
	var x any = switchBindingDevice{n: 6}
	switch v := x.(type) {
	case switchBindingReader:
		return v.read()
	default:
		return 0
	}
}

func main() {
	typeSwitchInterfaceBinding()
}
