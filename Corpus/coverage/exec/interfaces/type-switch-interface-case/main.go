package main

type switchInterfaceReader interface {
	read() int
}

type switchInterfaceValue struct {
	n int
}

func (v switchInterfaceValue) read() int {
	return v.n
}

func typeSwitchInterfaceCase() int {
	var x any = switchInterfaceValue{n: 8}
	switch v := x.(type) {
	case interface{ missing() int }:
		return v.missing()
	case switchInterfaceReader:
		return v.read()
	default:
		return 0
	}
}
