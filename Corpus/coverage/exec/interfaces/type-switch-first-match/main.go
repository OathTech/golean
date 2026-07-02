package main

type firstMatchReader interface {
	read() int
}

type firstMatchDevice struct{}

func (firstMatchDevice) read() int {
	return 8
}

func typeSwitchFirstMatch() int {
	var x any = firstMatchDevice{}
	switch x.(type) {
	case firstMatchReader:
		return 1
	case firstMatchDevice:
		return 2
	default:
		return 0
	}
}

