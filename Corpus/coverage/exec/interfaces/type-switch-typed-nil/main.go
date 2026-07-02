package main

type switchNilTree struct {
	value int
}

func typeSwitchTypedNil() int {
	var p *switchNilTree
	var x any = p
	switch x.(type) {
	case nil:
		return 1
	case *switchNilTree:
		return 2
	default:
		return 3
	}
}

func main() {
	typeSwitchTypedNil()
}
