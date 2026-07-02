package main

type typedNilBindingTree struct {
	value int
}

func typeSwitchTypedNilBinding() int {
	var p *typedNilBindingTree
	var x any = p
	switch v := x.(type) {
	case *typedNilBindingTree:
		if v == nil {
			return 1
		}
		return v.value
	case nil:
		return 2
	default:
		return 3
	}
}

