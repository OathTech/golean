package main

func typeSwitchNilMultiCase() int {
	var x any
	switch x.(type) {
	case nil, int:
		return 1
	default:
		return 2
	}
}

