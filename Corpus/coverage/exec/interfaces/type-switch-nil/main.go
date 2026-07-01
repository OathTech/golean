package main

func typeSwitchNil() int {
	var x any
	switch x.(type) {
	case nil:
		return 1
	case int:
		return 2
	default:
		return 3
	}
}
