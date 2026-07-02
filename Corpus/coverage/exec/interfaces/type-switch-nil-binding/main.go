package main

func typeSwitchNilBinding() int {
	var x any
	switch v := x.(type) {
	case nil:
		if v == nil {
			return 1
		}
		return 2
	default:
		return 3
	}
}

