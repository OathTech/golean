package main

func typeSwitchDefaultBindingType() int {
	var x any = int8(4)
	switch v := x.(type) {
	case string:
		return len(v)
	default:
		if y, ok := v.(int8); ok {
			return int(y)
		}
		return 0
	}
}

