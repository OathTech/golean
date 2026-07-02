package main

func typeSwitchMultiBinding() int {
	var x any = int8(7)
	switch v := x.(type) {
	case int8, int16:
		if y, ok := v.(int8); ok {
			return int(y)
		}
		return 1
	default:
		return 0
	}
}

func main() {
	typeSwitchMultiBinding()
}
