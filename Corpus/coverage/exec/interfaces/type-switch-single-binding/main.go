package main

func typeSwitchSingleBinding() int {
	var x any = int8(7)
	switch v := x.(type) {
	case int8:
		var y int8 = v
		return int(y)
	default:
		return 0
	}
}

func main() {
	typeSwitchSingleBinding()
}
