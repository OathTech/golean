package main

func typeSwitchDynamic() int {
	var x any = "go"
	switch v := x.(type) {
	case int:
		return v
	case string:
		return len(v)
	default:
		return 9
	}
}

func main() {
	typeSwitchDynamic()
}
