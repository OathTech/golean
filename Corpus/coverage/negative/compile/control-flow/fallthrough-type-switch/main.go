package main

func main() {
	var x any = 1
	switch x.(type) {
	case int:
		fallthrough
	default:
	}
}
