package main

func main() {
	var x any = int8(1)
	switch v := x.(type) {
	case int8, int16:
		var y int8 = v
		_ = y
	}
}
