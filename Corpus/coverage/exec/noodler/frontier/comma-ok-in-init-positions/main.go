// noodler frontier probe — comma-ok type assertion in if/switch/for init positions
package main

// Comma-ok assertions in if/switch/for init statements.
func commaOkInInitPositions() int {
	var x any = 7
	r := 0
	if v, ok := x.(int); ok {
		r += v
	}
	switch v, ok := x.(string); {
	case ok:
		r += len(v)
	default:
		r += 100
	}
	for _, ok := x.(int); ok; ok = false {
		r += 1000
	}
	return r
}

func main() {}
