// noodler frontier probe — self-shadowing define with builtin / conversion RHS
package main

// Inner-scope `s := append(s, 1)` and `x := int64(x)`: the builtin and
// conversion RHS forms of the self-shadowing define.
func selfShadowBuiltinConversion() (int, int64) {
	s := []int{1}
	x := 7
	var n int
	var y int64
	if true {
		s := append(s, 2)
		x := int64(x) * 2
		n = len(s)
		y = x
	}
	return n*10 + len(s), y
}

func main() {}
