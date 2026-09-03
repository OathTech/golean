// noodler frontier probe — per-iteration copies of two loop variables
package main

// Two loop variables both get per-iteration copies.
func twoLoopVarsPerIteration() int {
	var fs []func() int
	for i, j := 0, 10; i < 3; i, j = i+1, j-1 {
		fs = append(fs, func() int { return i*100 + j })
	}
	return fs[0]() + fs[2]()
}

func main() {}
