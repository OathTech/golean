// noodler frontier probe — three-level nested closure capture of one variable
package main

// Three nested closures capture and modify the same variable.
func threeLevelClosureCapture() int {
	x := 1
	f := func() func() func() int {
		x *= 2
		return func() func() int {
			x += 3
			return func() int {
				x *= 10
				return x
			}
		}
	}
	r := f()()()
	return r*100 + x
}

func main() {}
