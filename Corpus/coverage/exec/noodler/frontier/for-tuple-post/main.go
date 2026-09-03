// noodler frontier probe — tuple assignment and a call in the for post statement
package main

func next(i int) int { return i + 2 }

// Tuple assignment in the for post statement, and a call in the post.
func forTuplePost() (int, int) {
	r := 0
	for i, j := 0, 10; i < j; i, j = i+1, j-1 {
		r += j - i
	}
	c := 0
	for i := 0; i < 7; i = next(i) {
		c++
	}
	return r, c
}

func main() {}
