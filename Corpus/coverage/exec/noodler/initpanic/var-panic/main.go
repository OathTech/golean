// noodler probe — a package-level variable initializer panics (an index
// out of range in a called function).
package main

func pick(i int) int {
	s := []int{1, 2}
	return s[i]
}

var bad = pick(5)

func afterInit() int { return bad }

func main() {}
