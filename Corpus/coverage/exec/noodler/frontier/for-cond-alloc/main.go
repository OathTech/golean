// noodler frontier probe — make() inside the for condition
package main

// An allocation in the for condition.
func forCondAlloc() int {
	i := 0
	for len(make([]int, i)) < 3 {
		i++
	}
	return i
}

func main() {}
