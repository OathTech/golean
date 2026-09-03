// noodler frontier probe — auto-deref through pointer-valued map elements (index, field incdec, method)
package main

type Counter struct{ n int }

func (c *Counter) Inc() { c.n++ }

// Map values that are pointers: auto-deref on index, field, method.
func mapOfPointersAutoderef() int {
	m := map[int]*[3]int{1: {1, 2, 3}}
	c := map[string]*Counter{"c": {}}
	c["c"].Inc()
	c["c"].n++
	m[1][2] = 9
	return m[1][2]*10 + c["c"].n
}

func main() {}
