// noodler frontier probe — &[]T{}, &map[K]V{}, &[N]T{} composite literal addresses
package main

// Pointers to slice/map/array composite literals (spec#Composite_literals:
// "&T{...}" for any composite type).
func addressOfSliceMapArrayLiteral() int {
	ps := &[]int{1, 2, 3}
	pm := &map[string]int{"a": 4}
	pa := &[2]int{5, 6}
	(*ps)[0] = 10
	(*pm)["b"] = 7
	return (*ps)[0] + (*pm)["a"] + (*pm)["b"] + pa[1] + len(*pm)
}

func main() {}
