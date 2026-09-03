// noodler frontier probe — nested composite literals with elided element/key types
package main

type Point struct{ x, y int }

// Nested composite literals with elided inner types.
func arrayLitsNestedElided() int {
	g := [2][2]int{{1, 2}, {3, 4}}
	m := map[string]Point{"a": {1, 2}, "b": {3, 4}}
	s := [][]Point{{{1, 1}}, {{2, 2}, {3, 3}}}
	pm := map[Point]string{{1, 2}: "p"}
	return g[1][0]*1000 + m["b"].y*100 + s[1][1].x*10 + len(pm[Point{1, 2}])
}

func main() {}
