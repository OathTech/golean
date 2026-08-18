package main

// spec#Composite_literals block Composite_literals-10-34318a7a: inside
// composite literals, element and key types may be elided — inner composite
// literals lose their type, and for pointer element types (*Point, PPoint)
// the elided form implies &Point{...}, with {} meaning &Point{} (a non-nil
// pointer to a zero Point). Point is the section's struct{ x, y float64 }.

type Point struct{ x, y float64 }

type PPoint *Point

func compositeLiteralElision() int {
	arr := [...]Point{{1.5, -3.5}, {0, 0}} // same as [...]Point{Point{1.5, -3.5}, Point{0, 0}}
	nested := [][]int{{1, 2, 3}, {4, 5}}   // same as [][]int{[]int{1, 2, 3}, []int{4, 5}}
	pts := [][]Point{{{0, 1}, {1, 2}}}     // same as [][]Point{[]Point{Point{0, 1}, Point{1, 2}}}
	m1 := map[string]Point{"orig": {0, 0}} // same as map[string]Point{"orig": Point{0, 0}}
	m2 := map[Point]string{{0, 0}: "orig"} // same as map[Point]string{Point{0, 0}: "orig"}
	pp := [2]*Point{{1.5, -3.5}, {}}       // same as [2]*Point{&Point{1.5, -3.5}, &Point{}}
	pn := [2]PPoint{{1.5, -3.5}, {}}       // same as [2]PPoint{PPoint(&Point{1.5, -3.5}), PPoint(&Point{})}
	if arr[0].x != 1.5 || arr[0].y != -3.5 || arr[1] != (Point{}) {
		return 1
	}
	sum := 0
	for _, row := range nested {
		for _, v := range row {
			sum += v
		}
	}
	if sum != 15 {
		return 2
	}
	if pts[0][1].y != 2 || pts[0][0].y != 1 {
		return 3
	}
	if m1["orig"] != (Point{}) {
		return 4
	}
	if m2[Point{0, 0}] != "orig" {
		return 5
	}
	if pp[0] == nil || pp[0].x != 1.5 || pp[1] == nil || *pp[1] != (Point{}) {
		return 6
	}
	if pn[0] == nil || (*Point)(pn[0]).y != -3.5 || pn[1] == nil {
		return 7
	}
	return 0
}
