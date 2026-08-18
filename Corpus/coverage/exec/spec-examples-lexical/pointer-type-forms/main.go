// spec#Pointer_types block Pointer_types-2-4fa35dec
// The spec's two pointer-type example forms, *Point and *[4]int,
// declared and exercised. Also pins the surrounding prose assertion
// that the value of an uninitialized pointer is nil, auto-deref field
// selection through *Point, indexing/len through *[4]int.
package main

type Point struct {
	x, y float64
}

func pointerTypeForms() int {
	var pp *Point  // *Point
	var pa *[4]int // *[4]int
	score := 0
	if pp == nil {
		score += 1
	}
	if pa == nil {
		score += 2
	}
	p := Point{x: 3, y: 4}
	a := [4]int{10, 20, 30, 40}
	pp = &p
	pa = &a
	if pp.x == 3 && pp.y == 4 {
		score += 4
	}
	pp.x = 5
	if p.x == 5 {
		score += 8
	}
	pa[1] = 21
	if a[1] == 21 && len(pa) == 4 {
		score += 16
	}
	return score
}

func main() {
	pointerTypeForms()
}
