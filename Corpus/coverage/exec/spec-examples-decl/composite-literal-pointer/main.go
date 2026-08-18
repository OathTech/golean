package main

// spec#Composite_literals block Composite_literals-3-5424b977 (the Point3D
// and Line declarations) + block Composite_literals-5-3a437841: taking the
// address of a composite literal generates a pointer to a unique variable
// initialized with the literal's value — pointer.y == 1000 with the omitted
// x and z fields zeroed.

type Point3D struct{ x, y, z float64 }

type Line struct{ p, q Point3D }

var pointer *Point3D = &Point3D{y: 1000}

func compositeLiteralPointer() int {
	if pointer.x != 0 || pointer.z != 0 {
		return -1
	}
	line := Line{p: Point3D{x: 1}, q: *pointer}
	return int(line.q.y) + int(line.p.x) // 1001
}
