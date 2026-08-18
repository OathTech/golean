package main

// spec#Composite_literals block Composite_literals-4-56653998: struct
// literals — a keyless empty literal is the zero value; a keyed
// literal may omit fields, and "omitted fields get the zero value".
// Expected: origin == Point3D{0,0,0}; line.p == origin;
// line.q.y == -4, line.q.z == 12.3, and line.q.x == 0 (the spec's
// own comment: "zero value for line.q.x").

type czPoint3D struct{ x, y, z float64 }
type czLine struct{ p, q czPoint3D }

func complitStructZero() (float64, float64, float64, float64, bool) {
	origin := czPoint3D{}                              // zero value for Point3D
	line := czLine{origin, czPoint3D{y: -4, z: 12.3}} // zero value for line.q.x
	return line.q.x, line.q.y, line.q.z, origin.x + origin.y + origin.z, line.p == origin
}

func main() {
	complitStructZero()
}
