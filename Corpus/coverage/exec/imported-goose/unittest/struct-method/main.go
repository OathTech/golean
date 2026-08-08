// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/struct_method.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type Point struct {
	x uint64
	y uint64
}

func (c Point) Add(z uint64) uint64 {
	return c.x + c.y + z
}

func (c Point) GetField() uint64 {
	x := c.x
	y := c.y
	return x + y
}

func UseAdd() uint64 {
	c := Point{x: 2, y: 3}
	r := c.Add(4)
	return r
}

func UseAddWithLiteral() uint64 {
	r := Point{x: 2, y: 3}.Add(4)
	return r
}

func (Point) IgnoreReceiver() string {
	return "ok"
}

// --- GoLean harness ---
// Authored wrapper.

func goleanStructMethod() int {
	sum := int(UseAdd())
	sum += int(UseAddWithLiteral()) * 100
	sum += int(Point{x: 1, y: 2}.GetField()) * 10000
	sum += len(Point{}.IgnoreReceiver()) * 100000
	return sum
}

func main() {}
