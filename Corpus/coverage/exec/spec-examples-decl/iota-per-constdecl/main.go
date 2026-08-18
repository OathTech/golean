package main

// spec#Iota block Iota-1-b1d75795: iota is the index of the ConstSpec within
// its ConstSpec list — c0..c2 count 0 1 2; an unused iota still advances
// (a b c d == 1 2 3 8); a typed middle constant (v float64) does not disturb
// the untyped neighbors (u w == 0 84); separate const declarations each reset
// iota to zero (x == 0, y == 0). Subject returns 0 iff every comment holds,
// else the 1-based index of the first failing group.

const (
	c0 = iota // c0 == 0
	c1 = iota // c1 == 1
	c2 = iota // c2 == 2
)

const (
	a = 1 << iota // a == 1  (iota == 0)
	b = 1 << iota // b == 2  (iota == 1)
	c = 3         // c == 3  (iota == 2, unused)
	d = 1 << iota // d == 8  (iota == 3)
)

const (
	u         = iota * 42 // u == 0     (untyped integer constant)
	v float64 = iota * 42 // v == 42.0  (float64 constant)
	w         = iota * 42 // w == 84    (untyped integer constant)
)

const x = iota // x == 0
const y = iota // y == 0

func iotaPerConstDecl() int {
	if c0 != 0 || c1 != 1 || c2 != 2 {
		return 1
	}
	if a != 1 || b != 2 || c != 3 || d != 8 {
		return 2
	}
	if u != 0 || w != 84 {
		return 3
	}
	var vf float64 = v // v is a float64 constant
	if vf != 42.0 {
		return 4
	}
	if x != 0 || y != 0 {
		return 5
	}
	return 0
}
