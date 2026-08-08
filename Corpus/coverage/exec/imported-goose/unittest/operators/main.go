// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/operators.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func LogicalOperators(b1 bool, b2 bool) bool {
	return b1 && (b2 || b1) && !false
}

func LogicalAndEqualityOperators(b1 bool, x uint64) bool {
	return x == 3 && b1 == true
}

func ArithmeticShifts(x uint32, y uint64) uint64 {
	return 0
	// return uint64(x<<3) + (y << uint64(x)) + (y << 1)
}

func BitwiseOps(x uint32, y uint64) uint64 {
	return uint64(x) | uint64(uint32(y))&43
}

func Comparison(x uint64, y uint64) bool {
	if x < y {
		return true
	}
	if x == y {
		return true
	}
	if x != y {
		return true
	}
	if x > y {
		return true
	}
	if x+1 > y-2 {
		return true
	}
	return false
}

func AssignOps() {
	var x uint64
	x += 3
	x -= 3
	x++
	x--
}

func BitwiseAndNot(x uint32, y uint64) uint64 {
	z := uint64(x) &^ y
	z &^= 0xff
	return z
}

func Negative() {
	var x int64 = -10
	x += 3
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanOperators() int {
	sum := 0
	if LogicalOperators(true, false) {
		sum++
	}
	if LogicalAndEqualityOperators(true, 3) {
		sum += 2
	}
	sum += int(ArithmeticShifts(2, 4))*4 + int(BitwiseOps(6, 43))*8
	if Comparison(3, 9) {
		sum += 16
	}
	AssignOps()
	sum += int(BitwiseAndNot(0xabcd, 0xf0f0f))
	Negative()
	return sum
}

func main() {}
