// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/operations.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// helpers
func reverseAssignOps64(x uint64) uint64 {
	var y uint64
	y += x
	y -= x
	y++
	y--
	return y
}

func reverseAssignOps32(x uint32) uint32 {
	var y uint32
	y += x
	y -= x
	y++
	y--
	return y
}

func add64Equals(x uint64, y uint64, z uint64) bool {
	return x+y == z
}

func sub64Equals(x uint64, y uint64, z uint64) bool {
	return x-y == z
}

// tests
func testReverseAssignOps64() bool {
	var ok = true
	ok = ok && (reverseAssignOps64(0) == 0)
	ok = ok && (reverseAssignOps64(1) == 0)
	ok = ok && (reverseAssignOps64(1231234) == 0)
	ok = ok && (reverseAssignOps64(0xDD00CC00BB00AA) == 0)
	ok = ok && (reverseAssignOps64(1<<63) == 0)
	ok = ok && (reverseAssignOps64(1<<47) == 0)
	ok = ok && (reverseAssignOps64(1<<20) == 0)
	ok = ok && (reverseAssignOps64(1<<18) == 0)
	ok = ok && (reverseAssignOps64(1<<10) == 0)
	ok = ok && (reverseAssignOps64(1<<0) == 0)
	ok = ok && (reverseAssignOps64(1<<64-1) == 0)
	return ok
}

func failing_testReverseAssignOps32() bool {
	var ok = true
	ok = ok && (reverseAssignOps32(0) == 0)
	ok = ok && (reverseAssignOps32(1) == 0)
	ok = ok && (reverseAssignOps32(1231234) == 0)
	ok = ok && (reverseAssignOps32(0xCCBB00AA) == 0)
	ok = ok && (reverseAssignOps32(1<<20) == 0)
	ok = ok && (reverseAssignOps32(1<<18) == 0)
	ok = ok && (reverseAssignOps32(1<<10) == 0)
	ok = ok && (reverseAssignOps32(1<<0) == 0)
	ok = ok && (reverseAssignOps32(1<<32-1) == 0)
	return ok
}

func testAdd64Equals() bool {
	var ok = true
	ok = ok && add64Equals(2, 3, 5)
	ok = ok && add64Equals(1<<64-1, 1, 0)
	return ok
}

func testSub64Equals() bool {
	var ok = true
	ok = ok && sub64Equals(2, 1, 1)
	ok = ok && sub64Equals(1<<64-1, 1<<63, 1<<63-1)
	ok = ok && sub64Equals(2, 8, 1<<64-6)
	return ok
}

func testDivisionPrecedence() bool {
	blockSize := uint64(4096)
	hdrmeta := uint64(8)
	hdraddrs := (blockSize - hdrmeta) / 8
	return hdraddrs == 511
}

func testModPrecedence() bool {
	x1 := 513 + 12%8
	x2 := (513 + 12) % 8
	return x1 == 517 && x2 == 5
}

func testBitwiseOpsPrecedence() bool {
	var ok = true

	ok = ok && (222|327 == 479)
	ok = ok && (468&1191 == 132)
	ok = ok && (453^761 == 828)

	ok = ok && (453^761|121 == 893)
	ok = ok && (468&1191|333 == 461)
	ok = ok && (222|327&421 != 389)
	return ok
}

func testArithmeticShifts() bool {
	var ok = true
	ok = ok && (672<<3 == 5376)
	ok = ok && (672<<51 == 1513209474796486656)

	ok = ok && (672>>4 == 42)
	ok = ok && (672>>12 == 0)

	ok = ok && (672>>4<<4 == 672)
	return ok
}

func testBitAddAnd() bool {
	tid := uint64(17)
	n := uint64(16)
	return ((tid + n) & ^(n - 1)) == 32
}

func testManyParentheses() bool {
	return ((1%2)|(3%4))*6 == 3*6
}

func testPlusTimes() bool {
	return (2+5)*2 == 14
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestReverseAssignOps64() int {
	if testReverseAssignOps64() {
		return 1
	}
	return 0
}

func goleanFailing_testReverseAssignOps32() int {
	if failing_testReverseAssignOps32() {
		return 1
	}
	return 0
}

func goleanTestAdd64Equals() int {
	if testAdd64Equals() {
		return 1
	}
	return 0
}

func goleanTestSub64Equals() int {
	if testSub64Equals() {
		return 1
	}
	return 0
}

func goleanTestDivisionPrecedence() int {
	if testDivisionPrecedence() {
		return 1
	}
	return 0
}

func goleanTestModPrecedence() int {
	if testModPrecedence() {
		return 1
	}
	return 0
}

func goleanTestBitwiseOpsPrecedence() int {
	if testBitwiseOpsPrecedence() {
		return 1
	}
	return 0
}

func goleanTestArithmeticShifts() int {
	if testArithmeticShifts() {
		return 1
	}
	return 0
}

func goleanTestBitAddAnd() int {
	if testBitAddAnd() {
		return 1
	}
	return 0
}

func goleanTestManyParentheses() int {
	if testManyParentheses() {
		return 1
	}
	return 0
}

func goleanTestPlusTimes() int {
	if testPlusTimes() {
		return 1
	}
	return 0
}

func main() {}
