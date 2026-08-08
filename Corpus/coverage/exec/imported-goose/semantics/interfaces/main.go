// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/interfaces.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// ----------------------------
// SETUP
// ----------------------------

type geometryInterface interface {
	Square() uint64
	Volume() uint64
}

func measureArea(t geometryInterface) uint64 {
	return t.Square()
}

func measureVolumePlusNM(t geometryInterface, n uint64, m uint64) uint64 {
	return t.Volume() + n + m
}

func measureVolume(t geometryInterface) uint64 {
	return t.Volume()
}

type SquareStruct struct {
	Side uint64
}

func (t SquareStruct) Square() uint64 {
	return t.Side * t.Side
}

func (t SquareStruct) Volume() uint64 {
	return t.Side * t.Side * t.Side
}

// ----------------------------
// TESTS
// ----------------------------

func testBasicInterface() bool {
	s := SquareStruct{
		Side: 2,
	}
	return measureArea(s) == 4
}

func testAssignInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	area := measureArea(s)
	return area == 9
}

func testMultipleInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureArea(s)
	square2 := measureArea(s)
	return square1 == square2
}

func testBinaryExprInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureArea(s)
	square2 := measureVolume(s)
	return square1 == measureArea(s) && square2 == measureVolume(s)
}

func testIfStmtInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	if measureArea(s) == 9 {
		return true
	}
	return false
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestBasicInterface() int {
	if testBasicInterface() {
		return 1
	}
	return 0
}

func goleanTestAssignInterface() int {
	if testAssignInterface() {
		return 1
	}
	return 0
}

func goleanTestMultipleInterface() int {
	if testMultipleInterface() {
		return 1
	}
	return 0
}

func goleanTestBinaryExprInterface() int {
	if testBinaryExprInterface() {
		return 1
	}
	return 0
}

func goleanTestIfStmtInterface() int {
	if testIfStmtInterface() {
		return 1
	}
	return 0
}

func main() {}
