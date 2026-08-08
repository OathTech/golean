// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/shortcircuiting.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// helpers
type BoolTest struct {
	t  bool
	f  bool
	tc uint64
	fc uint64
}

func CheckTrue(b *BoolTest) bool {
	b.tc += 1
	return b.t
}

func CheckFalse(b *BoolTest) bool {
	b.fc += 1
	return b.f
}

// tests
func testShortcircuitAndTF() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckTrue(b) && CheckFalse(b) {
		return false
	}
	return b.tc == 1 && b.fc == 1
}

func testShortcircuitAndFT() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckFalse(b) && CheckTrue(b) {
		return false
	}
	return b.tc == 0 && b.fc == 1
}

func testShortcircuitOrTF() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckTrue(b) || CheckFalse(b) {
		return b.tc == 1 && b.fc == 0
	}
	return false
}

func testShortcircuitOrFT() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckFalse(b) || CheckTrue(b) {
		return b.tc == 1 && b.fc == 1
	}
	return false
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestShortcircuitAndTF() int {
	if testShortcircuitAndTF() {
		return 1
	}
	return 0
}

func goleanTestShortcircuitAndFT() int {
	if testShortcircuitAndFT() {
		return 1
	}
	return 0
}

func goleanTestShortcircuitOrTF() int {
	if testShortcircuitOrTF() {
		return 1
	}
	return 0
}

func goleanTestShortcircuitOrFT() int {
	if testShortcircuitOrFT() {
		return 1
	}
	return 0
}

func main() {}
