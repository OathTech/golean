// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/globals.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func foo() uint64 {
	return 10
}

var GlobalX uint64 = foo()
var globalY string

var globalA, globalB = "a", "b"

const MaxRune = '\U0010FFFF'
const runeWithType rune = 'a'
const IntWidth = 8

var _ = foo()

func other() {
	globalY = "ok"
}

func bar() {
	other()
	if GlobalX != 10 || globalY != "ok" {
		panic("bad")
	}
}

func init() {
	GlobalX = GlobalX
}

func init() {
	globalY = ""
}

func useUntypedRune() {
	if runeWithType > MaxRune {
		panic("invalid comparison")
	}
}

// --- GoLean harness ---
// Authored wrapper.

func goleanGlobals() int {
	bar()
	useUntypedRune()
	return int(GlobalX)*10 + len(globalA) + len(globalB)
}

func main() {}
