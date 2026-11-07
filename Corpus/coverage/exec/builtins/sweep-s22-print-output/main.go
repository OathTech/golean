package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md, BUG-093 above all; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group B1/B3: the program's fd-2 bytes are the `output` field, byte for byte, at the admitted operand kinds.

type S string

const named = 5
const label = "k"

func noTrailingNewline() int { print("x"); return 1 }
func emptyPrint() int        { print(""); print("", ""); return 1 }
func nulByte() int           { print("a\x00b\n"); return 1 }
func crAndTab() int          { print("a\r\tb\n"); return 1 }
func fourKiB() int {
	for i := 0; i < 256; i++ {
		print("0123456789abcdef")
	}
	return 1
}
func trailerTextMidOutput() int { println("exit status 0"); println("more"); return 1 }
func untypedConstants() int     { println(1, "s", true, 'c', 1<<40, -7); return 1 }
func namedConstants() int       { println(named, label, named+1); return 1 }
func byteAndRune() int          { println(byte(1), 'a', rune('b'), byte('c')); return 1 }
func definedStringKind() int    { println(S("x"), S("")); print(S("y\n")); return 1 }
func concatenation() int        { s := "c"; println("a"+"b", "d"+s); return 1 }
func deferredPrintNormalReturn() int {
	defer func() { println("deferred") }()
	println("body")
	return 1
}
func manyOperands() int      { println(1, 2, 3, 4, 5, 6, 7, 8, true, false, "end"); return 1 }
func two() (int, string)     { return 1, "two" }
func multiValueOperand() int { println(two()); print(two()); print("\n"); return 1 }
func uintptrOperand() int    { var u uintptr = 5; println(u, uintptr(7), -u); return 1 }

func main() {
	noTrailingNewline()
	emptyPrint()
	nulByte()
	crAndTab()
	fourKiB()
	trailerTextMidOutput()
	untypedConstants()
	namedConstants()
	byteAndRune()
	definedStringKind()
	concatenation()
	deferredPrintNormalReturn()
	manyOperands()
	multiValueOperand()
	uintptrOperand()
}
