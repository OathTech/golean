package main

import "unsafe"

// DESIGNED RED (stdlib slice 3; BUGS.md BUG-093; ledger §5.1 item 3): an
// unsafe.Pointer operand — gc prints its address. The refusal fires at the
// package-unsafe boundary before emitPrintStmt is reached; either way the
// row is red by name, completing the §5.1 item 3 kind list.
func refused() int {
	x := 1
	p := unsafe.Pointer(&x)
	println(p)
	return 0
}
