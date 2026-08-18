// spec#Goto_statements block Goto_statements-4-42aaa746: 'A "goto"
// statement outside a block cannot jump to a label inside that block.'
// (spec verbatim, quote corrected at the P3 audit) — the spec's own
// erroneous example.
package main

func g(xs []int) {
	if len(xs) == 0 {
		goto L1
	}
	for i := range xs {
	L1:
		_ = i
	}
}

func main() { g(nil) }
