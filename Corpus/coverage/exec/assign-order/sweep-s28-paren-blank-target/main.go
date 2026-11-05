// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The PARENTHESISED BLANK target
// `(_) = v`, `(_), x = 1, 2`, `(_), (_) = two()` — legal Go, gc runs it — BUG-420 (born
// red): the emitter's blank tests read the target without ast.Unparen, so `(_)` falls to
// the address-taking lvalue path, whose identifier arm looks `_` up in go/types' Uses
// (no object) and the frontend CRASHES (a nil-pointer dereference in locals.go localID),
// an unnamed stop instead of a lowering; expected = gc go1.26.5.

package main

var n int

func bump() int { n++; return n }

func two() (int, int) { return 40, 2 }

func parenBlankSingle() int {
	n = 0
	(_) = bump()
	return n*10 + 1 // 11
}

func parenBlankMulti() int {
	n = 0
	x := 0
	(_), x = bump(), 2
	return n*10 + x // 12
}

func parenBlankMultiValue() int {
	n = 0
	(_), (_) = two()
	return n*10 + 3 // 3
}

func main() {
	println("parenBlankSingle", parenBlankSingle())
	println("parenBlankMulti", parenBlankMulti())
	println("parenBlankMultiValue", parenBlankMultiValue())
}
