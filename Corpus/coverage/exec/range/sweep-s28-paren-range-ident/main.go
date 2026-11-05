// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The assign-form range with a
// PARENTHESISED IDENTIFIER target `for (i) = range s`, `for (i), (v) = range s` — legal
// Go, gc runs it — BUG-421 (born red): emitRange's assign-form bind reads the target
// without ast.Unparen and refuses `(i)` as a non-identifier target with the reason that
// its operands would re-evaluate per iteration (an identifier has none), while
// `for i = range s` lowers; expected = gc go1.26.5.

package main

func rangeParenIdentTargets() int {
	s := []int{10, 20, 30}
	var i, v int
	sum := 0
	for (i) = range s {
		sum += i
	}
	for (i), (v) = range s {
		sum += i + v
	}
	for (i), v = range s {
		sum += v
	}
	return sum*10 + i // 1262
}

func rangeParenValueOnly() int {
	s := []int{10, 20, 30}
	var v int
	sum := 0
	for _, (v) = range s {
		sum += v
	}
	return sum // 60
}

func main() {
	println("rangeParenIdentTargets", rangeParenIdentTargets())
	println("rangeParenValueOnly", rangeParenValueOnly())
}
