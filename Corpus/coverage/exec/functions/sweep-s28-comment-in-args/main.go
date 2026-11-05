// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). A newline-bearing block comment
// inside an argument list (after a comma no semicolon is inserted, so the comment is
// prose) and leading / trailing block comments around arguments; expected = gc go1.26.5.

package main

func add(a, b int) int { return a + b }

func commentNewlineInArgs() int {
	n := add(1, /*
	*/ 2)
	m := add(
		/* leading */ 3,
		4 /* trailing */)
	return n*10 + m // 37
}

func main() { println("commentNewlineInArgs", commentNewlineInArgs()) }
