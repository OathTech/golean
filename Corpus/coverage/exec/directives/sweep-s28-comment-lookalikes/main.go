// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Comment forms that LOOK like
// directives and are prose for gc: `// go:noinline` (a space) inside a body, a block
// comment `/*go:noinline*/` before a function; beside S20's rows (directives/*) — the
// `//go:` forms outside the allowlist are refused by name (coverage gaps, not rowed);
// expected = gc go1.26.5.

package main

func spaceNoinlineBody() int {
	n := 1
	// go:noinline
	n += 2
	return n // 3
}

/*go:noinline*/
func blockNoinline() int { return 3 }

func blockNoinlineSubject() int { return blockNoinline() + 1 } // 4

func main() {
	println("spaceNoinlineBody", spaceNoinlineBody())
	println("blockNoinlineSubject", blockNoinlineSubject())
}
