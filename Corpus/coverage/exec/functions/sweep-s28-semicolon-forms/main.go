// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Explicit semicolons: one-line
// statement lists, a trailing semicolon before a closing brace, the for / switch / if
// header forms with empty clauses, a one-line struct type and grouped var;
// expected = gc go1.26.5.

package main

func oneLiner() int { return 1; }

func semicolonForms() int {
	x := 1; y := 2; x += y
	{ x++; }
	for ;; { x++; break }
	for i := 0; i < 3; { i++; x++ }
	i := 0
	for ; i < 3; i++ { x++ }
	switch z := x; { case z > 0: x += 10 }
	switch ; x { case 0: x = -1 }
	if z := x; z > 0 { x += 100 }
	type pt struct{ a int; b string }
	p := pt{1, "ab"}
	var (q = 1; r = 2;)
	x += p.a + len(p.b) + q + r;
	return x*10 + oneLiner();
}

func doubleSemicolons() int {
	n := 1
	n++;;
	n++; ;
	return n // 3
}

func main() {
	println("semicolonForms", semicolonForms())
	println("doubleSemicolons", doubleSemicolons())
}
