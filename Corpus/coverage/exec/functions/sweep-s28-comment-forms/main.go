// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Comments in every prose
// position: between a signature and its body, inside a signature, a receiver, a call's
// arguments, an if header, before an else, in an empty block, inside a literal, trailing;
// nested slashes, adjacent block comments, comment delimiters inside comments and inside
// string literals, a comment at the end of the file without a newline; expected = gc.

package main

type pt struct{ v int }

func (t /* receiver */ pt) get() int /* result */ { return t.v }

func /* name follows */ add(a /* first */ int, b int /* second */) (int /* one */) {
	return a + b
}

func commentForms() int /* c */ {
	n := add( /* c */ 1 /* c */, 2 /* c */)
	if n > 0 /* c */ {
		n += 10
	} /* c */ else {
		n -= 1
	}
	{ /* empty */ }
	s := []int{1, /* c */ 2 /* c */}
	n += len(s) // trailing // nested // slashes
	/* a */ /* b */ n += 100
	// a line comment holding */ inside
	/* a block comment holding // inside */
	n += len("// not a comment") + len(`/* raw */`)
	n += pt{3}.get() * 1000 /* c */ + 0
	x := 1 /* same-line block comment */ + 2
	n += x * 10000
	return n
}

func main() {
	println("commentForms", commentForms())
}
// a comment at the end of the file, no trailing newline