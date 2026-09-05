package main

// DESIGNED RED (stdlib slice 3): print/println of a kind the frontend
// refuses BY NAME — FR-29 (the zero-operand spelling has no machine shape).
// The red IS the pin (BUGS.md BUG-093): a silent lowering here would be a
// wrong answer against gc's stderr.
func refused() int {
	println()
	return 0
}
