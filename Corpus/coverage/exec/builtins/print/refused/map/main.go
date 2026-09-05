package main

// DESIGNED RED (stdlib slice 3): print/println of a kind the frontend
// refuses BY NAME — ledger §5.1 item 3 (gc prints an ADDRESS the machine does not have; permanent).
// The red IS the pin (BUGS.md BUG-093): a silent lowering here would be a
// wrong answer against gc's stderr.
func refused() int {
	m := map[int]int{}
	println(m)
	return 0
}
