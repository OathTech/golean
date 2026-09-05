package main

// DESIGNED RED (stdlib slice 3): print/println of a kind the frontend
// refuses BY NAME — FR-29 (floats: internal/strconv.AppendFloat shortest-repr formatting, not transcribed this slice).
// The red IS the pin (BUGS.md BUG-093): a silent lowering here would be a
// wrong answer against gc's stderr.
func refused() int {
	var f float32 = 2.5
	print(f)
	return 0
}
