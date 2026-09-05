package main

// G-OUT: a terminal observation carries the output PREFIX printed before
// it — gc's stderr carries the prints, then the `panic:` block; the
// harness splits at the unique line-start marker.
func printThenPanic() int {
	println("before the panic")
	print("no newline yet\n")
	panic("boom")
}
