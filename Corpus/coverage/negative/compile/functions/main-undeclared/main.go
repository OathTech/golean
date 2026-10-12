package main

// A main package with no func main: gc rejects the PROGRAM ("function main
// is undeclared in the main package"). GoLean's native frontend lowers
// SUBJECT functions (the machine's entry is chosen by --function), so it
// accepts this directory and writes a wire — docs/BUGS.md BUG-125; this
// row is born FAIL at the negative lane's frontend-accepts stage.
func f() int { return 1 }
