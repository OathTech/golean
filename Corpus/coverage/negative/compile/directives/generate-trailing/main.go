package main

// BUG-127 fix round: a directive that is not on a line by itself is
// «misplaced compiler directive» in gc whatever its verb — //go:generate
// included, though on its own line it is never misplaced.
func main() { println(1) } //go:generate echo hi
