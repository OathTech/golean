package main

// BUG-108 red-first row: the excluded sibling extra_windows.go REDECLARES
// `conflict` and `helper`. gc never reads the file (excluded by the _windows
// suffix on linux/amd64), so the package is legal and prints 1. A frontend
// that parses excluded files type-checks a redeclaration and refuses the
// export — a red at frontend-export where gc has an answer.
var conflict = 1

func helper() int { return conflict }

func excludedConflict() int { return helper() }

func main() { println(excludedConflict()) }
