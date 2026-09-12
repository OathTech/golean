package main

// BUG-108 red-first row: the excluded sibling _extra.go imports a package
// this file does not (`os`) and uses it in an `init`. gc never reads
// _extra.go (leading underscore), so the program imports nothing and prints
// 1. A frontend that parses excluded files meets the unadmitted import and
// refuses the export — a red at frontend-export where gc has an answer.
var fromImport = 1

func excludedImport() int { return fromImport }

func main() { println(excludedImport()) }
