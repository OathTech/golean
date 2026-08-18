// spec#Identifiers block Identifiers-2-b38494c4
// The spec's four example identifiers — lowercase, underscore+digit,
// exported multi-word, and non-ASCII (Unicode letters) — declared and
// used so each FORM must lex as a single identifier token. Each carries
// a distinct decimal digit so a mis-lexed or dropped identifier changes
// the returned sum.
package main

var ThisVariableIsExported = 300

func specIdentifiers() int {
	a := 1
	_x9 := 20
	αβ := 4000
	return a + _x9 + ThisVariableIsExported + αβ
}

func main() {
	specIdentifiers()
}
