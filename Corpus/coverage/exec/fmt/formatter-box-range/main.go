package main

import "fmt"

// FORMATTER BOXING x RANGE-ASSIGN REFUSAL PIN (audit fix round
// 2026-09-01, BLOCKER-1(a); probe fm1): the `=`-form range clause
// assigns each element into a PRE-DECLARED interface-typed variable —
// a boxing context the checkFormatterDynHole walk's enumerated list
// (fmtdesugar.go) was missing, so this program EXPORTED and rendered
// "via-string" where gc's handleMethods consults Format first
// ("via-format"): a silent wrong answer. The walk now covers `=`-form
// range key/value targets; this row is RED (frontend-export) BY
// DESIGN — the refusal firing IS the pin. gc @ go1.26.5: "via-format".

type both int

func (both) Format(s fmt.State, verb rune) { fmt.Fprint(s, "via-format") }
func (both) String() string                { return "via-string" }

func rangeBox() string {
	var a any
	xs := []both{both(3)}
	for _, a = range xs {
	}
	return fmt.Sprint(a) // gc: "via-format" — Format wins at dyn sites
}

func main() { rangeBox() }
