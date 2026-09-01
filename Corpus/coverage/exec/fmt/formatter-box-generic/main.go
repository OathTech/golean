package main

import "fmt"

// FORMATTER BOXING x GENERIC-BODY REFUSAL PIN (audit fix round
// 2026-09-01, BLOCKER-1(c); probe fm4): inside a generic body,
// `return t` boxes a TYPE-PARAMETER-typed value into `any` —
// types.Implements answers FALSE for a *types.TypeParam, so the
// per-type boxing key could not see that the instantiation
// wrap[both] boxes a Formatter implementor. Pre-fix this program
// EXPORTED and rendered "via-string" where gc calls Format
// ("via-format"): a silent wrong answer. The walk now treats a
// type-parameter boxing as a conservative HIT whenever any unit
// declares an implementor; this row is RED (frontend-export) BY
// DESIGN. gc @ go1.26.5: "via-format".

type both int

func (both) Format(s fmt.State, verb rune) { fmt.Fprint(s, "via-format") }
func (both) String() string                { return "via-string" }

func wrap[T any](t T) any { return t }

func genericBox() string {
	return fmt.Sprint(wrap(both(3))) // gc: "via-format"
}

func main() { genericBox() }
