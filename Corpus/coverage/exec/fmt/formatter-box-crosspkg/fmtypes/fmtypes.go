// Package fmtypes declares the Formatter implementor AWAY from the
// boxing site — the cross-package leg of the formatter-box pins (see
// ../main.go).
package fmtypes

import "fmt"

type Both int

func (Both) Format(s fmt.State, verb rune) { fmt.Fprint(s, "via-format") }
func (Both) String() string                { return "via-string" }

func Make() Both { return Both(3) }
