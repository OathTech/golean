package main

import (
	"fmt"

	"fmtypes"
)

// FORMATTER BOXING x CROSS-PACKAGE REFUSAL PIN (audit fix round
// 2026-09-01, BLOCKER-1(b); probe fm8): the implementor is declared
// in the case-local package fmtypes, the boxing happens HERE — the
// pre-fix checkFormatterDynHole coupled its implementor scan and its
// boxing walk PER UNIT, so neither unit fired and the program
// EXPORTED, rendering "via-string" where gc calls Format
// ("via-format"): a silent wrong answer. The scans are now decoupled
// (implementor in ANY unit arms the walk over EVERY unit); this row
// is RED (frontend-export) BY DESIGN. gc @ go1.26.5: "via-format".

func crossUnitBox() string {
	var a any = fmtypes.Make()
	return fmt.Sprint(a) // gc: "via-format"
}

func main() { crossUnitBox() }
