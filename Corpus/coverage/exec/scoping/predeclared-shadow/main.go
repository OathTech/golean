package main

// Shadowing the predeclared identifiers true/false/nil (BUG-069, the
// launch audit's D10-F1, widened by V1). The predeclared identifiers
// live in the UNIVERSE scope (spec#Predeclared_identifiers,
// spec#Declarations_and_scope) and are shadowable like any other
// identifier; a local named `true` is an ordinary variable. The
// frontend's emitIdent used to resolve these three NAMES to the
// universe constants before consulting go/types, so every read of a
// shadow was mis-lowered as the literal — silent wrong values, wrong
// branches, a fabricated panic, and a wrong len, depending only on how
// the literal type-checked downstream. No idiomatic program shadows
// these names, so the differential was structurally blind (BUG-002's
// epistemic class); these rows keep the mechanism pinned.
//
// The ctrl row is the genuine-use control: unshadowed true/false/nil
// must keep folding to the universe constants.

func shadowTrueBranch() int {
	true := false
	if true {
		return 1
	}
	return 2 // gc: 2 — the shadow is false; the old frontend returned 1
}

func shadowFalseBranch() int {
	false := (1 == 1)
	if false {
		return 1
	}
	return 2 // gc: 1 — the shadow is true; the old frontend returned 2
}

func pick(true bool) int {
	if true {
		return 1
	}
	return 2
}

func shadowParam() int {
	return pick(false) // gc: 2 — the old frontend passed literal true: 1
}

func shadowVarForm() int {
	var true bool // zero value: false
	if true {
		return 1
	}
	return 2 // gc: 2
}

func shadowNilLen() int {
	nil := []int{1, 2, 3}
	return len(nil) // gc: 3 — the old frontend read literal nil: 0
}

func shadowNilAppend() int {
	nil := []int{9}
	nil = append(nil, 8)
	return len(nil)*10 + nil[0] // gc: 29 — the old frontend fabricated
	// an index-out-of-range panic here
}

func shadowNilInt() int {
	nil := 5
	return nil + 1 // gc: 6 — the old frontend went stuck (honest red)
}

func ctrl() int {
	if true && !false {
		var p *int
		if p == nil {
			return 7
		}
	}
	return 0 // gc: 7 — genuine universe uses still fold
}

func main() {
	shadowTrueBranch()
	shadowFalseBranch()
	shadowParam()
	shadowVarForm()
	shadowNilLen()
	shadowNilAppend()
	shadowNilInt()
	ctrl()
}
