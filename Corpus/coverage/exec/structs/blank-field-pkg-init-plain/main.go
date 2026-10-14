package main

// The admitted package-level shape (BUG-129, [USER] Mike 2026-10-14): a plain
// variable read at a blank field gives the zero value with nothing evaluated,
// at package level as in a body; gc's initplan skips the field alike. PASS.

type blankPkgPlainS struct {
	_ int
	X int
	_ int
}

var blankPkgG = 9

var blankPkgV = blankPkgPlainS{blankPkgG, 2, blankPkgG}

func blankPkgInitPlain() int {
	u := blankPkgPlainS{4, 2, 4}
	if blankPkgV == u {
		return blankPkgV.X
	}
	return 0
}
