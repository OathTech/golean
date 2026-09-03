package main

// BUG-087 audit fix F3 (2026-09-03): member 1's QUALIFIER is a
// differential observation, not a key convention. The receiver type
// `pkgs/valuer.T` is declared in a non-main package; gc's panicwrap text
// names it by import PATH (`pkgs/valuer.T.Val … nil *T pointer`), which
// is what the machine renders from the frontend's path-qualified TypeId
// key — so this text is outside BUG-059's name-vs-path class (where gc
// prints the package NAME). The dispatch goes through a //go:noinline
// callee so gc cannot devirtualize: member 1 at default flags.

import "pkgs/valuer"

type Valuer interface{ Val() int }

//go:noinline
func callValuer(v Valuer) int { return v.Val() }

func crossPkgValueMethodNilPtr() int {
	var p *valuer.T
	return callValuer(p)
}

func main() {}
