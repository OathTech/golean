package main

// Go type identity is by IMPORT PATH, not package NAME: `html/template`
// and `text/template` both declare a package named `template`, and
// `*html/template.Template` is a different type from
// `*text/template.Template` (Go's own runtime says so verbatim:
// "types from different packages"). The wire's `TypeId` keys are built
// from the package NAME, so both types lower to the single key
// `template.Template` and the assert answered `true` where Go answers
// `false` — a silent wrong answer reachable from a single `package main`
// with two stdlib imports (pre-merge audit 2026-07-31, findings 4/7).
//
// v1 fails CLOSED: the frontend refuses to export a program in which two
// distinct import paths would produce the same qualified prefix. Widening
// the keys to import paths is the real fix and is scoped in
// docs/2026-07-30_quorum-extern-policy.md.

import (
	ht "html/template"
	tt "text/template"
)

func importedPackageNameCollision() int {
	var p *ht.Template
	var a any = p
	_, ok := a.(*tt.Template)
	if ok {
		return 1
	}
	return 0
}
