package main

// Go type identity is by IMPORT PATH, not package NAME: `html/template`
// and `text/template` both declare a package named `template`, and
// `*html/template.Template` is a different type from
// `*text/template.Template` (Go's own runtime says so verbatim:
// "types from different packages"). BUG-010's original wire built
// `TypeId` keys from the package NAME, so both types lowered to the
// single key `template.Template` and the assert answered `true` where
// Go answers `false` — a silent wrong answer reachable from a single
// `package main` with two stdlib imports (pre-merge audit 2026-07-31,
// findings 4/7). The v1 fail-closure refused such exports outright.
//
// FIXED 2026-08-18 (multi-package identity, raft W1.1,
// docs/2026-08-18_multipackage-identity.md §1): TypeId keys qualify by
// the IMPORT PATH — `html/template.Template` vs `text/template.Template`
// are distinct keys — so this case now passes with the correct `false`.
// The panic-form MESSAGE-rendering residue for multi-segment paths is
// pinned separately (multipkg/same-name-identity-panic, BUG-059).

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
