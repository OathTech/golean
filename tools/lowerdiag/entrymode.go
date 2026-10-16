package main

import "go/types"

// THE ENTRY RULE, statically (BUG-125; the frontend's twin is
// tools/nativefrontend/entrymode.go — [AGENT] lane
// frontend/main-undeclared-refuse-1013, 2026-10-13, under the [USER]'s
// ruling, Mike 2026-10-13, relayed: refuse the case rather than open the
// door to special-casing; support may come later; release-readiness row
// 41). Without --subject the
// frontend refuses a `package main` that declares no `func main` (gc's
// «function main is undeclared in the main package»), so the static judge
// records the same WHOLE-EXPORT refusal on a pseudo-declaration
// `package main`; with --subject (the differential corpus's mode) the rule
// is skipped, as in the frontend.
var subjectMode bool

func (a *analyzer) entryDeclared() {
	if subjectMode || a.lp.path != "main" || a.lp.pkg == nil || a.lp.pkg.Name() != "main" {
		return
	}
	if _, ok := a.lp.pkg.Scope().Lookup("main").(*types.Func); ok {
		return
	}
	pos := "-"
	if len(a.lp.files) > 0 {
		pos = a.p.pos(a.lp.files[0].Name)
	}
	d := &declReport{Pkg: a.lp.path, Kind: "package", Name: "main", Pos: pos}
	d.add(finding{Cause: mustCause("main-undeclared"), Key: "main-undeclared", Pos: pos, Certain: true, Export: true})
	a.lp.decls = append(a.lp.decls, d)
}
