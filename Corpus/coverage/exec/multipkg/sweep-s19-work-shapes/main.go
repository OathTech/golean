package main

// Sweep S19 (package initialization order), lane sweep/s19-init-order,
// 2026-10-27 (cells C14/C15): the BUG-061 classifier's WORK arms, each as
// the ONLY initializer of a package that gates one of two otherwise-tied
// importers. gc schedules a package whose initializer survives
// cmd/compile/internal/staticinit, so the gated importer waits and its
// rival records first: every chain is 21. A WORK verdict gc does not share
// would show as 12 here — the silent wrong-order direction the guard
// cannot see (the conversion arm's instance is multipkg/sweep-s19-
// staticinit-conv, BUG-341).

import (
	_ "am"
	_ "an"
	_ "fm"
	_ "fn"
	_ "im"
	_ "in"
	_ "mm"
	_ "mn"
	_ "pm"
	_ "pn"
	"rec"
	_ "vm"
	_ "vn"
	_ "wm"
	_ "wn"
)

func mapLiteral() int    { return rec.S["m"] }
func arithmetic() int    { return rec.S["a"] }
func multiStmtCall() int { return rec.S["f"] }
func indexing() int      { return rec.S["i"] }
func fieldRead() int     { return rec.S["p"] }
func ifaceCall() int     { return rec.S["v"] }
func funcValueCall() int { return rec.S["w"] }

func main() {
	println(mapLiteral(), arithmetic(), multiStmtCall(), indexing(), fieldRead(), ifaceCall(), funcValueCall())
}
